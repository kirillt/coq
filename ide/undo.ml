open GText
open Ideutils
type action = 
  | Insert of string * int * int (* content*pos*length *) 
  | Delete of string * int * int (* content*pos*length *) 

let neg act = match act with
  | Insert (s,i,l) -> Delete (s,i,l)
  | Delete (s,i,l) -> Insert (s,i,l)

class undoable_view (tv:Gtk.textview Gtk.obj) =
  let undo_lock = ref true in 
object(self)
  inherit GText.view tv as super
  val history = (Stack.create () : action Stack.t)
  val redo = (Queue.create () : action Queue.t)
  val nredo = (Stack.create () : action Stack.t)

  method private dump_debug =
    if !debug then begin
      prerr_endline "==========Stack top=============";
      Stack.iter 
	(fun e -> match e with
	   | Insert(s,p,l) ->
 	       Printf.eprintf "Insert of '%s' at %d (length %d)\n" s p l
	   | Delete(s,p,l) -> 			   
	       Printf.eprintf "Delete '%s' from %d (length %d)\n" s p l)
	history;
      Printf.eprintf "Stack size %d\n" (Stack.length history);
      prerr_endline "==========Stack Bottom==========";
      prerr_endline "==========Queue start=============";
      Queue.iter 
	(fun e -> match e with
	   | Insert(s,p,l) ->
 	       Printf.eprintf "Insert of '%s' at %d (length %d)\n" s p l
	   | Delete(s,p,l) -> 			   
	       Printf.eprintf "Delete '%s' from %d (length %d)\n" s p l)
	redo;
      Printf.eprintf "Stack size %d\n" (Queue.length redo);
      prerr_endline "==========Queue End==========" 

    end

  method clear_undo = Stack.clear history; Stack.clear nredo; Queue.clear redo

  method undo = if !undo_lock then begin
    undo_lock := false;
    prerr_endline "UNDO";
    try begin
      let r = 
	match Stack.pop history with
	  | Insert(s,p,l) as act -> let start = self#buffer#get_iter_at_char p in
	    (self#buffer#delete_interactive 
	       ~start
	       ~stop:(start#forward_chars l)
	       ()) or
	    (Stack.push act history; false)
	  | Delete(s,p,l) as act -> 
	      let iter = self#buffer#get_iter_at_char p in
	      (self#buffer#insert_interactive ~iter s) or
	      (Stack.push act history; false)
      in if r then begin
	process_pending ();
	let act = Stack.pop history in
	Queue.push act redo;
	Stack.push act nredo
      end;
      undo_lock := true; 
      r
    end
    with Stack.Empty -> 
      undo_lock := true; 
      false
  end else
    (prerr_endline "UNDO DISCARDED"; true)

  method redo = prerr_endline "REDO"; true
  initializer
    ignore (self#buffer#connect#insert_text 
	      ~callback:
	      (fun it s ->
		 if !undo_lock && not (Queue.is_empty redo) then begin
		   Stack.iter (fun e -> Stack.push (neg e) history) nredo;
		   Stack.clear nredo;
		   Queue.iter (fun e -> Stack.push e history) redo;
		   Queue.clear redo;
		 end;
		   let pos = it#offset in
		 if Stack.is_empty history or 
		   s=" " or s="\t" or s="\n" or
					(match Stack.top history with 
					   | Insert(old,opos,olen) -> 
					       opos + olen <> pos
					   | _ -> true)
		 then Stack.push (Insert(s,it#offset,Glib.Utf8.length s)) history
		 else begin
		   match Stack.pop history with
		     | Insert(olds,offset,len) -> 
			 Stack.push 
			 (Insert(olds^s,
				 offset,
				 len+(Glib.Utf8.length s)))
			 history
		     | _ -> assert false
		 end;
		 self#dump_debug
	      ));
    ignore (self#buffer#connect#delete_range
	      ~callback:
	      (fun ~start ~stop -> 
		 if !undo_lock && not (Queue.is_empty redo) then begin
		   Queue.iter (fun e -> Stack.push e history) redo;
		   Queue.clear redo;
		 end;
		 Stack.push 
		   (Delete(self#buffer#get_text ~start ~stop (),
			   start#offset,
			   stop#offset - start#offset
			  ))
		   history;
		 self#dump_debug
	      ))
end

let undoable_view ?(buffer:buffer option) 
?editable ?cursor_visible ?wrap_mode
    ?packing ?show () = 
    let w = match buffer with 
      | None -> GtkText.View.create ()
      | Some b -> GtkText.View.create_with_buffer b#as_buffer
    in
    GtkText.View.set w ?editable ?cursor_visible ?wrap_mode;
    GObj.pack_return (new undoable_view w) ~packing ~show

