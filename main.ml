open Js_of_ocaml

let document = Dom_html.window##.document

let eval () =
 let x = (Js.coerce_opt (document##getElementById (Js.string "in")) Dom_html.CoerceTo.textarea (fun _ -> assert false))##.value in
 let input = Js.to_string x in
 let o = ref "" in
 Strong_cbv._print_endline := (fun s -> o := !o ^ s ^ "<hr>");
 Strong_cbv._prerr_endline := (fun s -> o := !o ^ s ^ "<hr>");
 Strong_cbv.parse input (fun t -> Strong_cbv.eval_bite t);
 let main = Js.Opt.get (document##getElementById (Js.string "main")) (fun () -> assert false) in
 main##.innerHTML := Js.string !o

let _ = Js.export "eval" (Js.wrap_callback eval)

(*
let onload _ =
 let res = document##createDocumentFragment in
(*
 let s = ref "" in
 Strong_cbv.parse "x (y. (z.z) (z.z))" (fun t -> s := Strong_cbv.string_of_t t);
 Dom.appendChild res (document##createTextNode (Js.string !s));
 let main = Js.Opt.get (document##getElementById (Js.string "main")) (fun () -> assert false) in
 Dom.appendChild main res;
*) ignore res;
 Js._false

let _ = Dom_html.window##.onload := Dom_html.handler onload
*)
