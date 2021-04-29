type var = { name : int }

type exp_subst = 
 { mutable content : bite
 ; mutable copying : bool
 ; mutable prev : exp_subst option
 ; mutable rc : int
 ; mutable occurs : bite option }
and environment = exp_subst
and revenvironment = exp_subst
and body_or_container =
 | Body of environment
 | Container of zipper option
and bite =
 | Var of var
 | Lam of {v: var ; mutable b: body_or_container}
 | App of bite * bite
 | Shared of {mutable c: exp_subst}
and zipper = environment option * revenvironment option

type dir = LR | RL

(**************** utilities ******************)

let _print_endline = ref print_endline
let _prerr_endline = ref prerr_endline

let print_endline s = !_print_endline s
let prerr_endline s = !_prerr_endline s

let insert_after v v1 =
 v.prev <- Some v1

let mk_exp_subst content = { content ; copying = false ; prev = None ; rc = 0 ; occurs = None }
let mk_var name = { name }


(**************** pretty printing ******************)

let string_of_it s =
 let c = ref 0 in
 let m = ref [] in
 function v ->
  try List.assq v !m
  with Not_found ->
   let n = s ^ string_of_int !c in
   incr c ;
   m := (v,n)::!m ;
   n

let string_of_var {name} = "x" ^ string_of_int name
let string_of_exp_subst = string_of_it "y"

let rec string_of_t =
 function
    App(t1,t2) -> "(" ^ string_of_t t1 ^ " " ^ string_of_t t2 ^ ")"
  | Lam{v;b=Body e} -> "(" ^ string_of_var v ^ "." ^ pretty_print_list (Some e) ^ ")"
  | Lam{v;b=Container _} -> "(" ^ string_of_var v ^ "." ^ "[]" ^ ")"
  | Var v -> string_of_var v
  | Shared {c} -> string_of_exp_subst c

and pretty_print_subst v =
 "[" ^ string_of_t v.content ^ " / " ^ string_of_exp_subst v ^ "^" ^ string_of_int v.rc ^ "]"

and pretty_print_list =
 function
   None -> ""
 | Some v ->
    pretty_print_list v.prev ^
    pretty_print_subst v

and pretty_print_list_rev =
 function
   None -> ""
 | Some v ->
    pretty_print_subst v ^
    pretty_print_list_rev v.prev

and pretty_print_dir =
 function
    LR -> " >> "
  | RL -> " << "

and pretty_print_up plugged =
 function
    None -> plugged
  | Some (n,Some ({content=Lam{v;b=Container k};_} as z)) ->
     pretty_print_up 
      (pretty_print_list n ^
      "[" ^ "(" ^ string_of_var v ^ "." ^ plugged ^ ")" ^ " / " ^ string_of_exp_subst z ^ "]" ^
       pretty_print_list_rev z.prev)
     k
  | _ -> assert false
     

and pretty_print dir (n,z) k =
 pretty_print_up
  (pretty_print_list n ^
   pretty_print_dir dir ^
   pretty_print_list_rev z)
 k

(**************** reduction ******************)

let copying_exp_subst y y' f =
  let saved = y.content in
  let t = Shared {c=y'} in
  y'.occurs <- Some t ;
  y.content <- t ;
  y.copying <- true ;
  let res = f () in
  y.content <- saved ;
  y.copying <- false ;
  res

(*
           z  w     e  y   y y   
lambda y.  ---- ;  -----; ----   
             b        z     e    

            z'  w    e'  y   y y
            ----- ;  -----; -----
              b'       z'     e'
   b',e' = copy ?b' e in*)

let copy_env v n b' = 
 let rec copy = function
  | Var v' when v == v' -> n.rc <- n.rc + 1 ; Shared {c=n}
  | Shared {c={content; copying;_}} when copying -> content
  | Var _ as t -> t
  | Shared {c=v} as t -> v.rc <- v.rc + 1 ; t
  | App(t1,t2) -> App(copy t1,copy t2) 
  | Lam{v;b = Body e} -> Lam{v;b=Body (copy_env e)}
  | Lam{b=Container _;_} -> assert false
and copy_env ?b' =
 let rec aux e =
  let t' = copy e.content in 
  match e.prev with
   | None ->
     (match b' with
      | None -> mk_exp_subst t'
      | Some b' -> b'.content <- t' ; b')
   | Some p ->
      let n' = mk_exp_subst t' in
      let e' = copying_exp_subst e n' (fun () -> aux p) in
      insert_after n' e' ;
      n'
  in aux
in copy_env ~b'

let rec gc {prev=p;content=c;_} =
 Option.iter gc p;
 gc_bite c
and gc_bite =
 function
    Var _ -> ()
  | Shared {c=v} -> v.rc <- v.rc - 1
  | App(t1,t2) -> gc_bite t1; gc_bite t2
  | Lam{b=Body e;_} -> gc e
  | Lam{b=Container _;_} -> assert false

let last_rule_used = ref None

let rec eval_RL ((n,z) as zip : zipper) (k : zipper option) =
 Option.iter (fun rule -> print_endline ("\n --> " ^ rule ^ "\n")) !last_rule_used ;
 print_endline (pretty_print RL zip k) ;
 match n with
   None ->
    (* sea2 *)
    last_rule_used := Some "sea2" ;
    eval_LR (None,z) k
 | Some n ->
   match n.content with
    | (App(_ ,App _) | App(App _,_)
      |App(_, Lam _) | App(Lam _,_)
      |App(Shared {c={content=Lam{b=Container _;_};_}},_)) -> assert false
    | App(Shared {c={content=Lam{v=y;b=Body e;_};_} as r}, (Shared {c={content=Lam _;_} as y'})) ->
       (* bv *)
       last_rule_used := Some "bv" ;
       r.rc <- r.rc - 1 ;
       y'.rc <- y'.rc - 1 ;
       let e' = copy_env y y' n e in
       eval_RL (Some e',z) k
    | App(Shared {c={content=Lam{v=y;b=Body e};_} as r}, t) ->
       (* bi *)
       last_rule_used := Some "bi" ;
       r.rc <- r.rc - 1 ;
       let y' = mk_exp_subst t in
       let e' = copy_env y y' n e in
       y'.prev <- z;
       eval_RL (Some e',Some y') k
    | Shared {c={content=(Shared _ | Var _);_} as c} when n.prev <> None ->
        (* ren *)
        last_rule_used := Some "ren" ;
        (match n.occurs with
            Some (Shared r as o) ->
             c.occurs <- Some o;
             r.c <- c ;
             eval_RL (n.prev,z) k
          | _ -> assert false) ;
    | (Lam _ | Var _ | App(Var _, _)
       |Shared _ | App(Shared _, _)) ->
         (* sea1 *)
         last_rule_used := Some "sea1" ;
         let p = n.prev in
         n.prev <- z;
         eval_RL (p,Some n) k
and eval_LR ((n,z) as zip : zipper) (k : zipper option) =
   Option.iter (fun rule -> print_endline ("\n --> " ^ rule ^ "\n")) !last_rule_used ;
   print_endline (pretty_print LR zip k) ;
   match z,k with
      None,None ->
       (* normal form reached! *)
       print_endline "\n NORMAL FORM REACHED" ;
       n
   | None,Some (n',Some ({prev=z'';content=Lam({b=Container k';_} as r);_} as z')) ->
      (* sea4 *)
      last_rule_used := Some "sea4" ;
      r.b <- Body (match n with None -> assert false | Some n -> n);
      z'.prev <- n';
      eval_LR (Some z',z'') k'
   | None,Some _ -> assert false
   | Some ({prev=p;rc;_} as zz),_ ->
      match zz.content with
       | Lam {b=Body e;_} when rc = 0 && n <> None ->
           (* gc *)
           last_rule_used := Some "gc" ;
           gc e;
           eval_LR (n,p) k
       | Lam ({b=Body e;_} as r) ->
           (* sea5 *)
           last_rule_used := Some "sea5" ;
           r.b <- Container k;
           eval_RL (Some e,None) (Some (n,z))
       | Lam {b=Container _;_} ->
           assert false
       | (Var _ | Shared _ | App _) ->
           (* sea3 *)
           last_rule_used := Some "sea3" ;
           zz.prev <- n;
           eval_LR (Some zz,p) k

(********* translation ************************************)

let translate =
 let dummy = Var (mk_var 0) in
 let rec aux_bite this = function
 | Var _ as t -> t, this
 | App(t1, t2) ->
    let t1, this = maybe_aux this t1 in 
    let t2, this = maybe_aux this t2 in 
    App(t1, t2), this
 | Lam{v;b=Body e} -> let e = aux_env e in Lam{v;b=Body e}, this
 | Lam{b=Container _;_}
 | Shared _ -> assert false
 and maybe_aux this = function
 | App _ | Lam _ as t ->
    let n = mk_exp_subst dummy in
    n.rc <- 1;
    insert_after n this;
    let t, this = aux_bite n t in
    n.content <- t;
    let t = Shared {c=n} in
    n.occurs <- Some t;
    t, this
 | Var _ as t -> t,this
 | Shared _ -> assert false
 and aux_env e =
   let n = mk_exp_subst dummy in
   let t', last = aux_bite n e.content in
   n.content <- t' ;
   assert (e.prev = None);
   last
 in aux_env

let eval_bite t =
 let star = mk_exp_subst t in
 ignore (eval_RL (Some (translate star),None) None) ;
 last_rule_used := None

(**************** smart constructors ******************)

let lastvar = ref 0

let v () = incr lastvar ; Var (mk_var !lastvar)

let a t1 t2 = App(t1,t2)

let al =
 function
    [] -> None
  | hd::tl -> Some (List.fold_left a hd tl)

let l f =
 incr lastvar ;
 let v = mk_var !lastvar in
 let star = mk_exp_subst (f (Var v)) in
 Lam {v;b=Body star}

(**************** tests ******************)

let i () = (l (fun x -> x))

let _ = 
 print_endline "\n>>>>>>>>>>>>>> test weak, open normalization";
 (* I (I (x y)) *)
 eval_bite (a (i ()) (a (i ()) (a (v ()) (v ()))))

let _ = 
 print_endline "\n>>>>>>>>>>>>>> test strong normalization";
 (* x (y. I I) *)
 eval_bite (a (v ()) (l (fun _ -> a (i ()) (i ()))))

(**************** parser combinators ******************)

type 'm pstring = int * string * 'm
type ('a,'m) parse = 'm pstring -> ('a * 'm pstring) option

let return : 'a -> ('a,'m) parse = fun x s -> Some (x,s)
let (>>=) : ('a,'m) parse -> ('a -> ('b,'m) parse) -> ('b,'m) parse = fun x f s ->
 Option.bind (x s) (fun (r,s) -> f r s)
let return_with_map : ('m -> 'a * 'm) -> ('a,'m) parse = fun f (n,s,m) ->
 let r,m = f m in Some (r,(n,s,m))
let mfail : ('a,'m) parse = fun _ -> None

let is_letter = function 'a'..'z' | 'A'..'Z' -> true | _ -> false
let is_blank = function ' ' | '\n' | '\t' -> true | _ -> false

let rec ch : char -> (unit,'m) parse = fun x (n,s,m) ->
 if n >= String.length s then None
 else if is_blank s.[n] then ch x (n+1,s,m)
 else if s.[n] = x then Some ((),(n+1,s,m)) else None

let rec letter : (char,'m) parse = fun (n,s,m) ->
 if n >= String.length s then None
 else if is_blank s.[n] then letter (n+1,s,m)
 else if not (is_letter s.[n]) then None
 else Some (s.[n],(n+1,s,m))

let thens : ('a,'m) parse -> ('b,'m) parse -> ('a -> 'b -> 'c) -> ('c,'m) parse = fun p1 p2 f ->
 p1 >>= (fun r1 -> p2 >>= (fun r2 -> return (f r1 r2)))

let rec repeat' : ('a,'m) parse -> ('a list,'m) parse = fun p s ->
 match p s with
    None -> Some ([],s)
  | Some (r,s) ->
     let l,s = Option.get (repeat' p s) in
     Some (r::l,s)

let repeat : ('a,'m) parse -> ('a list -> 'b option) -> ('b,'m) parse = fun p f ->
 repeat' p >>= fun l -> match f l with None -> mfail | Some r -> return r

(*
let mapp : 'a parse list -> 'a list parse = fun pl ->
 List.fold_right (fun p res -> p >>= (fun r -> res >>= (fun l -> return (r::l)))) pl (return [])

let thenl : 'a parse list -> ('a list -> 'b) -> 'b parse = fun pl f ->
 mapp pl >>= (fun l -> return (f l))
*)

let orelse : ('a,'m) parse -> ('a,'m) parse -> ('a,'m) parse = fun p1 p2 s ->
 match p1 s with
    None -> p2 s
  | Some _ as res -> res

type symbol_table = (char * bite) list

let assoc w t =
 try
  List.assoc w t, t
 with
  Not_found ->
   let x = v () in
    x,(w,x)::t

let first a _ = a
let second _ a = a

let rec bitep : (bite,symbol_table) parse = fun s ->
 repeat abitep al s
and abitep : (bite,symbol_table) parse = fun s ->
 orelse (orelse lamp varp) (thens (ch '(') (thens bitep (ch ')') first) second) s
and appp : (bite,symbol_table) parse = fun s ->
 thens bitep bitep (fun l r -> a l r) s
and lamp : (bite,symbol_table) parse = fun s ->
 (letter >>= (fun c -> ch '.' >>= (fun _ ->
   incr lastvar ;
   let v = mk_var !lastvar in
   return_with_map (fun t -> (),(c,Var v)::t) >>=
   fun _ -> bitep >>= fun b -> return (Lam{v;b=Body (mk_exp_subst b)})))) s
and varp : (bite,symbol_table) parse = fun s ->
 (letter >>= (fun c -> return_with_map (assoc c))) s

let rec all_blanks n s =
 n >= String.length s || (is_blank s.[n] && all_blanks (n+1) s)

let parse s f =
 lastvar := 0;
 match
  (match bitep (0,s,[]) with
   | Some (t,(n,s,_)) when all_blanks n s -> Some t
   | _ -> None)
 with
   None -> prerr_endline ("Parsing error on \"" ^ s ^ "\"")
 | Some t -> f t
  

(**************** more tests ******************)

let print_and_eval t =
 print_endline ("Parsed bite " ^ string_of_t t);
 eval_bite t

let _ = 
 print_endline "\n>>>>>>>>>>>>>> test parser 1";
 (* x (y. I I) *)
 parse "x (y. (z.y))" print_and_eval
