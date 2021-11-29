(* λProlog interpreter! *)

(* Compile with:
 * $ ocamlfind ocamlc -package angstrom -package stdio -linkpkg -g -o lp lp.ml
 *)

type idx = int
type lvl = int

module CPS = struct
  type failure_cont = unit -> unit
  type success_cont = failure_cont -> unit

  type computation = failure_cont -> success_cont -> unit

  let id: computation = fun fk sk -> sk fk
  let compose f g fk sk = f fk (fun fk' -> g fk' sk)
end


module Names : sig
  val string_to_lvl : string -> lvl
  val lvl_to_string : lvl -> string

  val cut     : lvl (* !     *)
  val implies : lvl (* =>    *)
  val neck    : lvl (* :-    *)
  val pi      : lvl (* pi    *)
  val sigma   : lvl (* sigma *)
  val comma   : lvl (* ,     *)
  val semi    : lvl (* ;     *)
  val eq      : lvl (* =     *)

  val reserved_names : lvl list
end = struct
  (* String interning utils *)
  (* All global symbols get negative number lvl ids (trick from ELPI) *)

  type state =
    { hashmap: (string, int) Hashtbl.t
    ; mutable arr: string array
    ; mutable counter: int }
  let state: state =
    { hashmap = Hashtbl.create 20
    ; arr = Array.make 20 ""
    ; counter = 0 }

  let string_to_lvl s = match Hashtbl.find_opt state.hashmap s with
    | Some i -> - i - 1
    | None ->
        let i = state.counter in
        state.counter <- i + 1;
        (* grow if necessary *)
        if i = Array.length state.arr then begin
          let new_arr = Array.make (2 * i) "" in
          Array.blit state.arr 0 new_arr 0 i;
          state.arr <- new_arr
        end;
        state.arr.(i) <- s;
        Hashtbl.add state.hashmap s i;
        - i - 1

  let lvl_to_string lvl = state.arr.(- lvl - 1)

  let cut     = string_to_lvl "!"
  let implies = string_to_lvl "=>"
  let neck    = string_to_lvl ":-"
  let pi      = string_to_lvl "pi"
  let sigma   = string_to_lvl "sigma"
  let comma   = string_to_lvl ","
  let semi    = string_to_lvl ";"
  let eq      = string_to_lvl "="

  let reserved_names = [cut; implies; neck; pi; sigma; comma; semi; eq]
end

module Data = struct
  (* Data layout: uses CBV normalization by evaluation
    This is closer to Teyjus's data layout than ELPI's. It's simpler to think
    about than ELPI's, but I expect it's slower since unification quotes and
    unquotes all the time. If I rewrite I will try to go full de Bruijn levels
  *)
  type tm =
    | Local of idx
    | Global of lvl
    | App of tm * tm
    | Abs of tm
    | Hole of hole ref
  and vtm =
    | VRigid of lvl * vtm list
    | VFlex of hole ref * vtm list
    | VLam of (vtm -> vtm)
  and hole =
    | Empty of { scope: lvl; susp: CPS.computation list }
    | Filled of vtm

  let fresh_hole lvl = ref (Empty { scope = lvl; susp = [] })

  type trail =
    { mutable holes: hole ref Weak.t
    ; mutable scopes: int array
    ; mutable susps: CPS.computation list array
    ; mutable size: int }
  let trail: trail =
    { holes = Weak.create 256
    ; scopes = Array.make 256 0
    ; susps = Array.make 256 []
    ; size = 0 }

  let fill hole tm =
    (* grow if necessary *)
    if trail.size = Weak.length trail.holes then begin
      let new_size = 2 * trail.size in
      let new_holes = Weak.create new_size in
      Weak.blit trail.holes 0 new_holes 0 trail.size;
      trail.holes <- new_holes;
      let new_scopes = Array.make new_size 0 in
      Array.blit trail.scopes 0 new_scopes 0 trail.size;
      trail.scopes <- new_scopes;
      let new_susps = Array.make new_size [] in
      Array.blit trail.susps 0 new_susps 0 trail.size;
      trail.susps <- new_susps
    end;
    let Empty { scope; susp } = !hole in
    Weak.set trail.holes trail.size (Some hole);
    Array.set trail.scopes trail.size scope;
    Array.set trail.susps trail.size susp;
    trail.size <- trail.size + 1;
    hole := Filled tm

  let backtrack_to trailmarker =
    assert (0 <= trailmarker && trailmarker <= trail.size);
    for i = trailmarker to trail.size - 1 do
      begin match Weak.get trail.holes i with
        | Some h ->
            h := Empty { scope = trail.scopes.(i); susp = trail.susps.(i) }
        | None -> ()
      end;
      trail.susps.(i) <- []
    done;
    trail.size <- trailmarker

  let rec eval (env: vtm list) = function
    | Local i -> List.nth env i
    | Global lvl -> VRigid(lvl, [])
    | App(f, x) ->
        begin match eval env f, eval env x with
          | VFlex (h, args), x' -> VFlex (h, x'::args)
          | VRigid(x, args), x' -> VRigid(x, x'::args)
          | VLam f', x' -> f' x'
        end
    | Abs tm -> VLam (fun x -> eval (x::env) tm)
    | Hole h -> VFlex(h, [])

  let app f x = match f with
    | VFlex (h, args) -> VFlex (h, x::args)
    | VRigid(h, args) -> VRigid(h, x::args)
    | VLam f'         -> f' x
  let rec app_spine f args = match f, args with
    | _               , []    -> f
    | VFlex (h, args'), _     -> VFlex (h, args @ args')
    | VRigid(h, args'), _     -> VRigid(h, args @ args')
    | VLam f'         , x::xs -> app_spine (f' x) xs

  let rec deref = function
    | VFlex({ contents = Filled tm }, args) ->
        app_spine (deref tm) args
    | x -> x

  let quote base_lvl lvl vtm =
    let rec go lvl x = match deref x with
      | VFlex (h, args) ->
          List.fold_right (fun arg f -> App(f, go lvl arg)) args (Hole h)
      | VRigid(v, args) ->
          let head = if v < base_lvl then Global v else Local (lvl - v - 1) in
          List.fold_right (fun arg f -> App(f, go lvl arg)) args head
      | VLam f          -> Abs (go (lvl+1) (f (VRigid(lvl, [])))) in
    go lvl vtm

  let to_string lvl (vtm: vtm) =
    let buf = Buffer.create 16 in
    let add = Buffer.add_string buf in
    let subscripts = [|"₀";"₁";"₂";"₃";"₄";"₅";"₆";"₇";"₈";"₉"|] in
    let show_local n =
      add "x";
      let add_digit c =
        add subscripts.(Char.(code c - code '0')) in
      String.iter add_digit (string_of_int n) in
    let open_paren b = if b then add "(" in
    let close_paren b = if b then add ")" in
    let rec go lvl atom x = match deref x with
      | VRigid(f, args) ->
          open_paren (atom && args <> []);
          if f >= 0 then show_local f else add (Names.lvl_to_string f);
          List.iter (fun arg -> add " "; go lvl true arg) (List.rev args);
          close_paren (atom && args <> [])
      | VFlex (f, args) ->
          let Empty { scope; susp } = !f in
          open_paren (atom && args <> []);
          (* It would be nice to have a better representation of holes *)
          add ("?[at lvl " ^ string_of_int scope ^ "]");
          List.iter (fun arg -> add " "; go lvl true arg) (List.rev args);
          close_paren (atom && args <> [])
      | VLam f ->
          open_paren atom;
          show_local lvl;
          add "\\ ";
          go (lvl+1) false (f (VRigid(lvl, [])));
          close_paren atom in
    go lvl false vtm;
    Buffer.contents buf

  let debug_vtm lvl vtm =
    print_endline (to_string lvl vtm);
    vtm
end

module Unify : sig
  val unify_or_suspend : lvl -> Data.vtm -> Data.vtm -> CPS.computation
end = struct
  open Data

  (* not a pattern unification problem, delay until this hole is filled *)
  exception NotPattern of hole ref
  exception DoesNotUnify

  let rec unify (unsusp: CPS.computation list -> unit) lvl a b =
    match deref a, deref b with
    (* Rigid-rigid *)
    | VRigid(f_a, args_a), VRigid(f_b, args_b) when f_a = f_b ->
        (* must have same length args lists to be well-typed *)
        assert (List.length args_a = List.length args_b);
        List.iter2 (unify unsusp lvl) args_a args_b

    (* Eta! *)
    | VLam a, b ->
        let x = VRigid(lvl, []) in
        unify unsusp (lvl+1) (a x) (app b x)
    | a, VLam b ->
        let x = VRigid(lvl, []) in
        unify unsusp (lvl+1) (app a x) (b x)

    (* Flex-flex *)
    | VFlex(h_a, args_a), VFlex(h_b, args_b) ->
        if h_a == h_b then begin
          (* must have same length args lists to be well-typed *)
          assert (List.length args_a = List.length args_b);
          prune h_a args_a args_b
        end else unify_flex_flex lvl h_a args_a h_b args_b

    (* Flex-rigid *)
    | VFlex(h, args), b -> unify_flex unsusp lvl h args b
    | a, VFlex(h, args) -> unify_flex unsusp lvl h args a

    | _ -> raise DoesNotUnify

  and add_lambdas n tm =
    if n = 0 then tm else add_lambdas (n-1) (Abs tm)

  (* prune those arguments which are disequal *)
  and prune hole args_a args_b =
    let rec helper i changed acc xs ys =
      match List.map deref xs, List.map deref ys with
        | [], [] -> if changed then
            let Empty { scope; susp } = !hole in
            let new_hole = ref (Empty { scope; susp }) in
            let f = Hole new_hole in
            let with_args = List.fold_left (fun f x -> App(f, x)) f acc in
            let with_lams = add_lambdas i with_args in
            fill hole (eval [] with_lams)
        | VRigid(x, [])::xs, VRigid(y, [])::ys ->
            if x = y then helper (i+1) changed (Local i::acc) xs ys
            else helper (i+1) true acc xs ys
        | _ -> raise (NotPattern hole) in
    helper 0 false [] args_a args_b

  (* make a map from variables to their names in the solution *)
  and invert_spine lvl hole hole_lvl (spine: vtm list): lvl -> idx option =
    let arr = Array.make (lvl - hole_lvl) None in
    List.iteri (fun i x -> match deref x with
      | VRigid(v, []) when v >= hole_lvl && arr.(v - hole_lvl) = None ->
          arr.(v - hole_lvl) <- Some i
      | _ -> raise (NotPattern hole)) spine;
    fun v -> arr.(v - hole_lvl)

  and unify_flex unsusp initial_lvl hole args soln =
    let Empty { scope = hole_lvl; susp } = !hole in
    unsusp susp;
    let args_len = List.length args in
    let ren = invert_spine initial_lvl hole hole_lvl args in
    (* ugh level math *)
    let lvl_diff = initial_lvl - (hole_lvl + args_len) in
    let rename_var lvl = function
      | v when v < hole_lvl     -> Some (Global v)
      | v when v >= initial_lvl -> Some (Local (lvl - lvl_diff - v - 1))
      | v -> Option.map (fun i -> Local (i + lvl - initial_lvl)) (ren v) in
    (* quote and apply the renaming to the soln *)
    let rec apply_renaming lvl tm = match deref tm with
      | VRigid(v, xs) -> begin
          match rename_var lvl v with
            | Some v' -> rename_args lvl v' xs
            | None -> raise DoesNotUnify
          end
      | VFlex(h, xs)  ->
          if h == hole then raise DoesNotUnify else (* occurs check *)
          let Empty { scope; susp = h_susp } = !h in
          if scope > hole_lvl then
            (* convert the extra part of its scope to explicit applications *)
            let rec go spine tm i =
              if i = scope then spine, tm
              else match rename_var lvl i with
                | Some v -> go (VRigid(i,[]) :: spine) (App(tm, v)) (i+1)
                | None -> go spine tm (i+1) in
            let new_hole = ref (Empty { scope = hole_lvl; susp = h_susp }) in
            let spine, tm = go [] (Hole new_hole) hole_lvl in
            fill h (VFlex(new_hole, spine));
            rename_args lvl tm xs
          else
            rename_args lvl (Hole h) xs
      | VLam f        -> Abs (apply_renaming (lvl+1) (f (VRigid(lvl, []))))
    and rename_args lvl head args =
      List.fold_right (fun arg f -> App(f, apply_renaming lvl arg)) args head in
    fill hole (eval [] (add_lambdas args_len (apply_renaming initial_lvl soln)))

  and unify_flex_flex lvl h_a args_a h_b args_b =
    (* Flex-flex case of pattern unification: take the intersection of their
       arguments *)
    let Empty { scope = lvl_a; susp = susp_a } = !h_a in
    let Empty { scope = lvl_b; susp = susp_b } = !h_b in
    let len_args_a = List.length args_a in
    let len_args_b = List.length args_b in
    let make_renaming l hole spine =
      let ren = invert_spine lvl hole l spine in fun v ->
        if v < l then Some (Global v)
        else Option.map (fun i -> Local i) (ren v) in
    let ren_a = make_renaming lvl_a h_a args_a in
    let ren_b = make_renaming lvl_b h_b args_b in
    let rec intersect l a b =
      if l = lvl then begin
        fill h_a (eval [] (add_lambdas len_args_a a));
        fill h_b (eval [] (add_lambdas len_args_b b))
      end else match ren_a l, ren_b l with
        | Some x, Some y -> intersect (l+1) (App(a,x)) (App(b,y))
        | _              -> intersect (l+1) a b in
    let new_hole =
      Hole (ref (Empty { scope = min lvl_a lvl_b; susp = susp_a @ susp_b })) in
    intersect (min lvl_a lvl_b) new_hole new_hole

  let rec unify_or_suspend lvl a b fk sk =
    let what_next = ref CPS.id in
    let unsusp comps =
      what_next := List.fold_right CPS.compose comps !what_next in
    match unify unsusp lvl a b with
      | exception DoesNotUnify -> fk ()
      | exception (NotPattern hole) ->
          let Empty { scope; susp } = !hole in
          hole := Empty { scope; susp = (unify_or_suspend lvl a b)::susp };
          !what_next fk sk
      | () -> !what_next fk sk
end

module Runtime = struct
  open Data

  type clause =
    { n_vars: int
    ; functor_: lvl
    ; args: tm list
    ; body: tm list }

  (* dynamically bound things *)
  type ctx = { lvl: lvl; local_clauses: clause list }

  let initial_ctx: ctx = { lvl = 0; local_clauses = [] }

  module Database : sig
    val lookup_clauses : ctx -> lvl -> clause list
    val asserta : clause -> unit
    val assertz : clause -> unit
  end = struct
    let database: (lvl, clause list) Hashtbl.t = Hashtbl.create 20

    let lookup_clauses (ctx: ctx) functor_ =
      List.filter (fun cls -> cls.functor_ = functor_) ctx.local_clauses
        @ Hashtbl.find database functor_

    let asserta (cls: clause) =
      let old_clauses =
        Option.value ~default:[] (Hashtbl.find_opt database cls.functor_) in
      Hashtbl.replace database cls.functor_ (cls :: old_clauses)
    let assertz (cls: clause) =
      let old_clauses =
        Option.value ~default:[] (Hashtbl.find_opt database cls.functor_) in
      Hashtbl.replace database cls.functor_ (old_clauses @ [cls])
  end

  (* helper function for writing failure continuations *)
  let backtracking (k: unit -> unit): CPS.failure_cont =
    let trailmarker = trail.size in
    fun () -> backtrack_to trailmarker; k ()

  let compile_to_clause base_lvl vtm =
    let rec to_clause lvl (a: vtm): clause = match deref a with
      | VRigid(f, args) when f = Names.pi ->
          let [fn] = args in
          let cls = to_clause (lvl+1) (app fn (VRigid(lvl,[]))) in
          { cls with n_vars = cls.n_vars + 1 }
      | VRigid(f, args) when f = Names.implies || f = Names.neck ->
          let head, body =
            let [x; y] = args in
            if f = Names.neck then y, x else x, y in
          let cls = to_clause lvl head in
          assert (cls.n_vars = 0); (* disallow (pi x\ f x) :- body *)
          let goal = quote base_lvl lvl body in
          { cls with body = goal :: cls.body }
      | VRigid(f, args) ->
          assert (not (List.mem f Names.reserved_names));
          { n_vars = 0
          ; functor_ = f
          ; args = List.map (quote base_lvl lvl) args
          ; body = [] }
      | VFlex _ -> failwith "The hypothetical clause is a flexible term"
      | VLam _ -> failwith "unreachable: runtime type error" in
    to_clause base_lvl vtm


  let rec exec_clause (ctx: ctx) (cls: clause) (args: vtm list) fk sk =
    (* lexically bound state: cutpoint and env *)
    let cutpt = fk in
    let rec make_env acc n =
      if n = 0 then acc
      else make_env (VFlex(fresh_hole ctx.lvl, []) :: acc) (n-1) in
    let env = make_env [] cls.n_vars in
    (* unify the arguments *)
    let rec unify_args args params fk sk = match args, params with
      | [], [] -> sk fk
      | a::args, p::params ->
          Unify.unify_or_suspend ctx.lvl a (eval env p) fk (fun fk' ->
            unify_args args params fk' sk) in
    unify_args args cls.args fk (fun fk ->
      (* run the body *)
      let run_one x = exec_goal ctx cutpt (eval env x) in
      let rec run_body fk = function
        | [] -> sk fk
        | [x] -> run_one x fk sk
        | x::xs -> run_one x fk (fun fk' -> run_body fk' xs) in
      run_body fk cls.body)

  and exec_goal (ctx: ctx) cutpt vtm fk sk = match deref vtm with
    | VRigid(f, args) when f = Names.cut ->
        (* !: make the cut point the new failure continuation *)
        assert (args = []);
        sk cutpt
    | VRigid(f, args) when f = Names.pi ->
        (* pi x\ goal: make a new constant x and exec goal *)
        let [fn] = args in
        let new_var = VRigid(ctx.lvl, []) in
        exec_goal { ctx with lvl = ctx.lvl + 1 } cutpt (app fn new_var) fk sk
    | VRigid(f, args) when f = Names.sigma ->
        (* sigma X\ goal: make a new hole X and exec goal *)
        let [fn] = args in
        exec_goal ctx cutpt (app fn (VFlex(fresh_hole ctx.lvl, []))) fk sk
    | VRigid(f, args) when f = Names.implies || f = Names.neck ->
        (* hyp => goal: add hyp as a local clause and exec goal *)
        let hyp, goal =
          let [x; y] = args in
          if f = Names.implies then y, x else x, y in
        let cls = compile_to_clause ctx.lvl hyp in
        let new_ctx = { ctx with local_clauses = cls :: ctx.local_clauses } in
        exec_goal new_ctx cutpt goal fk sk
    | VRigid(f, args) when f = Names.comma ->
        (* special-cased to keep the same cut point *)
        let [rhs; lhs] = args in
        exec_goal ctx cutpt lhs fk (fun fk' ->
          exec_goal ctx cutpt rhs fk' sk)
    | VRigid(f, args) when f = Names.semi ->
        (* special-cased to keep the same cut point *)
        let [rhs; lhs] = args in
        exec_goal ctx cutpt lhs (backtracking (fun () ->
          exec_goal ctx cutpt rhs fk sk)) sk
    | VRigid(f, args) when f = Names.eq ->
        (* lhs = rhs: unify the terms! *)
        let [rhs; lhs] = args in
        Unify.unify_or_suspend ctx.lvl lhs rhs fk sk
    | VRigid(f, args) ->
        (* User-defined predicate: try each clause *)
        let rec go = function
          | [] -> fk ()
          | [cls] ->
              exec_clause ctx cls args fk sk
          | cls::clss ->
              let fk' = backtracking (fun () -> go clss) in
              exec_clause ctx cls args fk' sk in
        go (Database.lookup_clauses ctx f)
    | VFlex _ -> failwith "The goal is a flexible term"
    | VLam _ -> failwith "unreachable: runtime type error"

end

module Interactive = struct
  open Data

  type user_goal =
    { free_count: int
    ; vars: (string, lvl) Hashtbl.t
    ; term: tm }

  let interact (goal: user_goal) =
    let rec make_env acc n =
      if n = 0 then acc else make_env (VFlex(fresh_hole 0, []) :: acc) (n-1) in
    let env = make_env [] goal.free_count in
    let sk fk =
      print_endline "yes.";
      Hashtbl.iter (fun name l ->
        let x = List.nth env (goal.free_count - l - 1) in
        print_endline (" " ^ name ^ " = " ^ Data.to_string 0 x);
        print_string "more? "; flush stdout;
        let resp = read_line () in
        if List.mem resp ["y"; "yes"; ";"] then fk ()) goal.vars in
    let fk () = print_endline "no." in
    Runtime.exec_goal Runtime.initial_ctx fk (eval env goal.term) fk sk
end


module AST : sig
  type term =
    | RigidVar of string
    | FlexVar of string
    | Abs of string * term
    | App of term * term
    | Wildcard

  val parse : string -> (term list, string) result
end = struct
  type term =
    | RigidVar of string
    | FlexVar of string
    | Abs of string * term
    | App of term * term
    | Wildcard

  open Angstrom (* parser combinators library *)

  let whitespace =
    let is_space = String.contains " \n\t" in
    let spaces = skip is_space *> skip_while is_space in
    let comment = char '%' *> skip_while (fun c -> c <> '\n') in
    skip_many (comment <|> spaces)
  let lexeme a = a <* whitespace
  let str s = lexeme (string s) *> return ()
  let ident_tail =
    let is_ident_char c =
      c = '_'
        || ('a' <= c && c <= 'z')
        || ('A' <= c && c <= 'Z')
        || ('0' <= c && c <= '0') in
    lexeme (take_while is_ident_char)

  let rigid_var =
    let+ first_char = satisfy (fun c -> 'a' <= c && c <= 'z')
    and+ rest = ident_tail in 
    RigidVar (String.make 1 first_char ^ rest)
  let flex_var =
    let+ first_char = satisfy (fun c -> c = '_' || ('A' <= c && c <= 'Z'))
    and+ rest = ident_tail in
    match String.make 1 first_char ^ rest with
      | "_" -> Wildcard
      | v -> FlexVar v

  let binop op a b = App(App(RigidVar op, a), b)

  let chainr1 op elem = fix (fun p ->
    let+ x = elem
    and+ cont = option Fun.id (lift2 Fun.flip op p) in
    cont x)

  let exp = fix (fun exp ->
    let mklam body = function
      | FlexVar v -> Abs(v, body)
      | RigidVar v -> Abs(v, body)
      | Wildcard -> Abs("¯\\_(ツ)_/¯", body)
      | _ -> failwith "unreachable" in
    let var_or_lambda =
      let+ var = rigid_var <|> flex_var
      and+ maybe_lambda = option Fun.id (lift mklam (str "\\" *> exp)) in
      maybe_lambda var in
    let atomic_exp = (str "(" *> exp <* str ")") <|> var_or_lambda in
    let make_app (f::args) =
      List.fold_left (fun f arg -> App(f, arg)) f args in
    let simple_exp = lift make_app (many1 atomic_exp) in
    let eq_exp =
      let+ e = simple_exp
      and+ equation = option Fun.id
        (lift (binop "=") (str "=" *> simple_exp)) in
      equation e in
    let comma_exp =
      let comma_op = str "," *> return (binop ",") in
      let implies_op = str "=>" *> return (binop "=>") in
      chainr1 (comma_op <|> implies_op) eq_exp in
    let semis_exp =
      let semi_op = str ";" *> return (binop ";") in
      let neck_op = str ":-" *> return (binop ":-") in
      chainr1 (semi_op <|> neck_op) comma_exp in
    semis_exp)

  let defn = exp <* str "."
  let program = whitespace *> many defn

  let parse (input: string): (term list, string) result =
    parse_string ~consume:Consume.All program input
end

module Compiler : sig
  val lower_clause: AST.term -> Runtime.clause
  val lower_goal  : AST.term -> Interactive.user_goal
end = struct
  (* kinda boring compiler, just translates AST to Data.tm *)
  open Data

  type free =
    { mutable count: int
    ; mutable wildcards: lvl list
    ; table: (string, lvl) Hashtbl.t }

  let collect_free_vars (tm: AST.term) =
    let free: free = { count = 0; wildcards = []; table = Hashtbl.create 20 } in
    let rec helper env (tm: AST.term) = match tm with
      | RigidVar _ -> ()
      | FlexVar v ->
          if not (Hashtbl.mem free.table v) && not (List.mem v env) then begin
            Hashtbl.add free.table v free.count;
            free.count <- free.count + 1
          end
      | Abs(v, x) -> helper (v::env) x
      | App(x, y) -> helper env x; helper env y
      | Wildcard ->
          free.wildcards <- free.count :: free.wildcards;
          free.count <- free.count + 1 in
    helper [] tm;
    free

  let lookup_in_env var env =
    let rec go i = function
      | [] -> None
      | x::_ when x = var -> Some i
      | _::xs -> go (i+1) xs in 
    go 0 env

  let lower (tm: AST.term) =
    let free = collect_free_vars tm in
    let rec helper lvl env (tm: AST.term) =
      match tm with
        | RigidVar v ->
            begin match lookup_in_env v env with
              | Some i -> Local i
              | None -> Global (Names.string_to_lvl v)
            end
        | FlexVar v ->
            begin match lookup_in_env v env with
              | Some i -> Local i
              | None -> Local (lvl - Hashtbl.find free.table v - 1)
            end
        | Abs(v, x) -> Abs (helper (lvl+1) (v::env) x)
        | App(x, y) -> App(helper lvl env x, helper lvl env y)
        | Wildcard ->
            let x::xs = free.wildcards in
            free.wildcards <- xs;
            Local (lvl - x - 1) in
    free, helper free.count [] tm

  let lower_clause tm: Runtime.clause =
    let free, lowered = lower tm in
    let rec add_binders acc n = if n = 0 then acc else
      add_binders (App(Global Names.pi, Abs(acc))) (n-1) in
    let tm_with_pis = add_binders lowered free.count in
    let vtm_with_pis = eval [] tm_with_pis in
    Runtime.compile_to_clause 0 vtm_with_pis

  let lower_goal tm: Interactive.user_goal =
    let free, lowered = lower tm in
    { free_count = free.count; vars = free.table; term = lowered }
end

(* To do: type checking *)
(* I'll get around to it sometime *)

let load filename =
  let contents = Stdio.In_channel.read_all filename in
  match AST.parse contents with
    | Error e ->
        print_endline ("Parse error: " ^ filename ^ e)
    | Ok defns ->
        List.iter (fun defn ->
          let cls = Compiler.lower_clause defn in
          Runtime.Database.assertz cls) defns;
        print_endline ("Loaded " ^ filename)

let run_goal input =
  match AST.parse input with
    | Error e ->
        print_endline ("Parse error in goal" ^ e)
    | Ok goals ->
        List.iter (fun goal ->
          let goal = Compiler.lower_goal goal in
          Interactive.interact goal) goals

let rec repl () =
  print_string "?- ";
  flush stdout;
  let input = read_line () in
  if input <> ":q" && input <> ":quit" then begin
    run_goal input;
    repl ()
  end

let main () =
  let usage = "lp [--goal <goal>] file.lpr..." in
  let append_to r x = r := !r @ [x] in
  let goals = ref [] in
  let filenames = ref [] in
  let spec = ["--goal", Arg.String (append_to goals), "Goal to run"] in
  Arg.parse spec (append_to filenames) usage;
  List.iter load !filenames;
  List.iter run_goal !goals;
  if !goals = [] then
    repl ()

let () = main ()
