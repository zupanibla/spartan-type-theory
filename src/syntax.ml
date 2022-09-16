(** Abstract syntax of expressions, before they are type-checked. *)

(** De Bruijn index *)
type index = int

(** Expressions *)
type expr = expr' Location.located
and expr' =
  | Var of index
  | Type
  | Prod of (Name.ident * ty) * ty
  | Lambda of (Name.ident * ty option) * expr
  | Apply of expr * expr
  | Ascribe of expr * ty
  | Nat
  | Zero
  | Succ of expr
  | IndNat of expr * expr * expr * expr
  | Empty
  | IndEmpty of expr * expr
  | Identity of expr * expr
  | Refl of expr
  | IndId of expr * expr * expr

(** Types (equal to expressions at this point). *)
and ty = expr

(** Top-level commands. *)
type toplevel = toplevel' Location.located
and toplevel' =
  | TopLoad of toplevel list
  | TopDefinition of Name.ident * expr
  | TopCheck of expr
  | TopEval of expr
  | TopAxiom of Name.ident * expr

(** Shift all indices greter than or equal to [n] by [k]. *)
let rec shift n k {Location.data=e'; loc} =
  let e' = shift' n k e' in
  Location.locate ~loc e'

and shift' n k = function

  | Var j -> if j >= n then Var (j + k) else Var j

  | Type -> Type

  | Prod ((x, t), u) ->
     let t = shift_ty n k t
     and u = shift_ty (n + 1) k u in
     Prod ((x, t), u)

  | Lambda ((x, topt), e) ->
     let t = shift_tyopt n k topt
     and e = shift (n + 1) k e in
     Lambda ((x, t), e)

  | Apply (e1, e2) ->
     let e1 = shift n k e1
     and e2 = shift n k e2 in
     Apply (e1, e2)

  | Ascribe (e, t) ->
     let e = shift n k e
     and t = shift_ty n k t in
     Ascribe (e, t)

  | Nat     -> Nat
  | Zero    -> Zero
  | Succ e1 -> Succ (shift n k e1)
  | IndNat (e1, e2, e3, e4) ->
     let e1 = shift n k e1
     and e2 = shift n k e2
     and e3 = shift n k e3
     and e4 = shift n k e4 in
     IndNat (e1, e2, e3, e4)

  | Empty -> Empty
  | IndEmpty (e1, e2) ->
     let e1 = shift n k e1
     and e2 = shift n k e2 in
     IndEmpty (e1, e2)

  | Identity (e1, e2) ->
     let e1 = shift n k e1
     and e2 = shift n k e2 in
     Identity (e1, e2)
  | Refl e1 -> Refl (shift n k e1)
  | IndId (e1, e2, e3) ->
     let e1 = shift n k e1
     and e2 = shift n k e2
     and e3 = shift n k e3 in
     IndId (e1, e2, e3)

and shift_ty n k t = shift n k t

and shift_tyopt n k = function
  | None -> None
  | Some t -> Some (shift_ty n k t)
