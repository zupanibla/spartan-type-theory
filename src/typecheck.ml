(** Spartan type checking. *)

(** Type errors *)
type type_error =
  | InvalidIndex of int
  | TypeExpected of TT.ty * TT.ty
  | TypeExpectedButFunction of TT.ty
  | FunctionExpected of TT.ty
  | CannotInferArgument of Name.ident

exception Error of type_error Location.located

(** [error ~loc err] raises the given type-checking error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

let print_error ~penv err ppf =
  match err with

  | InvalidIndex k -> Format.fprintf ppf "invalid de Bruijn index %d, please report" k

  | TypeExpected (ty_expected, ty_actual) ->
     Format.fprintf ppf "this expression should have type %t but has type %t"
                        (TT.print_ty ~penv ty_expected)
                        (TT.print_ty ~penv ty_actual)

  | TypeExpectedButFunction ty ->
     Format.fprintf ppf "this expression is a function but should have type %t"
                        (TT.print_ty ~penv ty)

  | FunctionExpected ty ->
     Format.fprintf ppf "this expression should be a function but has type %t"
                        (TT.print_ty ~penv ty)

  | CannotInferArgument x ->
     Format.fprintf ppf "cannot infer the type of %t" (Name.print_ident x)

(** [infer ctx e] infers the type [ty] of expression [e]. It returns
    the processed expression [e] and its type [ty].  *)
let rec infer ctx {Location.data=e'; loc} =
  match e' with

  | Syntax.Var k ->
     begin
       match Context.lookup k ctx with
       | None -> error ~loc (InvalidIndex k)
       | Some (a, t) -> TT.Atom a, t
     end

  | Syntax.Type ->
     TT.Type, TT.ty_Type

  | Syntax.Prod ((x, t), u) ->
     let t = check_ty ctx t in
     let x' = TT.new_atom x in
     let ctx = Context.extend_ident x' t ctx in
     let u = check_ty ctx u in
     let u = TT.abstract_ty x' u in
     TT.Prod ((x, t), u),
     TT.ty_Type

  | Syntax.Lambda ((x, Some t), e) ->
     let t = check_ty ctx t in
     let x' = TT.new_atom x in
     let ctx  = Context.extend_ident x' t ctx in
     let e, u = infer ctx e in
     let e = TT.abstract x' e in
     let u = TT.abstract_ty x' u in
     TT.Lambda ((x, t), e),
     TT.Ty (TT.Prod ((x, t), u))

  | Syntax.Lambda ((x, None), _) ->
     error ~loc (CannotInferArgument x)

  | Syntax.Apply (e1, e2) ->
     let e1, t1 = infer ctx e1 in
     begin
       match Equal.as_prod ctx t1 with
       | None -> error ~loc (FunctionExpected t1)
       | Some ((x, t), u) ->
          let e2 = check ctx e2 t in
          TT.Apply (e1, e2),
          TT.instantiate_ty e2 u
     end

  | Syntax.Ascribe (e, t) ->
     let t = check_ty ctx t in
     let e = check ctx e t in
     e, t

  | Syntax.IndNat (p, p0, ps, n) ->
     let p  = check ctx p  (TT.Ty (TT.Prod ((Name.anonymous (), TT.ty_Nat), TT.ty_Type))) in
     let p0 = check ctx p0 (TT.Ty (TT.Apply (p, TT.Zero))) in
     let ps = check ctx ps (
        TT.Ty (TT.Prod ((Name.anonymous (), TT.ty_Nat),
           TT.Ty (TT.Prod ((Name.anonymous (), TT.Ty (TT.Apply (p, TT.Bound 0))),
              TT.Ty (TT.Apply (p, TT.Succ (TT.Bound 1)))
           ))
        ))
     ) in
     let n  = check ctx n TT.ty_Nat in
     TT.IndNat (p, p0, ps, n),
     TT.Ty (TT.Apply (p, n))

  | Syntax.Nat ->
     TT.Nat,
     TT.ty_Type

  | Syntax.Zero ->
     TT.Zero,
     TT.ty_Nat

  | Syntax.Succ e1 ->
     TT.Succ (check ctx e1 TT.ty_Nat),
     TT.ty_Nat

  | Syntax.Empty ->
     TT.Empty,
     TT.ty_Type

  | Syntax.IndEmpty (p, e) ->
     let p  = check ctx p  (TT.Ty (TT.Prod ((Name.anonymous (), TT.Ty (TT.Empty)), TT.ty_Type)))
     and e  = check ctx e (TT.Ty (TT.Empty)) in
     TT.IndEmpty (p, e),
     TT.Ty (TT.Apply (p, e))

  | Syntax.Identity (e1, e2) ->
     let e1, t1 = infer ctx e1 in
     let e2 = check ctx e2 t1 in
     TT.Identity (e1, e2),
     TT.ty_Type

  | Syntax.Refl e1 ->
     let e1, t1 = infer ctx e1 in
     TT.Refl e1,
     TT.Ty (TT.Identity (e1, e1))

  | Syntax.IndId (c, d, a, b, p) ->
     let a, t = infer ctx a in
     let b = check ctx b t in
     let p = check ctx p (TT.Ty (TT.Identity (a, b))) in
     let c = check ctx c (
         TT.Ty (TT.Prod ((Name.Ident ("x", Name.Word), t),
            TT.Ty (TT.Prod ((Name.Ident ("y", Name.Word), t),
               TT.Ty (TT.Prod ((Name.Ident ("p", Name.Word), TT.Ty (TT.Identity (TT.Bound(1), TT.Bound(0)))),
                  TT.ty_Type
               ))
            ))
         ))
     ) in
     let d = check ctx d (
         TT.Ty (TT.Prod ((Name.Ident ("x", Name.Word), t), TT.Ty (
            TT.Apply (
               TT.Apply (
                  TT.Apply (
                     c,
                     TT.Bound 0
                  ),
                  TT.Bound 0
               ),
               TT.Refl (TT.Bound 0)
            )
         )))
     ) in
     TT.IndId (c, d, a, b, p),
     TT.Ty (TT.Apply (TT.Apply (TT.Apply (c, a), b), p))

(** [check ctx e ty] checks that [e] has type [ty] in context [ctx].
    It returns the processed expression [e]. *)
and check ctx ({Location.data=e'; loc} as e) ty =
  match e' with

  | Syntax.Lambda ((x, None), e) ->
     begin
       match Equal.as_prod ctx ty with
       | None -> error ~loc (TypeExpectedButFunction ty)
       | Some ((x, t), u) ->
          let x' = TT.new_atom x in
          let ctx = Context.extend_ident x' t ctx
          and u = TT.unabstract_ty x' u in
          check ctx e u
     end

  | Syntax.Lambda ((_, Some _), _)
  | Syntax.Apply _
  | Syntax.Prod _
  | Syntax.Var _
  | Syntax.Type
  | Syntax.Ascribe _
  | Syntax.Nat
  | Syntax.Zero
  | Syntax.Succ _
  | Syntax.IndNat _
  | Syntax.Empty
  | Syntax.IndEmpty _
  | Syntax.Identity _
  | Syntax.Refl _
  | Syntax.IndId _
  ->
     let e, ty' = infer ctx e in
     if Equal.ty ctx ty ty'
     then
       e
     else
       error ~loc (TypeExpected (ty, ty'))


(** [check_ty ctx t] checks that [t] is a type in context [ctx]. It returns the processed
   type [t]. *)
and check_ty ctx t =
  let t = check ctx t TT.ty_Type in
  TT.Ty t

let rec toplevel ~quiet ctx {Location.data=tc; loc} =
  let ctx = toplevel' ~quiet ctx tc in
  ctx

and toplevel' ~quiet ctx = function

  | Syntax.TopLoad lst ->
     topfile ~quiet ctx lst

  | Syntax.TopDefinition (x, e) ->
     let e, ty = infer ctx e in
     let x' = TT.new_atom x in
     let ctx = Context.extend_ident x' ty ctx in
     let ctx = Context.extend_def x' e ctx in
     if not quiet then Format.printf "%t is defined.@." (Name.print_ident x) ;
     ctx

  | Syntax.TopCheck e ->
     let e, ty = infer ctx e in
     Format.printf "@[<hov>%t@]@\n     : @[<hov>%t@]@."
       (TT.print_expr ~penv:(Context.penv ctx) e)
       (TT.print_ty ~penv:(Context.penv ctx) ty) ;
     ctx

  | Syntax.TopEval e ->
     let e, ty = infer ctx e in
     let e = Equal.norm_expr ~strategy:Equal.CBV ctx e
     and ty = Equal.norm_ty ~strategy:Equal.CBV ctx ty in
     Format.printf "@[<hov>%t@]@\n     : @[<hov>%t@]@."
       (TT.print_expr ~penv:(Context.penv ctx) e)
       (TT.print_ty ~penv:(Context.penv ctx) ty) ;
     ctx

  | Syntax.TopAxiom (x, ty) ->
     let ty = check_ty ctx ty in
     let x' = TT.new_atom x in
     let ctx = Context.extend_ident x' ty ctx in
     if not quiet then Format.printf "%t is assumed.@." (Name.print_ident x) ;
     ctx

and topfile ~quiet ctx lst =
  let rec fold ctx = function
    | [] -> ctx
    | top_cmd :: lst ->
       let ctx = toplevel ~quiet ctx top_cmd in
       fold ctx lst
  in
  fold ctx lst
