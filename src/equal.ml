(** Equality and normalization. *)

(** A normalization strategy. *)
type strategy =
  | WHNF (** normalize to weak head-normal form *)
  | CBV (** call-by-value normalization *)

(** Normalize an expression. *)
let rec norm_expr ~strategy ctx e =
  let norm e = norm_expr ~strategy ctx e in
  let norm_ty t = norm_ty ~strategy ctx t in
  let norm_if_cbv e = begin match strategy with
    | WHNF -> e
    | CBV  -> norm e
  end in
  let norm_ty_if_cbv t = begin match strategy with
    | WHNF -> t
    | CBV  -> norm_ty t
  end in
  match e with
  | TT.Bound k -> assert false

  | TT.Type -> e

  | TT.Atom x ->
    begin
      match Context.lookup_def x ctx with
      | None -> e
      | Some e -> norm e
    end

  | TT.Prod _ -> e

  | TT.Lambda _ -> e

  | TT.Apply (e1, e2) ->
    let e1 = norm e1
    and e2 = norm_if_cbv e2 in
    begin
      match e1 with
      | TT.Lambda (_, e') ->
        let e' = TT.instantiate e2 e' in
        norm e'
      | _ -> TT.Apply (e1, e2)
    end

  | TT.Nat    -> e
  | TT.Zero   -> e
  | TT.Succ n -> TT.Succ (norm_if_cbv n)
  | TT.IndNat (p, p0, ps, n) ->
    let n' = norm n in
    begin
     match n' with
     | TT.Zero   -> norm p0
     | TT.Succ m -> norm (TT.Apply (TT.Apply (ps, m), TT.IndNat (p, p0, ps, m)))
     | _ -> TT.IndNat (norm_if_cbv p, norm_if_cbv p0, norm_if_cbv ps, norm_if_cbv n)
    end

  | TT.Empty -> e
  | TT.IndEmpty (p, e) -> TT.IndEmpty (norm_if_cbv p, norm_if_cbv e)
  | TT.Identity (t, e1, e2) -> TT.Identity (norm_ty_if_cbv t, norm_if_cbv e1, norm_if_cbv e2)
  | TT.Refl (t, e) -> TT.Refl (norm_ty_if_cbv t, norm_if_cbv e)
  | TT.IndId (t, c, d, a, b, p) ->
    let p' = norm p in
    begin
      match p' with
      | TT.Refl (t, e) -> norm (TT.Apply (d, a))
      | _ -> TT.IndId (norm_ty_if_cbv t, norm_if_cbv c, norm_if_cbv d, norm_if_cbv a, norm_if_cbv b, norm_if_cbv p)
    end

(** Normalize a type *)
and norm_ty ~strategy ctx (TT.Ty ty) =
  let ty = norm_expr ~strategy ctx ty in
  TT.Ty ty

(** Normalize a type to a product. *)
let as_prod ctx t =
  let TT.Ty t' = norm_ty ~strategy:WHNF ctx t in
  match t' with
  | TT.Prod ((x, t), u) -> Some ((x, t), u)
  | _ -> None

(** Normalize a type to the identity type. *)
let as_identity ctx t =
  let TT.Ty t' = norm_ty ~strategy:WHNF ctx t in
  match t' with
  | TT.Identity (t, a, b) -> Some (t, a, b)
  | _ -> None

(** Compare expressions [e1] and [e2] at type [ty]? *)
let rec expr ctx e1 e2 ty =
  (* short-circuit *)
  (e1 == e2) ||
  begin
    (* The type directed phase *)
    let TT.Ty ty' = norm_ty ~strategy:WHNF ctx ty in
    match  ty' with

    | TT.Prod ((x, t), u) ->
      (* Apply function extensionality. *)
      let x' = TT.new_atom x in
      let ctx = Context.extend_ident x' t ctx
      and e1 = TT.Apply (e1, TT.Atom x')
      and e2 = TT.Apply (e2, TT.Atom x')
      and u = TT.unabstract_ty x' u in
      expr ctx e1 e2 u

    | TT.Type
    | TT.Apply _
    | TT.Bound _
    | TT.Atom _
    | TT.Nat
    | TT.Zero
    | TT.Succ _
    | TT.IndNat _
    | TT.Empty
    | TT.IndEmpty _
    | TT.Identity _
    | TT.Refl _
    | TT.IndId _
    ->
      (* Type-directed phase is done, we compare normal forms. *)
      let e1 = norm_expr ~strategy:WHNF ctx e1
      and e2 = norm_expr ~strategy:WHNF ctx e2 in
      expr_whnf ctx e1 e2

    | TT.Lambda _ ->
      (* A type should never normalize to an abstraction *)
      assert false
  end

(** Structurally compare weak head-normal expressions [e1] and [e2]. *)
and expr_whnf ctx e1 e2 =
  match e1, e2 with

  | TT.Type, TT.Type -> true

  | TT.Bound k1, TT.Bound k2 ->
    (* We should never be in a situation where we compare bound variables,
       as that would mean that we forgot to unabstract a lambda or a product. *)
    assert false

  | TT.Atom x, TT.Atom y -> x = y

  | TT.Prod ((x, t1), u1), TT.Prod ((_, t2), u2)  ->
    ty ctx t1 t2 &&
    begin
      let x' = TT.new_atom x in
      let ctx = Context.extend_ident x' t1 ctx
      and u1 = TT.unabstract_ty x' u1
      and u2 = TT.unabstract_ty x' u2 in
      ty ctx u1 u2
    end

  | TT.Lambda ((x, t1), e1), TT.Lambda ((_, t2), e2)  ->
    (* We should never have to compare two lambdas, as that would mean that the
       type-directed phase did not figure out that these have product types. *)
    assert false

  | TT.Apply (e11, e12), TT.Apply (e21, e22) ->
    let rec collect sp1 sp2 e1 e2 =
      match e1, e2 with
      | TT.Apply (e11, e12), TT.Apply (e21, e22) ->
        collect (e12 :: sp1) (e22 :: sp2) e11 e21
      | TT.Atom a1, TT.Atom a2 ->
        Some ((a1, sp1), (a2, sp2))
      | _, _ -> None
    in
    begin
      match collect [e12] [e22] e11 e21 with
      | None -> false
      | Some ((a1, sp1), (a2, sp2)) -> spine ctx (a1, sp1) (a2, sp2)
    end

  | TT.Nat, TT.Nat -> true
  | TT.Zero, TT.Zero -> true
  | TT.Succ e1, TT.Succ e2 -> expr ctx e1 e2 TT.ty_Nat
  | TT.IndNat (a1, a2, a3, a4), TT.IndNat (b1, b2, b3, b4) ->
     let p = a1 in
     expr ctx a1 b1 (TT.Ty (TT.Prod ((Name.anonymous (), TT.ty_Nat), TT.ty_Type))) &&
     expr ctx a2 b2 (TT.Ty (TT.Apply (p, TT.Zero))) &&
     expr ctx a3 b3 (
        TT.Ty (TT.Prod ((Name.anonymous (), TT.ty_Nat),
           TT.Ty (TT.Prod ((Name.anonymous (), TT.Ty (TT.Apply (p, TT.Bound 0))),
              TT.Ty (TT.Apply (p, TT.Succ (TT.Bound 1)))
           ))
        ))
     ) &&
     expr ctx a4 b4 TT.ty_Nat

  | TT.Empty, TT.Empty -> true
  | TT.IndEmpty (a1, a2), TT.IndEmpty (b1, b2) ->
     expr ctx a1 b1 (TT.Ty (TT.Prod ((Name.anonymous (), TT.Ty (TT.Empty)), TT.ty_Type))) &&
     expr ctx a2 b2 (TT.Ty TT.Empty)

  | TT.Identity (at, a1, a2), TT.Identity (bt, b1, b2) ->
     ty ctx at bt &&
     expr ctx a1 b1 at &&
     expr ctx a2 b2 at
  | TT.Refl (t1, e1), TT.Refl (t2, e2) ->
     ty ctx t1 t2 &&
     expr ctx e1 e2 t1
  | TT.IndId (t1, c1, d1, a1, b1, p1), TT.IndId (t2, c2, d2, a2, b2, p2) ->
     ty ctx t1 t2 &&
     expr ctx a1 a2 t1 &&
     expr ctx b1 b2 t1 &&
     let t = t1 and a = a1 and b = b1 in
     expr ctx p1 p2 (TT.Ty (TT.Identity (t, a, b))) &&
     let t = t1 in
     expr ctx c1 c2 (
        TT.Ty (TT.Prod ((Name.Ident ("x", Name.Word), t),
           TT.Ty (TT.Prod ((Name.Ident ("y", Name.Word), TT.shift_ty 1 t),
              TT.Ty (TT.Prod ((Name.Ident ("p", Name.Word), TT.Ty (TT.Identity (TT.shift_ty 2 t, TT.Bound 1, TT.Bound 0))),
                 TT.ty_Type
              ))
           ))
        ))
     ) &&
     let t = t1 and c = c1 in
     expr ctx d1 d2 (
       TT.Ty (TT.Prod ((Name.Ident ("x", Name.Word), t), TT.Ty (
          TT.Apply (
             TT.Apply (
                TT.Apply (
                   TT.shift 1 c,
                   TT.Bound 0
                ),
                TT.Bound 0
             ),
             TT.Refl (TT.shift_ty 1 t, TT.Bound 0)
          )
       )))
     )
  | (TT.Type | TT.Bound _ | TT.Atom _ | TT.Prod _ | TT.Lambda _ | TT.Apply _ |
     TT.Nat | TT.Zero | TT.Succ _ | TT.IndNat _ | TT.Empty | TT.IndEmpty _ | TT.Identity _ | TT.Refl _ | TT.IndId _), _ ->
    false

(** Compare two types. *)
and ty ctx (TT.Ty ty1) (TT.Ty ty2) =
  expr ctx ty1 ty2 TT.ty_Type

(** Compare two spines of equal lengths.

    A spine is a nested application of the form [a e1 e2 ... en]
    where [a] is an atom.
*)
and spine ctx (a1, sp1) (a2, sp2) =
  a1 = a2 &&
  begin
    let rec fold ty sp1 sp2 =
      match as_prod ctx ty with
      | None -> assert false
      | Some ((x, t), u) ->
        begin
          match sp1, sp2 with
          | [e1], [e2] -> expr ctx e1 e2 t
          | e1 :: sp1, e2 :: sp2 ->
            expr ctx e1 e2 t &&
            begin
              let u = TT.instantiate_ty e1 u in
              fold u sp1 sp2
            end
          | _, _ ->
            (* We should never be here, as the lengths of the spines should match. *)
            assert false
        end
    in
    match Context.lookup_atom_ty a1 ctx with
    | None -> assert false
    | Some ty -> fold ty sp1 sp2
  end
