(** Equality and normalization. *)

(** A normalization strategy. *)
type strategy =
  | WHNF (** normalize to weak head-normal form *)
  | CBV (** call-by-value normalization *)

(** Normalize an expression. *)
let rec norm_expr ~strategy ctx e =
  match e with
  | TT.Bound k -> e

  | TT.Type -> e

  | TT.Atom x ->
    begin
      match Context.lookup_def x ctx with
      | None -> e
      | Some e -> norm_expr ~strategy ctx e
    end

  | TT.Prod ((ident, t1), t2) ->
    let t1 = norm_ty ~strategy ctx t1
    and t2 = norm_ty ~strategy ctx t2 in
    TT.Prod ((ident, t1), t2)

  | TT.Lambda (param, body) ->
    begin
    match strategy with
      | WHNF -> e
      | CBV -> TT.Lambda (param, norm_expr ~strategy ctx body)
    end

  | TT.Apply (e1, e2) ->
    let e1 = norm_expr ~strategy ctx e1
    and e2 =
      begin
        match strategy with
        | WHNF -> e2
        | CBV -> norm_expr ~strategy ctx e2
      end
    in
    begin
      match e1 with
      | TT.Lambda (_, e') ->
        let e' = TT.instantiate e2 e' in
        norm_expr ~strategy ctx e'
      | _ -> TT.Apply (e1, e2)
    end

  | TT.Nat    -> e
  | TT.Zero   -> e
  | TT.Succ n -> TT.Succ (norm_expr ~strategy ctx n)
  | TT.IndNat (p, p0, ps, n) ->
     let n = norm_expr ~strategy ctx n in
     begin
       match n with
       | TT.Zero   -> norm_expr ~strategy ctx p0
       | TT.Succ m -> norm_expr ~strategy ctx (TT.Apply (TT.Apply (ps, m), TT.IndNat (p, p0, ps, m)))
       | _ -> TT.IndNat (
           norm_expr ~strategy ctx p,
           norm_expr ~strategy ctx p0,
           norm_expr ~strategy ctx ps,
           norm_expr ~strategy ctx n
         )
     end

  | TT.Empty -> e
  | TT.IndEmpty (p, e) -> TT.IndEmpty (
     norm_expr ~strategy ctx p,
     norm_expr ~strategy ctx e
  )

  | TT.PairType (t, p) ->
    let t = norm_ty ~strategy ctx t
    and p = norm_expr ~strategy ctx p in
    TT.PairType (t, p)

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
    | TT.PairType _
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
  | TT.Succ e1, TT.Succ e2 -> expr_whnf ctx e1 e2
  | TT.IndNat (a1, a2, a3, a4), TT.IndNat (b1, b2, b3, b4) ->
     expr_whnf ctx a1 b1 &&
     expr_whnf ctx a2 b2 &&
     expr_whnf ctx a3 b3 &&
     expr_whnf ctx a4 b4

  | TT.Empty, TT.Empty -> true
  | TT.IndEmpty (a1, a2), TT.IndEmpty (b1, b2) ->
     expr_whnf ctx a1 b1 &&
     expr_whnf ctx a2 b2

  | TT.PairType (t1, p1), TT.PairType (t2, p2)  ->
     ty ctx t1 t2 &&
     expr_whnf ctx p1 p2

  | (TT.Type | TT.Bound _ | TT.Atom _ | TT.Prod _ | TT.Lambda _ | TT.Apply _ | 
     TT.Nat | TT.Zero | TT.Succ _ | TT.IndNat _ | TT.Empty | TT.IndEmpty _ | TT.PairType _), _ ->
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
