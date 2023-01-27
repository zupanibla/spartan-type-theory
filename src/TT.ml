(** {1 Spartan type theory} *)

(** De Bruijn index. *)
type index = int

(** An atom is a primitive symbol. We tag atom names with integers so that
    it is easy to generate fresh ones. *)
type atom = Name.ident * int

(** Expression *)
type expr =
  | Bound of index (** de Bruijn index *)
  | Atom of atom (** primitive symbol *)
  | Type (** the type of types *)
  | Prod of (Name.ident * ty) * ty (** dependent product *)
  | Lambda of (Name.ident * ty) * expr (** lambda abstraction *)
  | Apply of expr * expr (** application *)
  | Nat (** the type of natural numbers *)
  | Zero (** the natural number zero *)
  | Succ of expr (** successor of a natural number *)
  | IndNat of expr * expr * expr * expr (** induction on natural numbers *)
  | Empty (** the empty type **)
  | IndEmpty of expr * expr (** induction on the empty type **)
  | Identity of ty * expr * expr (** the identity type **)
  | Refl of ty * expr (** constructor of the identity type **)
  | IndId of ty * expr * expr * expr * expr * expr (** induction on the identity type *)

(** Type *)
and ty = Ty of expr

(** {2 Support for bound variables and atoms.} *)

let atom_name (x, _) = x

(** Create a fresh atom from an identifier. *)
let new_atom : Name.ident -> atom =
  let k = ref (-1) in
  fun x -> incr k ; (x, !k)

(** [Type] as a type. *)
let ty_Type = Ty Type

(** [Nat] as a type. *)
let ty_Nat = Ty Nat

(** [instantiate ~lvl:k e e'] instantiates deBruijn index [k] with [e] in expression [e']. *)
let rec instantiate ?(lvl=0) e e' =
  match e' with

  | Bound j ->
     if j = lvl then e else e'

  | Atom _ -> e'

  | Type -> e'

  | Prod ((x, t), u) ->
     let t = instantiate_ty ~lvl e t
     and u = instantiate_ty ~lvl:(lvl+1) e u in
     Prod ((x, t), u)

  | Lambda ((x, t), e2) ->
     let t = instantiate_ty ~lvl e t
     and e2 = instantiate ~lvl:(lvl+1) e e2 in
     Lambda ((x, t), e2)

  | Apply (e1, e2) ->
     let e1 = instantiate ~lvl e e1
     and e2 = instantiate ~lvl e e2 in
     Apply (e1, e2)

  | Nat     -> e'
  | Zero    -> e'
  | Succ e1 -> Succ (instantiate ~lvl e e1)
  | IndNat (e1, e2, e3, e4) ->
     let e1 = instantiate ~lvl e e1
     and e2 = instantiate ~lvl e e2
     and e3 = instantiate ~lvl e e3
     and e4 = instantiate ~lvl e e4 in
     IndNat (e1, e2, e3, e4)

  | Empty -> e'
  | IndEmpty (e1, e2) -> IndEmpty (instantiate ~lvl e e1, instantiate ~lvl e e2)


  | Identity (t, e1, e2) ->
     let t  = instantiate_ty ~lvl e t
     and e1 = instantiate ~lvl e e1
     and e2 = instantiate ~lvl e e2 in
     Identity (t, e1, e2)
  | Refl (t, e1) ->
     let t  = instantiate_ty ~lvl e t
     and e1 = instantiate ~lvl e e1 in
     Refl (t, e1)
  | IndId (t, e1, e2, e3, e4, e5) ->
     let t  = instantiate_ty ~lvl e t
     and e1 = instantiate ~lvl e e1
     and e2 = instantiate ~lvl e e2
     and e3 = instantiate ~lvl e e3
     and e4 = instantiate ~lvl e e4
     and e5 = instantiate ~lvl e e5 in
     IndId (t, e1, e2, e3, e4, e5)

(** [instantiate k e t] instantiates deBruijn index [k] with [e] in type [t]. *)
and instantiate_ty ?(lvl=0) e (Ty t) =
  let t = instantiate ~lvl e t in
  Ty t

(** [shift ~lvl k e] shifts bound variables above lvl by k in expression [e]. *)
let rec shift ?(lvl=0) k e =
  match e with
  | Bound j ->
     if j >= lvl then Bound (j + k) else Bound j

  | Atom y -> e

  | Type -> e

  | Prod ((y, t), u) ->
     let t = shift_ty ~lvl k t
     and u = shift_ty ~lvl:(lvl+1) k u in
     Prod ((y, t), u)

  | Lambda ((y, t), e) ->
     let t = shift_ty ~lvl k t
     and e = shift ~lvl:(lvl+1) k e in
     Lambda ((y, t), e)

  | Apply (e1, e2) ->
     let e1 = shift ~lvl k e1
     and e2 = shift ~lvl k e2 in
     Apply (e1, e2)

  | Nat     -> e
  | Zero    -> e
  | Succ e1 -> Succ (shift ~lvl k e1)
  | IndNat (e1, e2, e3, e4) ->
     let e1 = shift ~lvl k e1
     and e2 = shift ~lvl k e2
     and e3 = shift ~lvl k e3
     and e4 = shift ~lvl k e4 in
     IndNat (e1, e2, e3, e4)

  | Empty -> e
  | IndEmpty (e1, e2) -> IndEmpty (shift ~lvl k e1, shift ~lvl k e2)

  | Identity (t, e1, e2) ->
     let t  = shift_ty ~lvl k t
     and e1 = shift ~lvl k e1
     and e2 = shift ~lvl k e2 in
     Identity (t, e1, e2)

  | Refl (t, e1) ->
     let t  = shift_ty ~lvl k t
     and e1 = shift ~lvl k e1 in
     Refl (t, e1)

  | IndId (t, e1, e2, e3, e4, e5) ->
     let t  = shift_ty ~lvl k t
     and e1 = shift ~lvl k e1
     and e2 = shift ~lvl k e2
     and e3 = shift ~lvl k e3
     and e4 = shift ~lvl k e4
     and e5 = shift ~lvl k e5 in
     IndId (t, e1, e2, e3, e4, e5)

(** [shift_ty ~lvl k t] shifts atom [x] into bound index [lvl] in type [t]. *)
and shift_ty ?(lvl=0) k (Ty t) =
  let t = shift ~lvl k t in
  Ty t

(** [abstract ~lvl x e] abstracts atom [x] into bound index [lvl] in expression [e]. *)
let rec abstract ?(lvl=0) x e =
  match e with
  | Bound j -> Bound j

  | Atom y ->
     if x = y then Bound lvl else e

  | Type -> e

  | Prod ((y, t), u) ->
     let t = abstract_ty ~lvl x t
     and u = abstract_ty ~lvl:(lvl+1) x u in
     Prod ((y, t), u)

  | Lambda ((y, t), e) ->
     let t = abstract_ty ~lvl x t
     and e = abstract ~lvl:(lvl+1) x e in
     Lambda ((y, t), e)

  | Apply (e1, e2) ->
     let e1 = abstract ~lvl x e1
     and e2 = abstract ~lvl x e2 in
     Apply (e1, e2)

  | Nat     -> e
  | Zero    -> e
  | Succ e1 -> Succ (abstract ~lvl x e1)
  | IndNat (e1, e2, e3, e4) ->
     let e1 = abstract ~lvl x e1
     and e2 = abstract ~lvl x e2
     and e3 = abstract ~lvl x e3
     and e4 = abstract ~lvl x e4 in
     IndNat (e1, e2, e3, e4)

  | Empty -> e
  | IndEmpty (e1, e2) -> IndEmpty (abstract ~lvl x e1, abstract ~lvl x e2)

  | Identity (t, e1, e2) ->
     let t  = abstract_ty ~lvl x t
     and e1 = abstract ~lvl x e1
     and e2 = abstract ~lvl x e2 in
     Identity (t, e1, e2)
  | Refl (t, e1) ->
     let t  = abstract_ty ~lvl x t
     and e1 = abstract ~lvl x e1 in
     Refl (t, e1)
  | IndId (t, e1, e2, e3, e4, e5) ->
     let t  = abstract_ty ~lvl x t
     and e1 = abstract ~lvl x e1
     and e2 = abstract ~lvl x e2
     and e3 = abstract ~lvl x e3
     and e4 = abstract ~lvl x e4
     and e5 = abstract ~lvl x e5 in
     IndId (t, e1, e2, e3, e4, e5)

(** [abstract_ty ~lvl x t] abstracts atom [x] into bound index [lvl] in type [t]. *)
and abstract_ty ?(lvl=0) x (Ty t) =
  let t = abstract ~lvl x t in
  Ty t

(** [unabstract a e] instantiates de Bruijn index 0 with [a] in expression [e]. *)
let unabstract a e = instantiate (Atom a) e

(** [unabstract_ty a t] instantiates de Bruijn index 0 with [a] in type [t]. *)
let unabstract_ty a (Ty t) = Ty (instantiate (Atom a) t)

(** [occurs k e] returns [true] when de Bruijn index [k] occurs in expression [e]. *)
let rec occurs k = function
  | Bound j -> j = k
  | Atom _ -> false
  | Type -> false
  | Prod ((_, t), u) -> occurs_ty k t || occurs_ty (k+1) u
  | Lambda ((_, t), e) -> occurs_ty k t || occurs (k+1) e
  | Apply (e1, e2) -> occurs k e1 || occurs k e2
  | Nat     -> false
  | Zero    -> false
  | Succ e1 -> occurs k e1
  | IndNat (e1, e2, e3, e4) -> occurs k e1 || occurs k e2 || occurs k e3 || occurs k e4
  | Empty -> false
  | IndEmpty (e1, e2) -> occurs k e1 || occurs k e2
  | Identity (t, e1, e2) -> occurs_ty k t || occurs k e1 || occurs k e2
  | Refl (t, e1) -> occurs_ty k t || occurs k e1
  | IndId (t, e1, e2, e3, e4, e5) -> occurs_ty k t || occurs k e1 || occurs k e2 || occurs k e3 || occurs k e4 || occurs k e5

(** [occurs_ty k t] returns [true] when de Bruijn index [k] occurs in type [t]. *)
and occurs_ty k (Ty t) = occurs k t

(** {2 Printing routines} *)

let add_forbidden x forbidden = x :: forbidden

let print_binders ~penv print_u print_v xus ppf =
  Format.pp_open_hovbox ppf 2 ;
  let rec fold ~penv = function
    | [] -> penv
    | (x,u) :: xus ->
       let y = Name.refresh penv x in
       Print.print ppf "@;<1 -4>(%t : %t)"
                   (Name.print_ident y)
                   (print_u ~penv u) ;
       fold ~penv:(add_forbidden y penv) xus
  in
  let penv = fold ~penv xus in
  Print.print ppf ",@ %t" (print_v ~penv) ;
  Format.pp_close_box ppf ()

let print_lambda_binders ~penv print_u print_v xus ppf =
  Format.pp_open_hovbox ppf 2 ;
  let rec fold ~penv = function
    | [] -> penv
    | (x,u) :: xus ->
       let y = Name.refresh penv x in
       Print.print ppf "@;<1 -4>(%t : %t)"
                   (Name.print_ident y)
                   (print_u ~penv u) ;
       fold ~penv:(add_forbidden y penv) xus
  in
  let penv = fold ~penv xus in
  Print.print ppf " =>@ %t" (print_v ~penv) ;
  Format.pp_close_box ppf ()

let print_atom (x, _) ppf = Name.print_ident x ppf

let print_debruijn xs k ppf =
  let x = List.nth xs k in
  Name.print_ident x ppf

let rec print_expr ?max_level ~penv e ppf =
    print_expr' ~penv ?max_level e ppf


and print_expr' ~penv ?max_level e ppf =
    match e with
      | Type ->
        Format.fprintf ppf "Type"

      | Atom x ->
        print_atom x ppf

      | Bound k -> print_debruijn penv k ppf

      | Lambda ((x, t), e) -> print_lambda ?max_level ~penv ((x, t), e) ppf

      | Apply (e1, e2) -> print_app ?max_level ~penv e1 e2 ppf

      | Prod ((x, u), t) -> print_prod ?max_level ~penv ((x, u), t) ppf

      | Nat     -> Format.fprintf ppf "N"
      | Zero    -> Format.fprintf ppf "0"
      | Succ e1 -> print_succ ?max_level ~penv e 0 ppf

      | IndNat (e1, e2, e3, e4) -> Print.print ppf "ind(%t, %t, %t, %t)"
         (print_expr_with_parentheses_if_has_comma ?max_level ~penv e1)
         (print_expr_with_parentheses_if_has_comma ?max_level ~penv e2)
         (print_expr_with_parentheses_if_has_comma ?max_level ~penv e3)
         (print_expr_with_parentheses_if_has_comma ?max_level ~penv e4)

      | Empty -> Format.fprintf ppf "Empty"
      | IndEmpty (e1, e2) -> Print.print ppf "ind_empty(%t, %t)"
         (print_expr_with_parentheses_if_has_comma ?max_level ~penv e1)
         (print_expr_with_parentheses_if_has_comma ?max_level ~penv e2)

      | Identity (t, e1, e2) -> Print.print ?max_level ~at_level:Level.eq ppf "%t = %t"
         (print_expr ~max_level:Level.eq_left ~penv e1)
         (print_expr ~max_level:Level.eq_right ~penv e2)
      | Refl (t, e1) -> Print.print ppf ?max_level ~at_level:Level.app "refl@ %t"
         (print_expr ~max_level:Level.app_right ~penv e1)
      | IndId (t, e1, e2, e3, e4, e5) -> Print.print ppf "ind_id(%t, %t, %t)"
         (print_expr_with_parentheses_if_has_comma ?max_level ~penv e1)
         (print_expr_with_parentheses_if_has_comma ?max_level ~penv e2)
         (print_expr_with_parentheses_if_has_comma ?max_level ~penv e5)

and print_ty ?max_level ~penv (Ty t) ppf = print_expr ?max_level ~penv t ppf

(** [print_app e1 e2 ppf] prints the application [e1 e2] using formatter [ppf],
    possibly as a prefix or infix operator. *)
and print_app ?max_level ~penv e1 e2 ppf =
  let e1_prefix =
    match e1 with
    | Bound k ->
       begin
         match List.nth penv k with
         | Name.Ident (_, Name.Prefix) as op -> Some op
         | Name.Ident (_, _) -> None
         | exception Failure failure when failure = "nth" -> None
       end
    | Atom (Name.Ident (_, Name.Prefix) as op, _) -> Some op
    | _ -> None
  in
  match e1_prefix with
  | Some op ->
     Print.print ppf ?max_level ~at_level:Level.prefix "%t@ %t"
                 (Name.print_ident ~parentheses:false op)
                 (print_expr ~max_level:Level.prefix_arg ~penv e2)

  | None ->
     (* Infix or ordinary application. *)
     begin
       let e1_infix =
         begin
           match e1 with
           | Apply (Bound k, e1) ->
              begin
                match List.nth penv k with
                | Name.Ident (_, Name.Infix fixity) as op ->
                   Some (op, fixity, e1)
                | Name.Ident (_, (Name.Word | Name.Anonymous _| Name.Prefix)) -> None
                | exception Failure failure when failure = "nth" -> None
              end
           | Apply (Atom (Name.Ident (_, Name.Infix fixity) as op, _), e1) ->
              Some (op, fixity, e1)

           | _ -> None
         end
       in
       match e1_infix with
       | Some (op, fixity, e1) ->
          let (lvl_op, lvl_left, lvl_right) = Level.infix fixity in
          Print.print ppf ?max_level ~at_level:lvl_op "%t@ %t@ %t"
                      (print_expr ~max_level:lvl_left ~penv e1)
                      (Name.print_ident ~parentheses:false op)
                      (print_expr ~max_level:lvl_right ~penv e2)
       | None ->
          (* ordinary application *)
          Print.print ppf ?max_level ~at_level:Level.app "%t@ %t"
                       (print_expr ~max_level:Level.app_left ~penv e1)
                       (print_expr ~max_level:Level.app_right ~penv e2)
     end


(** [print_lambda a e t ppf] prints a lambda abstraction using formatter [ppf]. *)
and print_lambda ?max_level ~penv ((x, u), e) ppf =
  let x = (if not (occurs 0 e) then Name.anonymous () else x) in
  let rec collect xus e =
    match e with
    | Lambda ((x, u), e) ->
       let x = (if not (occurs 0 e) then Name.anonymous () else x) in
       collect ((x, u) :: xus) e
    | _ ->
       (List.rev xus, e)
  in
  let xus, e = collect [(x,u)] e in
  Print.print ?max_level ~at_level:Level.binder ppf "%s%t"
    (Print.char_lambda ())
    (print_lambda_binders ~penv
                   (print_ty ~max_level:Level.ascription)
                   (fun ~penv -> print_expr ~max_level:Level.in_binder ~penv e)
                   xus)

(** [print_prod ((x, u), t) ppf] prints the given product using formatter [ppf]. *)
and print_prod ?max_level ~penv ((x, u), t) ppf =
  if not (occurs_ty 0 t) then
    Print.print ?max_level ~at_level:Level.arr ppf "@[<hov>%t@ %s@ %t@]"
          (print_ty ~max_level:Level.arr_left ~penv u)
          (Print.char_arrow ())
          (print_ty ~max_level:Level.arr_right ~penv:(add_forbidden (Name.anonymous ()) penv) t)
  else
    let rec collect xus ((Ty t) as t_ty) =
      match t with
      | Prod ((x, u), t_ty) when occurs_ty 0 t_ty ->
         collect ((x, u) :: xus) t_ty
      | _ ->
         (List.rev xus, t_ty)
    in
    let xus, t = collect [(x,u)] t in
    Print.print ?max_level ~at_level:Level.binder ppf "%s%t"
                (Print.char_prod ())
                (print_binders ~penv
                               (print_ty ~max_level:Level.ascription)
                               (fun ~penv -> print_ty ~max_level:Level.in_binder ~penv t)
                               xus)

and print_succ ?max_level ~penv e depth ppf =
  match e with
    | Zero    -> Print.print ppf "%d" depth
    | Succ e1 -> print_succ ?max_level ~penv e1 (depth+1) ppf
    | e1      -> wrap_in_n_succs ?max_level ~penv e depth ppf

and wrap_in_n_succs ?max_level ~penv e n ppf =
  match n with
    | 0 -> print_expr ~max_level:Level.app_right ~penv e ppf
    | n -> Print.print ppf ?max_level ~at_level:Level.app "succ@ %t" (wrap_in_n_succs ~max_level:Level.app_right ~penv e (n-1))

and print_expr_with_parentheses_if_has_comma ?max_level ~penv e ppf = (* TODO there is a better way to do this *)
  match e with
    | Prod _
    | Lambda _
    -> Print.print ppf "(%t)" (print_expr ?max_level ~penv e)
    | _ ->  print_expr ?max_level ~penv e ppf
