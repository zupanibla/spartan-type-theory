(** {1 Spartan type theory} *)

(** De Bruijn index *)
type index = int

(** An atom is a primitive symbol. *)
type atom

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

(** [Type] as a type. *)
val ty_Type : ty

(** [Nat] as a type. *)
val ty_Nat : ty

(** The name of an atom *)
val atom_name : atom -> Name.ident

(** Print a TT expression *)
val print_expr : ?max_level:Level.t -> penv:Name.ident list -> expr -> Format.formatter -> unit

(** Print a TT type *)
val print_ty : ?max_level:Level.t -> penv:Name.ident list -> ty -> Format.formatter -> unit

(** Create a fresh atom from an identifier. *)
val new_atom : Name.ident -> atom

(** [shift ~lvl k e] shifts bound variables above [lvl] by [k] in [e]. *)
val shift : ?lvl:index -> int -> expr -> expr

(** [shift_ty ~lvl k ty] shifts bound variables above [lvl] by [k] in [ty]. *)
val shift_ty : ?lvl:index -> int -> ty -> ty

(** [abstract x e] abstracts atom [x] into bound index [0] in expression [e], or
   into index [lvl] if given. *)
val abstract : ?lvl:index -> atom -> expr -> expr

(** [abstract_ty x t] abstracts atom [x] into bound index [0] in type [t], or
   into index [lvl] if given. *)
val abstract_ty : ?lvl:index -> atom -> ty -> ty

(** [unabstract a e] instantiates de Bruijn index 0 with [a] in expression [e]. *)
val unabstract : atom -> expr -> expr

(** [unabstract_ty a t] instantiates de Bruijn index 0 with [a] in type [t]. *)
val unabstract_ty : atom -> ty -> ty

(** [instantiate ~lvl:k e e'] instantiates deBruijn index [k] with [e] in expression [e']. *)
val instantiate : ?lvl:index -> expr -> expr -> expr

(** [instantiate_ty ~lvl:k e t] instantiates deBruijn index [k] with [e] in type [t]. *)
val instantiate_ty : ?lvl:index -> expr -> ty -> ty
