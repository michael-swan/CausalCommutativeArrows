Require Import Coq.Program.Basics. (* compose *)
Require Import Coq.Setoids.Setoid. (* rewrite ... at ... *)
Require Import Coq.Logic.FunctionalExtensionality. (* functional_extensionality *)
Require Import Coq.Init.Datatypes. (* id *)

(** Definition of Arrow *)
Inductive Arrow : Type -> Type -> Prop :=
    | arr : forall {b c : Type}, (b -> c) -> Arrow b c
    | compose_arrow : forall {c : Type} {b d : Type}, Arrow b c -> Arrow c d -> Arrow b d
    | first : forall {d : Type} {b c : Type}, Arrow b c -> Arrow (b*d) (c*d)
    | loop : forall {d : Type} {b c : Type}, Arrow (b * d) (c * d) -> Arrow b c
    | init : forall {i : Type}, i -> Arrow i i.

Notation "A >>> B" := (compose_arrow A B)
                      (at level 60, right associativity).

(** Arrow Law Helper Functions *)
Definition fun_product {A B C D} (f : A -> C) (g : B -> D) : (A * B) -> (C * D) :=
  fun tup => match tup with (a, b) => (f a, g b) end.

Notation "f <x> g" := (fun_product f g)
                      (at level 60, right associativity).

Definition assoc {A B C} : (A * B) * C -> A * (B * C) :=
  fun tup => match tup with (tup', c) => match tup' with (a, b) => (a, (b, c)) end end.

Definition assoc_inv {A B C} : A * (B * C) -> (A * B) * C :=
  fun tup => match tup with (a, tup') => match tup' with (b, c) => ((a, b), c) end end.

Definition swap {A B} : A * B -> B * A :=
  fun tup => match tup with (a, b) => (b, a) end.

Definition second {C A B} (f : Arrow A B) : Arrow (C * A) (C * B) :=
  arr swap >>> first f >>> arr swap.

(** Arrow Laws: An Arrow is defined as having these properties. If your mathematical
    structure lacks any of the below laws, it is _not_ a valid Arrow.
 *)
Axiom left_identity : forall (x y : Type) (f : Arrow x y),
  arr id >>> f = f.
Axiom right_identity : forall (x y : Type) (f : Arrow x y),
  f >>> arr id = f.
Axiom associativity : forall (w x y z : Type) (f : Arrow w x) (g : Arrow x y) (h : Arrow y z),
  (f >>> g) >>> h = f >>> (g >>> h).
Axiom composition : forall (A B C : Type) (g : B -> C) (f : A -> B),
  arr (compose g f) = arr f >>> arr g.
Axiom extension : forall (A B C : Type) (f : A -> B),
  @first C A B (arr f)  = arr (f <x> id).
Axiom functor : forall (A B C D : Type) (f : Arrow A B) (g : Arrow B C),
  @first D A C (f >>> g) = first f >>> first g.
Axiom exchange : forall (A B C D : Type) (f : Arrow A B) (g : C -> D),
  first f >>> arr (id <x> g) = arr (id <x> g) >>> first f.
Axiom unit : forall (A B C : Type) (f : Arrow A B),
  @first C A B f >>> arr fst = arr fst >>> f.
Axiom association : forall (A B C D : Type) (f : Arrow A B),
  @first D _ _ (@first C _ _ f) >>> arr assoc = arr assoc >>> first f.

(** Derivative Arrow Laws: These are the [second] analogs to some of the  *)
Theorem functor_second : forall (A B C D : Type) (f : Arrow A B) (g : Arrow B C),
  @second D A C (f >>> g) = second f >>> second g.
Proof.
  intros.
  unfold second.
  repeat rewrite -> associativity.
  rewrite <- (associativity _ _ _ _ (arr swap) (arr swap)).
  rewrite <- composition.
  assert (H: forall A B, id = compose swap (@swap A B)).
  { intros.
    unfold id, compose, swap.
    apply functional_extensionality.
    intros [a b].
    reflexivity.
  }
  rewrite <- H; clear H.
  rewrite -> left_identity.
  rewrite -> functor.
  rewrite -> associativity.
  reflexivity.
Qed.

Theorem extension_second : forall (A B C : Type) (f : A -> B),
  @second C A B (arr f)  = arr (id <x> f).
Proof.
  intros.
  unfold second.
  rewrite -> extension.
  repeat rewrite <- composition.
  assert (H: forall A B C (f : A -> B), compose (compose (@swap B C) (f <x> id)) swap = id <x> f).
  { intros.
    unfold compose.
    apply functional_extensionality.
    intros [c a].
    unfold swap, fun_product, id.
    reflexivity.
  }
  rewrite -> H; clear H.
  reflexivity.
Qed.

(** Arrow Loop Laws *)
Axiom left_tightening_loop : forall (A B C D : Type) (f : Arrow (B * D) (C * D)) (h : Arrow A B),
  loop (first h >>> f) = h >>> loop f.
Axiom right_tightening_loop : forall (A B C D : Type) (f : Arrow (A * D) (B * D)) (h : Arrow B C),
  loop (f >>> first h) = loop f >>> h.
Axiom sliding_loop : forall (A B C D : Type) (f : Arrow (A * D) (B * C)) (k : C -> D),
  loop (f >>> arr (id <x> k)) = loop (arr (id <x> k) >>> f).
Axiom vanishing_loop : forall (A B C D : Type) (f : Arrow ((A * C) * D) ((B * C) * D)),
  loop (loop f) = loop (arr assoc_inv >>> f >>> arr assoc).
Axiom superposing_loop : forall (A B C D : Type) (f : Arrow (A * C) (B * C)),
  @second D A B (loop f) = loop (arr assoc >>> second f >>> arr assoc_inv).

(** CCA Laws: These additional restrictions allow for proof of the CCA optimization
    such that any arrow with this restriction can be refactored into an arrow of the
    form [loopD i f].
 *)
Axiom product_init : forall A B (i : A) (j : B),
  first (init i) >>> second (init j) = init (i, j).
Axiom commutativity : forall A B C D (f : Arrow A B) (g : Arrow C D),
  first f >>> second g = second g >>> first f.

(* Helper Functions (i.e. useful for intermediate steps of the proof) *)

Definition assoc' {A B C D E F} (f : (A * B) * C -> (D * E) * F) : A * (B * C) -> D * (E * F) :=
  compose assoc (compose f assoc_inv).

Definition juggle {A B C} : (A * B) * C -> (A * C) * B :=
  fun tup => match tup with (tup', c) => match tup' with (a, b) => ((a, c), b) end end.

Definition revjuggle {A B C} : A * (B * C) -> B * (A * C) :=
  fun tup => match tup with (a, tup') => match tup' with (b, c) => (b, (a, c)) end end.

Definition juggle' {A B C D E F} (f : (A * B) * C -> (D * E) * F) : (A * C) * B -> (D * F) * E :=
  compose juggle (compose f juggle).

Definition loopD {A B C} (i : C) (f : (A * C) -> (B * C)) : Arrow A B :=
  loop (arr f >>> second (init i)).

(* Preliminary Lemmas*)

Lemma identity_assoc : forall A B C,
  id = compose assoc_inv (@assoc A B C).
Proof.
  intros.
  apply functional_extensionality.
  intros [[a b] c].
  unfold compose, assoc, assoc_inv, id.
  reflexivity.
Qed.

Lemma compose_assoc : forall A B C D (f : C -> D) (g : B -> C) (h : A -> B),
  compose (compose f g) h = compose f (compose g h).
Proof.
  unfold compose;
  reflexivity.
Qed.

(** CCA Lemmas *)

(** Lemma 10.1 *)
Lemma second_juggle : forall (A B C D : Type) (f : Arrow A B),
  @second D _ _ (@second C _ _ f) = arr revjuggle >>> second (second f) >>> arr revjuggle.
Proof.
  intros.
  (* LHS *)
  (* definition of second *)
  unfold second at 1 2.
  (* functor of first, extension of first *)
  repeat rewrite functor;
  repeat rewrite extension;
  repeat rewrite -> associativity.
  (* identity of arr, id = assoc−1 . assoc, and composition of arr *)
  rewrite <- (right_identity _ _ (first (first f)));
  rewrite -> identity_assoc;
  rewrite -> composition;
  repeat rewrite -> associativity.
  (* association of first *)
  rewrite <- (associativity _ _ _ _ (first (first f)));
  rewrite -> (association _ _ _ _ f);
    repeat rewrite -> associativity.
  (* composition of arr *)
  repeat rewrite <- composition;
  repeat rewrite <- associativity;
  repeat rewrite <- composition;
  repeat rewrite -> associativity;
  repeat rewrite -> compose_assoc.
  (* unfold function definition and beta reduce *)
    (* See End *)
  (* RHS *)
  (* definition of second *)
  unfold second at 1 2;
  repeat rewrite -> associativity.
  (* functor of first, extension of first *)
  repeat rewrite -> functor, extension, associativity.
  (* identity of arr, id = assoc−1 . assoc, and composition of arr *)
  rewrite <- (right_identity _ _ (first (first f)));
  rewrite -> identity_assoc;
  rewrite -> (composition _ _ _ assoc_inv);
  repeat rewrite -> associativity.
  (* association of first *)
  rewrite <- (associativity _ _ _ _ (first (first f)));
  rewrite -> association;
  rewrite -> associativity.
  (* composition of arr *)
  do 3 rewrite <- composition;
  repeat rewrite <- associativity;
  do 3 rewrite <- composition;
  repeat rewrite -> associativity.

  (* unfold function definition and beta reduce *)
  assert (H0: forall D C A,
               compose 	assoc (compose (swap <x> id) swap) =
                 (fun x : D * (C * A) => match x with (a, (b, c)) => (c, (b, a)) end)).
  { intros.
    unfold compose.
    apply functional_extensionality.
    intros [a [b c]].
    unfold swap, id, fun_product, assoc.
    reflexivity.
  }
  assert (H1: forall D C A,
               compose assoc (compose (swap <x> id) (compose swap revjuggle)) =
                 (fun x : D * (C * A) => match x with (a, (b, c)) => (c, (a, b)) end)).
  { intros.
    unfold compose.
    apply functional_extensionality.
    intros [d [c a]].
    unfold revjuggle, fun_product, id, swap, assoc.
    reflexivity.
  }
  assert (H2: forall A B C,
               compose swap (compose (swap <x> id) assoc_inv) =
                 (fun x : C * (A * B) => match x with (c, (a, b)) => (b, (a, c)) end)).
  { intros.
    unfold compose.
    apply functional_extensionality.
    intros [c [a b]].
    unfold swap, id, fun_product, assoc_inv.
    reflexivity.
  }
  assert (H3: forall A B C,
               compose (compose (compose revjuggle swap) (swap <x> id)) assoc_inv =
                 (fun x : C * (A * B) => match x with (c, (a, b)) => (a, (b, c)) end)).
  { intros.
    unfold compose.
    apply functional_extensionality.
    intros [a [b c]].
    unfold swap, id, fun_product, revjuggle, assoc_inv.
    reflexivity.
  }
  rewrite -> H0, H1, H2, H3; clear H0; clear H1; clear H2; clear H3.
Admitted.

Lemma second_commute : forall (A B C D : Type) (f : Arrow A B),
  @second C _ _ (@first D _ _ f) >>> arr (compose assoc swap) = arr (compose assoc swap) >>> first f.
Admitted.

Lemma first_juggle : forall (A B C D : Type) (f : Arrow A B),
  first f = arr revjuggle >>> @second C _ _ (@first D _ _ f) >>> arr revjuggle.
Admitted.

Lemma first_eq_second : forall (A B C : Type) (f : Arrow A B),
  @first C _ _ f = arr swap >>> second f >>> arr swap.
Admitted.

Theorem compose_fun_product : forall A B C D E F (f : A -> B) (g : C -> D) (h : B -> E) (i : D -> F),
  compose (h <x> i) (f <x> g) = compose h f <x> compose i g.
Proof.
  intros.
  unfold compose.
  unfold fun_product.
  simpl.
  apply functional_extensionality.
  intros [a b].
  reflexivity.
Qed.

Theorem compose_identity : forall A,
  @id A = compose id id.
Proof.
  intros.
  unfold compose.
  unfold id.
  reflexivity.
Qed.

Theorem double_swap_identity : forall A B,
  id = compose swap (@swap A B).
Proof.
  intros.
  unfold compose.
  unfold swap.
  unfold id.
  apply functional_extensionality.
  intros [a b].
  reflexivity.
Qed.

Theorem compose_simplify : forall A B C,
  compose (@swap (A * B) C) (@assoc_inv A B C) = compose assoc (compose (swap <x> id) (compose assoc_inv (id <x> swap))).
Proof.
  intros.
  unfold compose.
  apply functional_extensionality.
  intros [a [b c]].
  unfold swap.
  unfold fun_product.
  unfold id.
  reflexivity.
Qed.

Theorem assoc_juggle_eq : forall A B C D E (f : (A * D) -> (B * D)) (g : (B * E) -> (C * E)),
  assoc' (compose (juggle' (g <x> id)) (f <x> id)) =
     compose revjuggle
        (compose (id <x> g)
           (compose (compose assoc swap)
              (compose (id <x> compose swap f) (compose swap assoc_inv)))).
Proof.
  intros.
  unfold juggle', assoc'.
  unfold compose at 1 2 3 4 5.
  unfold compose at 1 2 3 4 5.
  apply functional_extensionality.
  intros [a [b c]].
  unfold compose at 2.
  unfold assoc_inv.
  unfold swap at 3.
  unfold fun_product at 4.
  unfold compose.
  unfold swap at 1.
  unfold fun_product at 2.
  induction (f (a, b)).
  unfold swap.
  unfold assoc at 2.
  unfold juggle at 2.
  unfold fun_product.
  destruct (g (a0, id c)).
  unfold juggle, assoc, revjuggle.
  reflexivity.
Qed.

(** CCA Single-Step Reductions: CCA's can be optimized into the form [loopD i f]. This is
    done by repeatedly performing the below transformations. In each case, the left-hand side
    is rewritten into the form on the right-hand side.
 *)

Theorem composition_loopD : forall A B C (f : A -> B) (g : B -> C),
  arr f >>> arr g = arr (compose g f).
Proof.
  intros;
  rewrite <- composition.
  reflexivity.
Qed.

Theorem left_tightening_loopD : forall A B C D (i : D) (f : A -> B) (g : (B * D) -> (C * D)),
  arr f >>> loopD i g = loopD i (compose g (f <x> id)).
Proof.
  intros.
  unfold loopD.
  rewrite <- left_tightening_loop.
  rewrite -> extension.
  rewrite -> composition.
  rewrite -> associativity.
  reflexivity.
Qed.

Theorem right_tightening_loopD : forall A B C D (i : D) (g : B -> C) (f : (A * D) -> (B * D)),
  loopD i f >>> arr g = loopD i (compose (g <x> id) f).
Proof.
  intros.
  unfold loopD.
  rewrite <- right_tightening_loop.
  rewrite -> associativity.
  rewrite <- commutativity.
  rewrite -> extension.
  rewrite -> composition.
  rewrite -> associativity.
  reflexivity.
Qed.

Theorem extension_loopD : forall A B C (f : A -> B),
  @first C _ _ (arr f) = arr (f <x> id).
Proof.
  intros;
  rewrite -> extension.
  reflexivity.
Qed.

Theorem superposing_loopD : forall A B C D (i : C) (f : (A * C) -> (B * C)),
  @first D _ _ (loopD i f) = loopD i (juggle' (f <x> id)).
Proof.
  intros.
  unfold loopD.
  rewrite -> first_eq_second.
  rewrite -> superposing_loop.
Admitted.

(** Loop-Extension and Vanishing theorems could not be implemented because the [trace]
    function couldn't be defined in Coq since it relies on laziness.
 *)

Theorem sequencing_loopD : forall (A B C D E : Type) (i : D) (f : (A * D) -> (B * D))
                                                   (j : E) (g : (B * E) -> (C * E)),
  loopD i f >>> loopD j g =
    loopD (i, j) (assoc' (compose (juggle' (g <x> (@id D))) (f <x> (@id E)))).
Proof.
  intros.
  (* definition of loopD *)
  unfold loopD at 1 2.
  (* left tightening of loop *)
  rewrite <- left_tightening_loop.
  (* definition of first *)
  (* NOTE: CCA states "definition of second" although that is a mistake. *)
  (* NOTE: second is defined in terms of first, so there is no definition of first *)
  rewrite -> first_eq_second.
  (* superposing of loop *)
  rewrite -> superposing_loop.
  repeat rewrite <- associativity at 1.
  (* left tightening of loop *)
  rewrite <- left_tightening_loop.
  (* associativity of >>> and extension of first *)
  repeat rewrite -> associativity.
  rewrite extension.
  (* right tightening of loop *)
  rewrite <- right_tightening_loop.
  (* vanishing of loop *)
  rewrite -> vanishing_loop.
  (* identity of arr, id = id × swap . id × swap, composition of arr *)
  assert (H: forall A B C, arr (@assoc_inv A B C) = arr id >>> arr assoc_inv).
  { intros. rewrite -> left_identity. reflexivity. }
  rewrite -> H; clear H.
  repeat rewrite -> associativity.
  assert (H: forall A B C, id = compose (@id A <x> @swap C B) (id <x> swap)).
  { intros.
    rewrite compose_fun_product.
    rewrite <- compose_identity.
    rewrite <- double_swap_identity.
    unfold fun_product.
    apply functional_extensionality.
    intros [a b]. reflexivity.
  }
  rewrite -> H; clear H.
  rewrite composition.
  repeat rewrite -> associativity.
  (* sliding of loop *)
  rewrite <- sliding_loop.
  (* composition of arr, swap . assoc_inv = assoc . (swap × id) . assoc_inv . (id × swap) *)
  repeat rewrite <- associativity.
  repeat rewrite <- composition.
  repeat rewrite -> associativity.
  rewrite <- compose_simplify.
  (* definition of second and definition of first *)
  rewrite -> first_eq_second.
  unfold second at 2.
  (* functor and extension of second *)
  repeat rewrite <- associativity.
  rewrite <- composition.
  repeat rewrite -> associativity.
  repeat rewrite -> functor_second.
  repeat rewrite -> associativity.
  repeat rewrite -> composition.
  rewrite <- composition.
  rewrite -> extension_second.
  rewrite <- composition.
  rewrite -> functor_second.
  rewrite -> extension_second.
  rewrite -> extension_second.
  rewrite <- extension_second.
  repeat rewrite -> associativity.
  (* Lemma 10.1 (i.e. second_juggle) *)
  rewrite -> second_juggle.
  repeat rewrite -> associativity.
  (* composition of arr, id = (id × swap) . assoc . swap . revjuggle, identity of arr *)
  assert (H: forall A B C, id = compose (compose (compose (@id A <x> @swap B C) assoc) swap) revjuggle).
  { intros.
    unfold compose, id, swap, fun_product, assoc, revjuggle.
    apply functional_extensionality.
    intros [a [b c]].
    reflexivity.
  }
  do 3 rewrite <- composition.
  rewrite <- H; clear H.
  rewrite -> right_identity.
  (* composition of arr, assoc . swap = (id × swap) . swap . assoc−1 . (id × swap) *)
  assert (H: forall A B C,
    compose (@assoc A B C) (@swap C (A * B)) = compose (id <x> swap) (compose swap (compose assoc_inv (id <x> swap)))).
  { intros.
    unfold compose, id, swap, fun_product, assoc, assoc_inv.
    apply functional_extensionality.
    intros [a [b c]].
    reflexivity.
  }
  rewrite <- (associativity _ _ _ _ (arr (id <x> swap))).
  rewrite <- composition.
  rewrite <- (associativity _ _ _ _ _ (arr swap)).
  rewrite <- composition.
  rewrite <- (associativity _ _ _ _ _ (arr (id <x> swap))).
  rewrite <- composition.
  rewrite <- H; clear H.
  (* Lemma 10.2 *)
  rewrite <- (associativity _ _ _ _ (second (first (init i)))).
  rewrite -> second_commute.
  repeat rewrite -> associativity.
  (* commutativity *)
  rewrite <- (associativity _ _ _ _ (first (init i))).
  rewrite -> commutativity.
  repeat rewrite -> associativity.
  (* Lemma 10.3 *)
  rewrite -> first_juggle.
  repeat rewrite -> associativity.
  (* composition of arr, id = revjuggle . revjuggle, identity of arr *)
  rewrite <- (associativity _ _ _ _ _ _ (second (second (init j)))).
  rewrite <- composition.
  assert (H: forall A B C, id = compose revjuggle (@revjuggle A B C)).
  { intros.
    unfold revjuggle, compose, id.
    apply functional_extensionality.
    intros [a [b c]].
    reflexivity.
  }
  rewrite <- H; clear H.
  rewrite -> left_identity.
  (* extension of second, composition of arr *)
  repeat rewrite -> extension_second.
  do 4 rewrite <- associativity.
  repeat rewrite <- composition.
  (* assoc' (juggle' (g × id) . (f × id)) =
       revjuggle . (id × g) . assoc . swap . id × (swap . f ) . swap . assoc−1 *)
  rewrite <- assoc_juggle_eq.
  rewrite <- functor_second.
  (* product of init *)
  rewrite -> product_init.
  (* Extra: Fold LHS into loopD *)
  fold (loopD (i, j) (assoc' (compose (juggle' (g <x> id)) (f <x> id)))).
  (* Complete *)
  reflexivity.
Qed.