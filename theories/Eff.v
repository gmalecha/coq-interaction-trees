Section Eff.
  Variable eff : Type -> Type.

  Inductive EffF (Eff : Type) (T : Type) : Type :=
  | retF (_ : T)
  | interactF {A} (_ : eff A) (_ : A -> Eff)
  | delayF (_ : Eff).

  Arguments retF {_ _} _.
  Arguments interactF {_ _ _} _ _.
  Arguments delayF {_ _} _.

  CoInductive Eff (T : Type) : Type :=
  | do (_ : EffF (Eff T) T).

  Arguments do {_} _.

  Definition getEff {T} (x : Eff T) : EffF (Eff T) T :=
    match x with
    | do y => y
    end.

  Definition ret {T} (x : T) : Eff T :=
    do (retF x).

  Definition interact {T U} (x : eff T) (k : T -> Eff U) : Eff U :=
    do (interactF x k).

  Definition delay {T} (x : Eff T)  : Eff T :=
    do (delayF x).

  Theorem getEff_eq : forall {T} (x : Eff T),
      x = match getEff x with
          | retF v => ret v
          | interactF e k => interact e k
          | delayF k => delay k
          end.
  Proof.
    destruct x; destruct e; reflexivity.
  Defined.

  Section bind.
    Context {A B : Type} (k : A -> Eff B).

    CoFixpoint bind' (f : Eff A) : Eff B :=
      match getEff f with
      | retF x => k x
      | interactF io k' => interact io (fun x => bind' (k' x))
      | delayF f => delay (bind' f)
      end.
  End bind.

  Definition bind {A B} (f : Eff A) (k : A -> Eff B) : Eff B :=
    bind' k f.

  (* I should use paco to define this *)
  CoInductive Eff_eq {T} : Eff T -> Eff T -> Prop :=
  | eq_ret : forall t, Eff_eq (ret t) (ret t)
  | eq_interact : forall a (e : eff a) k1 k2,
      (forall x, Eff_eq (k1 x) (k2 x)) ->
      Eff_eq (interact e k1) (interact e k2)
  | eq_delay : forall a b, Eff_eq a b ->
                      Eff_eq (delay a) (delay b).

  CoInductive Eff_sim {T} : Eff T -> Eff T -> Prop :=
  | sim_ret : forall t, Eff_sim (ret t) (ret t)
  | sim_interact : forall a (e : eff a) k1 k2,
      (forall x, Eff_sim (k1 x) (k2 x)) ->
      Eff_sim (interact e k1) (interact e k2)
  | sim_delay : forall a b, Eff_sim a b ->
                       Eff_sim (delay a) (delay b).

End Eff.


Arguments bind {_ _ _} _ _.
Arguments bind' {_ _ _} _ _.
Arguments interactF {_ _ _ _} _ _.
Arguments interact {_ _ _} _ _.
Arguments retF {_ _ _} _.
Arguments ret {_ _} _.
Arguments delayF {_ _ _} _.
Arguments delay {_ _} _.
Arguments getEff {_ _} _.

(** Interpretation of effects *)

Section interp.

  Context {eff eff' : Type -> Type}.

  Variable do : forall {T}, eff T -> Eff eff' T.

  CoFixpoint interp {T} (c : Eff eff T) : Eff eff' T :=
    match getEff c with
    | retF x => ret x
    | interactF e k =>
      match getEff (do _ e) with
      | retF v => delay (interp (k v))
      | interactF e k' =>
        interact e (fun x => bind (k' x) (fun y => interp (k y)))
      | delayF v => delay (@bind' _ _ _ (fun x => interp (k x)) v)
      end
    | delayF x => delay (interp x)
    end.



  Lemma interp_ret : forall {T} (v : T),
      interp (ret v) = ret v.
  Proof.
    intros.
    rewrite getEff_eq.
    rewrite (getEff_eq _ (interp (ret v))).
    reflexivity.
  Defined.

  (* This doesn't preserve stuttering *)
  Lemma interp_interact : forall {a b} (e : eff a) (k : a -> Eff eff b),
      interp (interact e k) =
      bind (do _ e) (fun x => interp (k x)).
  Proof.
    intros.
    rewrite getEff_eq. symmetry. rewrite getEff_eq. symmetry.
    simpl.
    destruct (getEff (do a e)); simpl.
    { admit. }
    { reflexivity. }
    { reflexivity. }
  Admitted.

  Lemma interp_delay : forall {a} (k : Eff eff a),
      interp (delay k) = delay (interp k).
  Proof.
    intros.
    rewrite getEff_eq. symmetry. rewrite getEff_eq. symmetry.
    reflexivity.
  Defined.

End interp.

(** Effects **)

(* union of effects *)
Section bothE.
  Context {f g : Type -> Type}.
  Inductive both (T : Type) : Type :=
  | bleft : f T -> both T
  | bright : g T -> both T.
End bothE.

Arguments both _ _ _ : clear implicits.
Arguments bleft {_ _ _} _.
Arguments bright {_ _ _} _.

Section inj.

  Variable eff eff' : Type -> Type.

  CoFixpoint injL {T} (c : Eff eff T) : Eff (both eff eff') T :=
    match getEff c with
    | retF x => ret x
    | interactF e k => interact (bleft e) (fun x => injL (k x))
    | delayF x => delay (injL x)
    end.

  CoFixpoint injR {T} (c : Eff eff' T) : Eff (both eff eff') T :=
    match getEff c with
    | retF x => ret x
    | interactF e k => interact (bright e) (fun x => injR (k x))
    | delayF x => delay (injR x)
    end.

End inj.

Arguments injL {_} _ {_} _.
Arguments injR {_ _} _ _.

(* the fixpoint effect *)
Section Fix.

  Variable a : Type.

  Inductive fixpoint : Type -> Type :=
  | rec : fixpoint a.

  Variable eff : Type -> Type.

  (** Begin a bunch of variants to try to implement mfix *)

  Section mfix.
    Variable f : Eff (both eff fixpoint) a.

    CoFixpoint finterp_then
           {T b : Type} (k' : T -> Eff eff b)
               (c : Eff (both eff fixpoint) T) : Eff eff b :=
      match getEff c with
      | retF x => delay (k' x)
      | interactF (bleft e) k =>
        interact e (fun x => finterp_then k' (k x))
      | interactF (bright e) k =>
        delay (finterp_then k' (bind' (fun x => k match e with
                                        | rec => x
                                        end) f))
      | delayF x => delay (finterp_then k' x)
      end.

    Definition mfix : Eff eff a := finterp_then ret f.
  End mfix.

  Definition go (mfix : Eff eff a)
    T (X : both eff fixpoint T) : Eff eff T :=
    match X with
    | bleft e => interact e ret
    | bright f0 =>
      match f0 with
      | rec => mfix
      end
    end.

  Theorem mfix_unfold : forall f,
      mfix f = interp (go (mfix f)) f.
  Proof. Admitted.

  Theorem mfix_ret : forall v, mfix (ret v) = ret v.
  Proof. Admitted.

End Fix.

Arguments mfix {_} _.

(* the state effect *)
Section stateE.
  Variable s : Type.
  Inductive state : Type -> Type :=
  | Get : state s
  | Put : s -> state unit.

End stateE.

Arguments Get {_}.
Arguments Put {_} _.

(* the empty effect *)
Section nothingE.
  Inductive nothing : Type -> Type := .
End nothingE.

(** Testing *)
Definition trial : Eff nothing False :=
  mfix nothing (interact (bright (rec False)) ret).

Section diverge.
  Context {eff : Type -> Type}.
  Variable t : Type.
  CoFixpoint diverge : Eff eff t :=
    delay diverge.

  Theorem diverge_eq : diverge = delay diverge.
  Proof. symmetry. rewrite getEff_eq. reflexivity. Defined.

End diverge.

Require Import Setoid.

Goal Eff_eq _ trial (diverge _).
  cofix rec.
  unfold trial.
  rewrite mfix_unfold.
  rewrite interp_interact. simpl go.
  rewrite mfix_unfold. rewrite interp_interact.
  Eval compute in fun f => getEff (mfix nothing f ret).

  rewrite (getEff_eq _ (interp (go _ _ _) _)).


  simpl.
  rewrite (getEff_eq _ (diverge False)). simpl.


Admitted.