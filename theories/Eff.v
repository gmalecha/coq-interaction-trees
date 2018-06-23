Set Universe Polymorphism.

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Setoid.

Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Fin.
Require Import Interaction.FinGet.

Section Eff.
  Polymorphic Universes u u'.
  Variable eff : Type@{u} -> Type@{u'}.

  Inductive EffF (Eff : Type@{u'}) (T : Type@{u}) : Type@{u'} :=
  | retF (_ : T)
  | interactF {A : Type@{u}} (_ : eff A) (_ : A -> Eff)
  | delayF (_ : Eff).

  Arguments retF {_ _} _.
  Arguments interactF {_ _ _} _ _.
  Arguments delayF {_ _} _.

  CoInductive Eff (T : Type@{u}) : Type@{u'} :=
  | do (_ : EffF (Eff T) T).

  Arguments do {_} _.

  Definition getEff {T : Type@{u}} (x : Eff T) : EffF (Eff T) T :=
    match x with
    | do y => y
    end.

  Definition ret {T : Type@{u}} (x : T) : Eff T :=
    do (retF x).

  Definition interact {T U : Type@{u}} (x : eff T) (k : T -> Eff U) : Eff U :=
    do (interactF x k).

  Definition delay {T : Type@{u}} (x : Eff T)  : Eff T :=
    do (delayF x).

  Theorem getEff_eq : forall {T : Type@{u}} (x : Eff T),
      x = match getEff x with
          | retF v => ret v
          | interactF e k => interact e k
          | delayF k => delay k
          end.
  Proof.
    destruct x; destruct e; reflexivity.
  Defined.

  Section bind.
    Context {A B : Type@{u}} (k : A -> Eff B).

    CoFixpoint bind' (f : Eff A) : Eff B :=
      match getEff f with
      | retF x => k x
      | interactF io k' => interact io (fun x => bind' (k' x))
      | delayF f => delay (bind' f)
      end.
  End bind.

  Definition bind {A B : Type@{u}} (f : Eff A) (k : A -> Eff B) : Eff B :=
    bind' k f.

  Definition delayBind {t u : Type@{u}} (e : Eff t) (k : t -> Eff u) : Eff u :=
    match getEff e with
    | retF v => delay (k v)
    | interactF e k' =>
      interact e (fun x => bind (k' x) k)
    | delayF v => delay (bind v k)
    end.

  Lemma bind_ret : forall {T U} (x : T) (k : T -> Eff U),
      bind (ret x) k = k x.
  Proof.
    intros. rewrite getEff_eq at 1. simpl.
    destruct (k x); destruct e; reflexivity.
  Defined.

  Lemma bind_delay : forall {T U} (x : Eff T) (k : T -> Eff U),
      bind (delay x) k = delay (bind x k).
  Proof.
    intros. rewrite getEff_eq at 1. simpl.
    reflexivity.
  Defined.

  Lemma bind_interactd : forall {T U V} (e : eff T) (k' : T -> Eff U) (k : U -> Eff V),
      bind (interact e k') k = interact e (fun x => bind (k' x) k).
  Proof.
    intros. rewrite getEff_eq at 1. simpl.
    reflexivity.
  Defined.

  Lemma delayBind_ret : forall {T U} v (k : T -> Eff U),
      delayBind (ret v) k = delay (k v).
  Proof.
    intros. rewrite getEff_eq at 1. reflexivity.
  Defined.

  Lemma delayBind_delay : forall {T U} (v : Eff T) (k : T -> Eff U),
      delayBind (delay v) k = delay (bind v k).
  Proof.
    intros. rewrite getEff_eq at 1. reflexivity.
  Defined.

  Lemma delayBind_interact : forall {T U V} e (k : T -> Eff U) (k' : U -> Eff V),
      delayBind (interact e k) k' = interact e (fun x => bind (k x) k').
  Proof.
    intros. rewrite getEff_eq at 1. reflexivity.
  Defined.

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

  Global Instance Reflexive_Eff_eq {T} : Reflexive (@Eff_eq T).
  Admitted.
  Global Instance Symmetric_Eff_eq {T} : Symmetric (@Eff_eq T).
  Admitted.
  Global Instance Transitive_Eff_eq {T} : Transitive (@Eff_eq T).
  Admitted.

  Global Instance Proper_Eff_eq_impl {T}
  : Proper (@Eff_eq T --> @Eff_eq T ==> Basics.impl) (@Eff_eq _).
  Proof. red. red. red. red. intros.
         etransitivity; [ apply H | ].
         etransitivity; [ eapply H1 | eapply H0 ].
  Defined.

  Global Instance Proper_Eff_eq_iff {T}
  : Proper (@Eff_eq T --> @Eff_eq T ==> iff) (@Eff_eq _).
  Proof. red. red. red. intros.
         split; eapply Proper_Eff_eq_impl;
           solve [ assumption | symmetry; assumption ].
  Defined.

  Global Instance Reflexive_Eff_sim {T} : Reflexive (@Eff_sim T).
  Admitted.
  Global Instance Symmetric_Eff_sim {T} : Symmetric (@Eff_sim T).
  Admitted.
  Global Instance Transitive_Eff_sim {T} : Transitive (@Eff_sim T).
  Admitted.

  Global Instance Subrelation_Eff_sim_Eff_eq {T}
  : subrelation (@Eff_eq T) (@Eff_sim T).
  Admitted.

  Global Instance Proper_bind' {T U}
  : Proper (pointwise_relation T (@Eff_eq U) ==> @Eff_eq T ==> (@Eff_eq U)) bind'.
  Admitted.

  Global Instance Proper_bind {T U}
  : Proper (@Eff_eq T ==> pointwise_relation T (@Eff_eq U) ==> (@Eff_eq U)) bind.
  Admitted.

  Global Instance Proper_delayBind {T U}
  : Proper (@Eff_eq T ==> pointwise_relation T (@Eff_eq U) ==> (@Eff_eq U)) delayBind.
  Admitted.

  Global Instance Proper_delay {T}
  : Proper (@Eff_eq T ==> @Eff_eq T) delay.
  Admitted.

End Eff.


Arguments bind {_ _ _} _ _.
Arguments bind' {_ _ _} _ _.
Arguments delayBind {_ _ _} _ _.
Arguments interactF {_ _ _ _} _ _.
Arguments interact {_ _ _} _ _.
Arguments retF {_ _ _} _.
Arguments ret {_ _} _.
Arguments delayF {_ _ _} _.
Arguments delay {_ _} _.
Arguments getEff {_ _} _.
Arguments getEff_eq {_ _} _.

(** Interpretation of effects *)

Section interp.

  Context {eff eff' : Type -> Type}.

  Variable do : forall {T}, eff T -> Eff eff' T.

  CoFixpoint interp {T} (c : Eff eff T) : Eff eff' T :=
    match getEff c with
    | retF x => ret x
    | interactF e k =>
      delayBind (do _ e) (fun x => interp (k x))
    | delayF x => delay (interp x)
    end.

  Lemma interp_ret : forall {T} (v : T),
      interp (ret v) = ret v.
  Proof.
    intros.
    rewrite getEff_eq.
    rewrite (getEff_eq (interp (ret v))).
    reflexivity.
  Defined.

  Lemma interp_interact : forall {a b} (e : eff a) (k : a -> Eff eff b),
      interp (interact e k) =
      delayBind (do _ e) (fun x => interp (k x)).
  Proof.
    intros.
    rewrite getEff_eq. symmetry. rewrite getEff_eq. symmetry.
    simpl.
    destruct (delayBind (do a e) (fun x : a => interp (k x))).
    reflexivity.
  Defined.

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

  Definition injL {T} (c : Eff eff T) : Eff (both eff eff') T :=
    interp (fun _ e => interact (bleft e) (@ret _ _)) c.

  Definition injR {T} (c : Eff eff' T) : Eff (both eff eff') T :=
    interp (fun _ e => interact (bright e) (@ret _ _)) c.

End inj.

Arguments injL {_} _ {_} _.
Arguments injR {_ _} _ _.


(* the (value-level) fixpoint effect, this implements value-recursion *)
Section Fix.

  Variable a : Type.

  Inductive fixpoint : Type -> Type :=
  | rec : fixpoint a.

  Variable eff : Type -> Type.

  Section mfix.
    Variable f : Eff (both eff fixpoint) a.

    CoFixpoint finterp {T : Type}
               (c : Eff (both eff fixpoint) T)
    : Eff eff T :=
      match getEff c with
      | retF x => ret x
      | interactF (bleft e) k =>
        interact e (fun x => finterp (k x))
      | interactF (bright e) k =>
        delay (finterp (bind' (fun x => k match e with
                                       | rec => x
                                       end) f))
      | delayF x => delay (finterp x)
      end.

    Definition mfix : Eff eff a := finterp f.

    Definition go (mfix : Eff eff a)
               T (X : both eff fixpoint T) : Eff eff T :=
      match X with
      | bleft e => interact e ret
      | bright f0 =>
        match f0 with
        | rec => mfix
        end
      end.


    Theorem mfix_unfold :
      mfix = interp (go mfix) f.
    Proof. Admitted.

  End mfix.

  Theorem mfix_ret : forall v, mfix (ret v) = ret v.
  Proof. Admitted.

End Fix.

Arguments mfix {_} _.

Section FixF.
  Variable eff : Type -> Type.

  Variable a : Type.
  Variable b : a -> Type.

  Inductive fixpointF : Type -> Type :=
  | callF : forall x : a, fixpointF (b x).

  Section mfix.
    Variable f : forall x : a, Eff (both eff fixpointF) (b x).

    CoFixpoint finterpF {T : Type}
               (c : Eff (both eff fixpointF) T)
    : Eff eff T :=
      match getEff c with
      | retF x => ret x
      | interactF (bleft e) k =>
        interact e (fun x => finterpF (k x))
      | interactF (bright e) k =>
        match e in fixpointF X return (X -> _) -> _ with
        | callF x => fun k =>
          delay (finterpF (bind (f x) k))
        end k
      | delayF x => delay (finterpF x)
      end.

    Definition mfixF (x : a) : Eff eff (b x) :=
      finterpF (f x).

    Definition goF T (X : both eff fixpointF T) : Eff eff T :=
      match X with
      | bleft e => interact e ret
      | bright f0 =>
        match f0 with
        | callF x => mfixF x
        end
      end.

    Theorem mfixF_unfold : forall x,
      Eff_eq _ (mfixF x) (interp goF (f x)).
    Proof.
      unfold mfixF.
      intros.
      generalize (f x).
      cofix rec.
      intro. rewrite getEff_eq. symmetry. rewrite getEff_eq. symmetry.
      simpl.
      destruct (getEff e); simpl.
      - reflexivity.
      - destruct b0; simpl.
        + constructor.
          intro. rewrite bind_ret.
          rewrite rec. reflexivity.


    Admitted.

  End mfix.

  Theorem mfixF_ret : forall v x,
      mfixF (fun x => ret (v x)) x = ret (v x).
  Proof. Admitted.

End FixF.

Arguments callF {_ _} _.

Section mutual_fixpoints.
  Record ftype : Type :=
  { dom : Type
  ; codom : dom -> Type }.
  Definition ftypeD (eff : Type -> Type) (ft : ftype) : Type :=
    forall x : ft.(dom), Eff eff (ft.(codom) x).

  Context {eff : Type -> Type}.

  Context {ts : list ftype}.
  Variable fs :
    forall recs, hlist (ftypeD (both eff recs)) ts ->
            hlist (fun ab : ftype => ftypeD (both eff recs) ab) ts.
  Variable which : fin (length ts).

  Local Definition mdom := {x0 : fin (length ts) & dom (fin_get x0)}.
  Local Definition mcodom :=
   fun x0 : {x0 : fin (length ts) & dom (fin_get x0)} =>
   let ft := fin_get (projT1 x0) in codom ft (projT2 x0).

  Local Definition recs : hlist (ftypeD (both eff (fixpointF mdom mcodom))) ts.
  refine (hlist_map
     (fun (x0 : ftype) (H : {f : fin (length ts) | fin_get f = x0}) =>
      let (x1, e) := H in
      eq_rect (fin_get x1)
        (fun x2 : ftype => ftypeD (both eff (fixpointF mdom mcodom)) x2)
        (fun x2 : dom (fin_get x1) =>
         interact
           (bright
              (callF
                 (existT (fun x3 : fin (length ts) => dom (fin_get x3)) x1 x2)))
           ret) x0 e) (hlist_fins ts)).
  Defined.


  Definition mmfixF : ftypeD eff (fin_get which).
  refine (fun x =>
            let fs := fs _ recs in
            @mfixF eff mdom mcodom
                   (fun '(@existT _ _ tagF x) => @fin_get_hlist _ _ _ fs tagF x)
                   (@existT _ _ which x)
         ).  Show Proof.
  Defined.

End mutual_fixpoints.

(* the empty effect *)
Section nothingE.
  Inductive nothing : Type -> Type := .
End nothingE.

(* the output effect *)
Section outputE.
  Variable t : Type.
  Inductive out : Type -> Type :=
  | outE : t -> out t.
End outputE.

Arguments outE {_} _.


(* mfix Demo *)
Arguments mfixF {_} [_] _ _ _.
Definition count_up : Eff (out nat) False :=
  mfixF (fun _ : nat => False)
        (fun n : nat =>
           interact (bleft (outE n))
                    (fun _ : nat => interact (bright (callF (n + 1))) ret)) 0.

(* the state effect *)
Section stateE.
  Variable s : Type.
  Inductive state : Type -> Type :=
  | Get : state s
  | Put : s -> state unit.

End stateE.

Arguments Get {_}.
Arguments Put {_} _.


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

Lemma delayBind_diverge : forall t u eff (k : t -> Eff eff u),
    Eff_eq eff (delayBind (diverge t) k) (bind (diverge t) k).
Proof.
  intros. cofix rec.
  rewrite diverge_eq.
  rewrite (getEff_eq (delayBind (delay _) _)).
  rewrite (getEff_eq (bind (delay _) _)).
  simpl.
  constructor. reflexivity.
Defined.

Lemma bind_diverge : forall t u eff (k : t -> Eff eff u),
    Eff_eq eff (bind (diverge t) k) (diverge u).
Proof.
  intros. cofix rec.
  rewrite diverge_eq.
  rewrite (getEff_eq (bind (delay _) _)).
  rewrite (getEff_eq (diverge u)).
  simpl.
  constructor. eapply rec.
Defined.

Goal Eff_eq _ trial (diverge _).
  cofix rec.
  unfold trial.
  rewrite mfix_unfold.
  rewrite interp_interact. simpl go.
  change (mfix nothing (interact (bright (Top.rec False)) ret)) with trial.
  rewrite rec. rewrite delayBind_diverge. rewrite bind_diverge. reflexivity.
Admitted. (* need to do paco reasoning? *)