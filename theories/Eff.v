Set Universe Polymorphism.

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Setoid.

Require Import Paco.paco3.

Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Fin.
Require Import Interaction.FinGet.

Section paco_facts.

  Global Instance Subrelation_paco3_ext
  : forall {T U V} (r r' : forall x : T, U x -> U x -> Prop) f,
      monotone3 f ->
      (forall Z, subrelation (r Z) (r' Z)) -> subrelation (paco3 f r _) (paco3 f r' V).
  Proof. intros. red. intros.
         eapply paco3_mon. eapply H1. apply H0.
  Qed.

  Lemma upaco3_mon :
    forall (T0 : Type) (T1 : T0 -> Type) (T2 : forall x0 : T0, T1 x0 -> Type)
      (gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2), monotone3 (upaco3 gf).
  Proof. red. intros.
         destruct IN.
         + left. eapply paco3_mon; eauto.
         + right; eauto.
  Qed.

End paco_facts.

Section Eff.
  Polymorphic Universes u u'.
  Variable eff : Type@{u} -> Type@{u'}.

  Inductive EffF (Eff : Type@{u'}) (T : Type@{u}) : Type@{u'} :=
  | retF (_ : T)
  | interactF {A : Type@{u}} (_ : eff A) (_ : A -> Eff)
  | delayF (_ : Eff).
  (* todo: does it make sense for `delay` to be in the definition of `Eff` ?
   * > the implementation of interp requires delay in cases where it doesn't
   *   return something guarded.
   *)

  Arguments retF {_ _} _.
  Arguments interactF {_ _ _} _ _.
  Arguments delayF {_ _} _.

  (* todo: rename to `coEff` *)
  (* todo: make an inductive version to represent terminating programs. *)
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

  Lemma bind_interact : forall {T U V} (e : eff T) (k' : T -> Eff U) (k : U -> Eff V),
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

  Fixpoint Fn {A:Type} (step: A -> A)  (f0 : A) (n:nat) :=
    match n with
    | O => f0 
    | S n => step (Fn step f0 n)
    end.

  (* TODO: generalize for hetero relations *)
  Definition RTopN {A:Type->Type} (Rs: (forall T, A T-> A T->Prop)->(forall T, A T -> A T->Prop)) (n:nat) :=
    Fn Rs (fun _ _ _ => True) (* Top *) n.
  (* Equivalence, including stuttering steps *)

  (* greatest fixpoint if F is continuous *)
  Definition GFPC {A:Type->Type} (Rs: (forall T, A T-> A T->Prop)->(forall T, A T -> A T->Prop))
    T (a1 a2: A T): Prop:=
   forall n, RTopN Rs n _ a1 a2.
  (* Equivalence, including stuttering steps *)
  
  Section Eff_eq.

    Inductive Eff_eqF (eff_eq : forall T, Eff T -> Eff T -> Prop) {T}
    : Eff T -> Eff T -> Prop :=
    | eq_ret : forall t, Eff_eqF eff_eq (ret t) (ret t)
    | eq_interact : forall a (e : eff a) k1 k2,
        (forall x, eff_eq _ (k1 x) (k2 x)) ->
        Eff_eqF eff_eq (interact e k1) (interact e k2)
    | eq_delay : forall a b, eff_eq _ a b ->
                        Eff_eqF eff_eq (delay a) (delay b).

    Definition Eff_eq_ind := GFPC Eff_eqF.

    Lemma Eff_eqF_mon: monotone3 Eff_eqF.
    Proof.
      red. intros.
      destruct IN; try econstructor; eauto.
    Qed.
    Hint Resolve Eff_eqF_mon : paco.

   CoInductive Eff_eq_coind  {T}
     : Eff T -> Eff T -> Prop :=
   | cstep: forall t1 t2, Eff_eqF (@Eff_eq_coind) t1 t2
                     -> Eff_eq_coind t1 t2.

   Require Import Coq.Logic.Eqdep. (* imports the UIP axiom *)
   
 Lemma ind_implies_coind  {T} (t1 t2: Eff T):
   Eff_eq_ind _ t1 t2 -> Eff_eq_coind t1 t2.
 Proof using.
   intros Hi.
   hnf in Hi. revert dependent T. cofix.
   intros.
   constructor.
   pose proof (Hi (1)) as H1i.
   inversion H1i.
-  subst. constructor.
-  subst. constructor. clear H.
   intros ?. apply ind_implies_coind.
   intros ?. specialize (Hi (S n)).
   inversion Hi.  subst.
   apply inj_pair2 in H1. (* uses the UIP axiom! one way to avoid it is to interact only on data of decidable types *)
   apply inj_pair2 in H2.
   apply inj_pair2 in H3.
   apply inj_pair2 in H4.
   subst. clear H3. hnf. apply H0.
- subst. 
   subst. constructor.  clear H.
   apply ind_implies_coind.
   intros ?. specialize (Hi (S n)).
   inversion Hi.  subst. eauto.
 Qed.
 
 Lemma coind_implies_ind  {T} (t1 t2: Eff T):
   Eff_eq_coind t1 t2 -> Eff_eq_ind _ t1 t2.
 Proof using.
   intros Hi n. revert dependent T.
   induction n; intros; [exact I|].
   hnf. inversion Hi; subst.
   pose proof Eff_eqF_mon as Hm.
   hnf in Hm.
   eapply Hm;[ apply H | ].
   intros. simpl. 
   specialize (IHn _ _ _ PR).
   exact IHn.
 Qed.
 
    Definition Eff_eq : forall {T}, Eff T -> Eff T -> Prop :=
      paco3 Eff_eqF bot3.

    
    Global Instance Reflexive_Eff_eq {T} : Reflexive (@Eff_eq T).
    Proof.
      red.
      pcofix rec.
      intros. pfold.
      destruct x. destruct e; simpl; constructor.
      intros. right. eapply rec.
      right. eapply rec.
    Defined.

    Global Instance Symmetric_Eff_eq {T} : Symmetric (@Eff_eq T).
    Proof.
      red. pcofix rec.
      intros. pfold.
      punfold H0.
      inversion_clear H0.
      - constructor.
      - constructor.
        intros. specialize (H x0).
        destruct H.
        { eapply rec in H. right. assumption. }
        { destruct H. }
      - constructor.
        destruct H.
        { apply rec in H. right; assumption. }
        { destruct H. }
    Qed.

    Lemma Eff_eqF_inj_interact : forall {T U} rel e (k : T -> Eff U) z,
        Eff_eqF rel (interact e k) z ->
        exists k', z = interact e k' /\ (forall x, rel _ (k x) (k' x)).
    Proof.
      intros.
      refine match H in Eff_eqF _ X Z
                   return match X return Prop with
                          | do (interactF e k) => _
                          | do _ => True
                          end
             with
             | eq_ret _ _ => I
             | eq_interact _ _ _ _ _ _ => _
             | eq_delay _ _ _ _ => I
             end; simpl.
      eexists; split. reflexivity. assumption.
    Defined.

    Global Instance Transitive_Eff_eq {T} : Transitive (@Eff_eq T).
    Proof.
      red. pcofix rec.
      intros. pfold. punfold H0; punfold H1.
      inversion H0; clear H0; subst.
      - inversion H1; clear H1; subst.
        constructor.
      - eapply Eff_eqF_inj_interact in H1. destruct H1 as [ ? [ ? ? ] ].
        subst.
        constructor. intros.
        specialize (H x0). specialize (H1 x0).
        destruct H1 as [ | [ ] ].
        destruct H as [ | [ ] ].
        right. eapply rec; eassumption.
      - inversion H1; clear H1; subst.
        constructor.
        destruct H as [ | [] ].
        destruct H2 as [ | [] ].
        right; eapply rec; eassumption.
    Defined.

    Global Instance Proper_bind' {T U}
    : Proper (pointwise_relation T (@Eff_eq U) ==> @Eff_eq T ==> (@Eff_eq U))
             bind'.
    Proof.
      red. red. red.
      pcofix rec; intros.
      punfold H1. pfold.
      rewrite getEff_eq. rewrite getEff_eq at 1.
      inversion_clear H1.
      - simpl.
        specialize (H0 t).
        punfold H0.
        inversion H0; clear H0; subst.
        + constructor.
        + constructor.
          intro x1. specialize (H2 x1).
          destruct H2 as [ | [] ].
          left. eapply paco3_mon. eapply H0.
          inversion 1.
        + simpl. constructor.
          destruct H2 as [ | [] ].
          left. eapply paco3_mon. eapply H0.
          inversion 1.
      - simpl. constructor. intros.
        right.
        eapply (rec x y H0 (k1 x1) (k2 x1)).
        specialize (H x1). destruct H as [ | [] ].
        eapply H.
      - simpl. constructor.
        intros.
        right.
        eapply (rec _ _ H0).
        destruct H as [ | [] ]. apply H.
    Defined.

    Global Instance Proper_bind {T U}
    : Proper (@Eff_eq T ==> pointwise_relation T (@Eff_eq U) ==> (@Eff_eq U))
             bind.
    Proof.
      do 3 red. intros. eapply Proper_bind'; eauto.
    Defined.

    Global Instance Proper_delayBind {T U}
    : Proper (@Eff_eq T ==> pointwise_relation T (@Eff_eq U) ==> (@Eff_eq U))
             delayBind.
    Proof.
      red. red. red. intros.
      rewrite getEff_eq. rewrite getEff_eq at 1.
      pinversion H.
      - simpl. pfold. constructor.
        left. eapply H0.
      - simpl. pfold. constructor.
        intros.
        specialize (H1 x1).
        destruct H1 as [ | [] ].
        left.
        eapply Proper_bind. eapply H1. eapply H0.
      - simpl. pfold. constructor.
        left.
        eapply Proper_bind. eapply H1. eapply H0.
    Defined.

    Global Instance Proper_delay {T}
    : Proper (@Eff_eq T ==> @Eff_eq T) delay.
    Proof.
      do 2 red.
      intros.
      pfold. constructor. left; eapply H.
    Defined.

    Lemma bind_bind_gen : forall r {T U V} c (k : T -> Eff U) (k' : U -> Eff V),
        paco3 Eff_eqF r _ (bind (bind c k) k')(bind c (fun x => bind (k x) k')).
    Proof.
      pcofix rec.
      intros.
      rewrite getEff_eq.
      rewrite getEff_eq at 1. simpl.
      destruct (getEff c).
      - destruct (k t); destruct e.
        + simpl. eapply paco3_mon.
          eapply Reflexive_Eff_eq. inversion 1.
        + simpl. eapply paco3_mon.
          eapply Reflexive_Eff_eq. inversion 1.
        + simpl. eapply paco3_mon.
          eapply Reflexive_Eff_eq. inversion 1.
      - simpl. pfold. constructor; intros.
        right.
        eapply (rec _ _ _ (e0 x) k k').
      - simpl. pfold. constructor.
        right. eapply (rec _ _ _ e k k').
    Defined.

    Theorem bind_bind : forall {T U V} c (k : T -> Eff U) (k' : U -> Eff V),
        Eff_eq (bind (bind c k) k') (bind c (fun x => bind (k x) k')).
    Proof.
      intros; eapply bind_bind_gen.
    Defined.

  End Eff_eq.

  Hint Resolve Eff_eqF_mon : paco.

  (* Equivalence, excluding stuttering *)
  Section Eff_sim.
    Variable rel_eff : forall {T}, eff T -> eff T -> Prop.

    Definition notDelay {T} (c : Eff T) : Prop :=
      match c with
      | do (delayF _) => False
      | _ => True
      end.

    Inductive DropDelay {T} : Eff T -> Eff T -> Prop :=
    | drop_last : forall x, notDelay x -> DropDelay (delay x) x
    | drop_then : forall x y, DropDelay x y -> DropDelay (delay x) y.

    Section Eff_simF.
      Variable (eff_sim : forall T, Eff T -> Eff T -> Prop).

      Inductive Eff_simF {T} : Eff T -> Eff T -> Prop :=
      | sim_ret : forall t, Eff_simF (ret t) (ret t)
      | sim_interact : forall a (e1 e2 : eff a) k1 k2,
          rel_eff _ e1 e2 ->
          (forall x, eff_sim _ (k1 x) (k2 x)) ->
          Eff_simF (interact e1 k1) (interact e2 k2)
      (* note that we have to drop *all* delays in order to ensure that
       * we don't relate all programs to divergence.
       *)
      | sim_delayL : forall a a' b,
          DropDelay a a' ->
          notDelay b ->
          eff_sim _ a' b ->
          Eff_simF a b
      | sim_delayR : forall a b b',
          notDelay a ->
          DropDelay b b' ->
          eff_sim _ a b' ->
          Eff_simF a b
      (* in order to preserve reflexivity of the relation, we need to
       * relate programs that delay forever to themselves.
       *)
      | sim_delay_both : forall a b,
          eff_sim _ a b ->
          Eff_simF (delay a) (delay b)
      .

      (* attribution: the phrasing of delay is based on the vellvm semantics. *)

    End Eff_simF.

    Lemma Eff_simF_mon: monotone3 Eff_simF.
    Proof.
      red. intros.
      destruct IN; try solve [ econstructor; eauto ].
    Qed.
    Hint Resolve Eff_simF_mon : paco.

    Definition Eff_sim : forall {T}, Eff T -> Eff T -> Prop :=
      paco3 Eff_simF bot3.

    Hypothesis Refl_rel_eff : forall {T}, Reflexive (@rel_eff T).

    Global Instance Reflexive_Eff_sim {T} : Reflexive (@Eff_sim T).
    Proof.
      red.
      pcofix rec.
      intros. pfold.
      destruct x; destruct e; simpl.
      - constructor.
      - constructor. reflexivity.
        right. eapply rec.
      - constructor. right. auto.
    Defined.

    Hypothesis Sym_rel_eff : forall {T}, Symmetric (@rel_eff T).

    Global Instance Symmetric_Eff_sim {T} : Symmetric (@Eff_sim T).
    Proof using Sym_rel_eff.
      red. pcofix rec.
      intros. pfold.
      punfold H0.
      inversion_clear H0.
      - constructor.
      - constructor.
        + symmetry. assumption.
        + intros. specialize (H1 x0).
          destruct H1 as [ | [] ].
          right. eapply rec. assumption.
      - eapply sim_delayR; [ eassumption | eassumption | ].
        destruct H2 as [ | [] ].
        right; eapply rec; eassumption.
      - eapply sim_delayL; [ eassumption | eassumption | ].
        destruct H2 as [ | [] ].
        right; eapply rec; eassumption.
      - constructor.
        destruct H as [ | [] ].
        right; eapply rec; eassumption.
    Defined.

    Lemma Eff_simF_inj_interact : forall {T U} rel e (k : T -> Eff U) z,
       Eff_simF rel (interact e k) z ->
         (exists e' k', z = interact e' k' /\
                   rel_eff _ e e' /\
                   (forall x, rel _ (k x) (k' x)))
       \/ (exists e' k', DropDelay z (interact e' k') /\
                   rel_eff _ e e' /\
                   (forall x, rel _ (k x) (k' x))).
    Proof. (*
      intros.
      refine match H in Eff_simF _ X Z
                   return match X return Prop with
                          | do (interactF e k) => _
                          | do _ => True
                          end
             with
             | sim_ret _ _ => I
             | sim_interact _ _ _ _ _ _ _ _ => _
             | sim_delayL _ _ _ _ _ _ _ => _
             | sim_delayR _ _ _ _ _ _ _ => _
             | sim_delay_both _ _ _ _ => I
             end; simpl.
      - left. do 2 eexists. split; [ reflexivity | split; eauto ].
      - inversion d; exact I.
      - destruct e0; destruct e0; try exact I.
        right. induction d.
        + exists e0; exists e3.

        + destruct IHd; eauto. destruct H0; subst.
          eexists. split. reflexivity.

          Defined.
*)
    Admitted.

    Hypothesis Trans_rel_eff : forall {T}, Transitive (@rel_eff T).

    Global Instance Transitive_Eff_sim {T} : Transitive (@Eff_sim T).
    Proof using Trans_rel_eff.
(*
      red. pcofix rec.
      destruct x; destruct e; simpl; intros.
      - pfold. punfold H0.
      -


      intros. pfold. punfold H0.
      inversion H0; clear H0; subst.
      - punfold H1; inversion H1; clear H1; subst.
        + constructor.
        + constructor.
          destruct H as [ | [] ].
          right. eapply rec. eapply H. reflexivity.
      - punfold H1. eapply Eff_simF_inj_interact in H1.
        destruct H1.
        + destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ].
          subst.
          constructor.
          * etransitivity; eassumption.
          * intros.
            specialize (H3 x1); specialize (H2 x1).
            destruct H3 as [ | [] ].
            destruct H2 as [ | [] ].
            right; eapply rec; eassumption.
        + destruct H0 as [ ? [ ? ? ] ].
          subst. constructor.
          destruct H1 as [ | [] ].
          right. eapply rec; [ | eassumption ].
          pfold. constructor. assumption. eapply H2.
      - constructor.
        right. eapply rec.
        destruct H as [ | [] ].
        eapply p.
        eassumption.
      - eapply paco3_unfold in H1; eauto with paco.
        inversion H1; clear H1; subst.
        + destruct H as [ | [] ].
          destruct H2 as [ | [] ].
          specialize (rec _ _ _ H H0).

        right. eapply rec.
        destruct H as [ | [] ].
        eapply p.
        eassumption.
    Defined.
*)
    Admitted.

    Global Instance Subrelation_Eff_sim_Eff_eq {T}
    : subrelation (@Eff_eq T) (@Eff_sim T).
    Proof using Refl_rel_eff.
      red. pcofix rec.
      intros.
      punfold H0.
      inversion_clear H0.
      - pfold. constructor.
      - pfold. constructor.
        + reflexivity.
        + intros. right. eapply rec.
          destruct (H x0) as [ | [] ]. apply H0.
      - pfold. constructor.
        destruct H as [ | [] ].
        right. apply rec; auto.
    Qed.

  End Eff_sim.

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

  Variable eval : forall {T}, eff T -> Eff eff' T.

  CoFixpoint interp {T} (c : Eff eff T) : Eff eff' T :=
    match getEff c with
    | retF x => ret x
    | interactF e k =>
      delayBind (eval _ e) (fun x => interp (k x))
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
      delayBind (eval _ e) (fun x => interp (k x)).
  Proof.
    intros.
    rewrite getEff_eq. symmetry. rewrite getEff_eq. symmetry.
    simpl.
    destruct (delayBind (eval a e) (fun x : a => interp (k x))).
    reflexivity.
  Defined.

  Lemma interp_delay : forall {a} (k : Eff eff a),
      interp (delay k) = delay (interp k).
  Proof.
    intros.
    rewrite getEff_eq. symmetry. rewrite getEff_eq. symmetry.
    reflexivity.
  Defined.



  Theorem interp_bind : forall {T U} (c : Eff _ T) (k : T -> Eff _ U),
      Eff_eq _ (interp (bind c k))
             (bind (interp c) (fun x => interp (k x))).
  Proof.
    pcofix rec.
    intros.
    rewrite getEff_eq at 1.
    rewrite (getEff_eq (bind (interp c) (fun x : T => interp (k x)))).
    simpl. destruct (getEff c).
    - simpl. destruct (k t); destruct e; simpl.
      + pfold. constructor.
      + eapply paco3_mon.
        eapply Reflexive_Eff_eq.
        inversion 1.
      + eapply paco3_mon.
        eapply Reflexive_Eff_eq.
        inversion 1.
    - simpl.
      change (paco3 (Eff_eqF eff') r U
    match
      match
        delayBind (eval A e)
          (fun x : A =>
           interp
             (bind' k (e0 x)))
      with
      | do _ _ y => y
      end
    with
    | retF v => ret v
    | @interactF _ _ _ A0 e1 k0 => interact e1 k0
    | delayF k0 => delay k0
    end
    match
      match
        match
          match delayBind (eval A e) (fun x : A => interp (e0 x)) with
          | do _ _ y => y
          end
        with
        | retF x => interp (k x)
        | @interactF _ _ _ A0 io k' =>
            interact io
              (fun x : A0 => bind' (fun x => interp (k x)) (k' x))
        | delayF f =>
            delay
              (bind' (fun x => interp (k x)) f)
        end
      with
      | do _ _ y => y
      end
    with
    | retF v => ret v
    | @interactF _ _ _ A0 e1 k0 => interact e1 k0
    | delayF k0 => delay k0
    end).
      destruct (eval A e). destruct e1; simpl.
      + pfold. constructor.
        right. eapply (rec _ _ (e0 a) k).
      + pfold. constructor.
        intros.
        (* here I need to appeal to the associativity of bind to pull
         * off the head `bind (e2 x)` and use the inductive hypothesis
         * to prove the rest. However, I don't know that `r` is transitive
         * so I can't appeal to transitivity.
         *)
        change (bind' (fun x0 : T => interp (k x0))
       (bind (e2 x) (fun x0 : A => interp (e0 x0))))
          with (bind (bind (e2 x) (fun x0 => interp (e0 x0))) (fun x0 => interp (k x0))).
        admit.
      + pfold. constructor.
        (* this is the same problem *)
        admit.
    - simpl. pfold. constructor.
      right. eapply (rec _ _ e k).
  Admitted.

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
        | callF x => delay (mfixF x)
        end
      end.

    Theorem finterpF_bind : forall {T U} (c : Eff _ T) (k : T -> Eff _ U),
        Eff_eq _ (finterpF (bind c k))
               (bind (finterpF c) (fun x => finterpF (k x))).
    Proof.
      pcofix rec.
      intros.
      pfold.
      rewrite getEff_eq at 1.
      rewrite (getEff_eq (bind (finterpF c) (fun x : T => finterpF (k x)))).
      simpl. destruct (getEff c).
      - simpl. destruct (k t); destruct e; simpl.
        + constructor.
        + destruct b0; simpl.
          constructor.
          * intros. left.
            eapply paco3_mon; [ eapply Reflexive_Eff_eq | ].
            inversion 1.
          * destruct f0.
            simpl. constructor.
            left; eapply paco3_mon.
            eapply Reflexive_Eff_eq. inversion 1.
        + constructor.
          left. eapply paco3_mon; [ eapply Reflexive_Eff_eq | inversion 1 ].
      - simpl. destruct b0; simpl.
        + constructor. intros.
          match goal with
          | |- _ _ _ _ (finterpF (?X _)) (?Y _) =>
            change X with (bind' k) ;
            change Y with (bind' (fun x0 => finterpF (k x0)))
          end.
          right.
          apply (rec U _ (e x) k).
        + destruct f0. simpl.
          constructor.
          match goal with
          | |- _ _ (finterpF (bind _ (fun x => ?X _))) (?Y _) =>
            change X with (bind' k) ;
            change Y with (bind' (fun x0 => finterpF (k x0)))
          end.
          admit. (* I need a stronger inductive hypothesis... *)
      - simpl. constructor.
        right. eapply (rec _ _ e k).
    Admitted.

  End mfix.

  Theorem finterpF_interp_goF : forall {T} f (x : Eff _ T),
      Eff_eq _ (finterpF f x) (interp (goF f) x).
  Proof.
(*
    unfold mfixF.
    pcofix rec.
    intros.
    pfold.
    rewrite getEff_eq at 1. rewrite (getEff_eq (interp (goF f) x)).
    simpl.
    destruct (getEff x).
    - simpl. constructor.
    - destruct b0; simpl.
      + constructor; intros.
        rewrite bind_ret.
        match goal with
        | |- _ _ _ _ (?Y _ _) (?X _ _) =>
          change X with (@interp _ _ (goF f));
          change Y with (@finterpF f)
        end.
        right. eapply rec.
      + destruct f0.
        match goal with
        | |- context [ delay (?X _ _) ] =>
          change X with (@finterpF f)
        end.
        match goal with
        | |- context [ ?X _ _ ] =>
          change X with (@interp _ _ (goF f))
        end.
        simpl. constructor.
        unfold mfixF.
        left.


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

*)
  Admitted.


  Theorem mfixF_unfold : forall f x,
      Eff_eq _ (mfixF f x) (interp (goF f) (f x)).
  Proof.
(*
    unfold mfixF.
    pcofix rec.
    intros.
    pfold.
    rewrite getEff_eq at 1. rewrite (getEff_eq (interp (goF f) (f x))).
    simpl.
    destruct (getEff (f x)).
    - simpl. constructor.
    - destruct b0; simpl.
      + constructor; intros.
        rewrite bind_ret.
        match goal with
        | |- _ _ _ _ (?Y _ _) (?X _ _) =>
          change X with (@interp _ _ (goF f));
          change Y with (@finterpF f)
        end.
        right



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
*)
  Admitted.



  Theorem mfixF_ret : forall v x,
      mfixF (fun x => ret (v x)) x = ret (v x).
  Proof. Admitted.

End FixF.

Arguments mfixF {_} [_] _ _ _.
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


  Definition mmfixF : ftypeD eff (fin_get which) :=
    fun x =>
      let fs := fs _ recs in
      @mfixF eff mdom mcodom
             (fun '(@existT _ _ tagF x) => @fin_get_hlist _ _ _ fs tagF x)
             (@existT _ _ which x).

End mutual_fixpoints.


(* the output effect *)
Section outputE.
  Variable t : Type.
  Inductive out : Type -> Type :=
  | outE : t -> out t.
End outputE.

Arguments outE {_} _.

(* mfix Demo *)

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
Arguments mfixF {_ _} _ _ _.
Arguments fixpointF {_} _ _.
Arguments injL {_ _ _  } _.

Definition DO {eff a} (c : eff a) : Eff eff a :=
  interact c ret.

Definition spin {eff} {a} : Eff eff a :=
  mfixF (fun _ : unit => a)
        (fun _ : unit => DO (bright (callF tt))) tt.

Notation "x <- e  ;; k" := (bind e (fun x => k)) (at level 30).

Definition until {eff} (e : Eff eff bool) : Eff eff unit :=
  mfixF (fun _ : unit => unit)
        (fun _ => test <- injL e ;;
                if test
                then DO (bright (callF tt))
                else ret tt) tt.

(*
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
*)