Set Universe Polymorphism.

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Setoid.

Require Import Paco.paco3.

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
  (* todo: does it make sense for `delay` to be in the definition of `Eff` ? *)

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

    Lemma Eff_eqF_mon: monotone3 Eff_eqF.
    Proof.
      red. intros.
      destruct IN; try econstructor; eauto.
    Qed.
    Hint Resolve Eff_eqF_mon : paco.

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

  End Eff_eq.

  (* Equivalence, excluding stuttering *)
  Section Eff_sim.
    Variable rel_eff : forall {T}, eff T -> eff T -> Prop.

    Definition notDelay {T} (c : Eff T) : Prop :=
      match c with
      | do (delayF _) => False
      | _ => True
      end.

    Inductive DropDelay {T} : Eff T -> Eff T -> Prop :=
    | drop_delay : forall x y, DropDelay x y -> DropDelay (delay x) y
    | drop_no_delay : forall x, notDelay x -> DropDelay x x.

    CoInductive DelaysForever {T} : Eff T -> Prop :=
    | forever_delay : forall e, DelaysForever e -> DelaysForever (delay e).

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
      | sim_delay : forall a a' b,
          DropDelay (delay a) a' ->
          eff_sim _ a' b ->
          Eff_simF (delay a) b
      | sim_delayR : forall a b b',
          DropDelay (delay b) b' ->
          eff_sim _ a b' ->
          Eff_simF a (delay b)
      (* in order to preserve reflexivity of the relation, we need to
       * relate forever delaying programs to themselves.
       *)
      | sim_delay_forever : forall a b,
          DelaysForever a -> DelaysForever b ->
          Eff_simF (delay a) (delay b)
      .

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
      - constructor.
        left. pfold. constructor. right. eauto.
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
      - constructor.
        destruct H as [ | [] ].
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
       \/ (exists z', z = delay z' /\ rel _ (interact e k) z').
    Proof.
      intros.
      refine match H in Eff_simF _ X Z
                   return match X return Prop with
                          | do (interactF e k) => _
                          | do _ => True
                          end
             with
             | sim_ret _ _ => I
             | sim_interact _ _ _ _ _ _ _ _ => _
             | sim_delayL _ _ _ _ => I
             | sim_delayR _ _ _ _ => _
             end; simpl.
      - left. do 2 eexists. split; [ reflexivity | split; eauto ].
      - destruct e0. destruct e0; auto.
        right. eexists; split; eauto.
    Defined.

    Hypothesis Trans_rel_eff : forall {T}, Transitive (@rel_eff T).

    Global Instance Transitive_Eff_sim {T} : Transitive (@Eff_sim T).
    Proof using Trans_rel_eff.
      red. pcofix rec.
      destruct x; destruct e; simpl; intros.
      - admit.
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