(* Experimentation in strengthened co-induction
 *)

Require Import Paco.paco3.

Section Propy.
  Variable T0 : Type.
  Variable T1 : forall (x0: @T0), Type.
  Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
  Variable P : rel3 T0 T1 T2 -> Prop.
  Variable gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2.
  Arguments gf : clear implicits.

  Definition rel3_iff (r1 r2 : rel3 T0 T1 T2) : Prop :=
    forall a b c, r1 a b c <-> r2 a b c.

  Hypothesis ProperP : forall r1 r2, rel3_iff r1 r2 -> P r1 -> P r2.

  Require Import Paco.pacotac.

  (* From the paper, this seems to be how you strengthen the co-inductive
   * hypothesis. Namely, you require an additional fact about the quantified
   * relation.
   *)
  CoInductive paco3G (r: rel3 T0 T1 T2) x0 x1 x2 : Prop :=
  | paco3G_pfold pco (_ : P pco)
                (LE : pco <3= (paco3G r \3/ r))
                (SIM: gf pco x0 x1 x2).

  (* Now, prove that this is equivalent to `paco3` if `paco3` has the property.
   *
   * The first direction is pretty easy, it doesn't even require the property.
   *)
  Lemma paco3G_to_paco3 : forall r,
      forall x0 x1 x2, paco3G r x0 x1 x2 -> paco3 gf r x0 x1 x2.
  Proof.
    cofix rec; intros.
    - destruct H. econstructor. 2: eassumption. intros.
      eapply LE in PR. destruct PR.
      2: right; eauto.
      left. eapply rec; eauto.
  Defined.

  Hypothesis gf_mon : monotone3 gf.

  (* The second direction requires the property `P` hold on `upaco3 gf r`.
   *)
  Lemma paco3_to_paco3G : forall r, P (upaco3 gf r) ->
            forall x0 x1 x2, paco3 gf r x0 x1 x2 -> paco3G r x0 x1 x2.
  Proof.
    cofix rec; intros.
    - destruct H0. econstructor.
      + eassumption.
      + intros.
        destruct PR; [ left | right; auto ].
        eapply rec in H. 2: eassumption.
        eauto.
      + eapply gf_mon. eassumption.
        intros.
        eapply LE in PR. destruct PR; auto.
  Defined.

  (* This relates to the basic definition, i.e. when we build a relation
   * using paco3, we instantiate `r` with `bot3`.
   *
   * With this instantiation, and the proof about `paco3 gf`, we can
   * prove an isomorphism between `paco3` and `paco3G`.
   *)
  Theorem paco3_paco3G_iff : P (paco3 gf bot3) ->
                             rel3_iff (paco3 gf bot3) (paco3G bot3).
  Proof.
    split; intros.
    - eapply paco3_to_paco3G; eauto.
      eapply ProperP. 2: eassumption.
      clear. intros.
      split; intros.
      + left. assumption.
      + destruct H; auto. destruct H.
    - eapply paco3G_to_paco3; eauto.
  Defined.

  (* This is the "stronger" version of `paco3_acc` that carries arond the
   * extra information about `P`.
   *)
  Theorem paco3G_acc: forall
      l r (OBG: forall rr (INC: r <3= rr) (CIH: l <_paco_3= rr),
              P (upaco3 gf rr) ->
              l <_paco_3= paco3G rr),
      P (upaco3 gf (r \3/ l)) -> (* how are we going to prove this? *)
      l <3= paco3G r.
  Proof.
    intros; assert (SIM: paco3G (r \3/ l) x0 x1 x2).
    { eapply OBG; eauto. }
    clear PR; repeat (try left; do 4 paco_revert; paco_cofix_auto).
  Qed.

(*
  Theorem paco3G_acc: forall
      l r (OBG: forall rr (INC: r <3= rr) (CIH: l <_paco_3= rr),
              P rr ->
              l <_paco_3= paco3G rr),
      P (r \3/ l) -> (* how are we going to prove this? *)
      l <3= paco3G r.
  Proof.
    intros; assert (SIM: paco3G (r \3/ l) x0 x1 x2) by eauto.
    clear PR; repeat (try left; do 4 paco_revert; paco_cofix_auto).
  Qed.
*)

  (* Appealing to the isomorphism between `paco3` and `paco3G`, we get
   * a version of `paco3_acc` that threads the additional information
   * through the theorem.
   *)
  Theorem paco3_acc_P : forall
      l r (OBG: forall rr (INC: r <3= rr) (CIH: l <_paco_3= rr),
              P (upaco3 gf rr) ->
              l <_paco_3= paco3 gf rr),
      P (upaco3 gf (r \3/ l)) -> (* how will this work out? *)
      l <3= paco3 gf r.
  Proof.
    simpl. intros.
    eapply paco3G_to_paco3.
    eapply paco3G_acc; try eassumption.
    intros.
    specialize (OBG _ INC CIH H0 _ _ _ PR0).
    eapply paco3_to_paco3G. 2: eassumption. eauto.
  Defined.

End Propy.