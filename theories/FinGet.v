Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.Fin.

Section fin_get.
  Context {T : Type}.

  Fixpoint fin_get {ls : list T} (f : fin (length ls)) : T.
  destruct ls.
  - apply fin0_elim. eapply f.
  - simpl in f.
    refine (match f in fin (S x)
                 return x = length ls -> _
           with
           | F0 => fun _ => t
           | FS f => fun pf => fin_get _ (match pf in _ = X return fin X with
                                      | eq_refl => f
                                      end)
           end eq_refl).
  Defined.

  Definition fin_get_hlist' {U}
  : forall n (f : fin n) (ls : list T) (hs : hlist U ls) (pf : n = length ls),
      U (fin_get match pf in _ = X return fin X with
                 | eq_refl => f
                 end).
    induction f.
    - destruct ls.
      + inversion pf.
      + simpl.
        inversion pf. subst.
        rewrite (Eqdep_dec.UIP_refl_nat _ pf).
        eapply hlist_hd. eapply hs.
    - destruct ls.
      + inversion pf.
      + inversion pf. subst.
        rewrite (Eqdep_dec.UIP_refl_nat _ pf).
        simpl. apply (IHf _ (hlist_tl hs) eq_refl).
  Defined.

  Definition fin_get_hlist {U}
  : forall (ls : list T) (hs : hlist U ls) (f : fin (length ls)),
      U (fin_get f).
  Proof. intros. eapply (@fin_get_hlist' _ _ f ls hs eq_refl). Defined.

  Definition hlist_fins : forall (ls : list T),
      hlist (fun t => { f : fin (length ls) | fin_get f = t }) ls.
  induction ls.
  - constructor.
  - constructor.
    + exists F0. reflexivity.
    + revert IHls. eapply hlist_map.
      destruct 1.
      exists (FS x0). exact e.
  Defined.
End fin_get.
