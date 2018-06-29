
Section Eff_acc.

  Variable eff : Type -> Type.

  (* the thought is that I can shift accesses into the variable contex
   * - if i do this, then i need to be able to extend the effect system in
   *   different ways, for example,
   *
   *   Probe {t}
   *         (ret : t -> Eff eff a)
   *         (int : forall a, e b -> Eff (both eff (indexed a (fun _ => t))) a)
   *         (del : Eff (both eff (one t)) a)
   *   : eff t -> Eff eff a
   *)

  Record WC : Type :=
  { A : Type
  ; B : A -> Type }.

  (* This is the co-inductive type *)
  CoInductive C (wt : WC) : Type :=
  | Cprobe : forall x : wt.(A), (wt.(B) x -> C wt) -> C wt.

  Inductive One (wc : WC) : WC -> Type :=
  | It : One wc wc.

  Inductive Indexed (a : Type) (b : a -> WC) : WC -> Type :=
  | ref : forall x : a, Indexed a b (b x).

  Inductive both (a b : WC -> Type) (x : WC) : Type :=
  | L (_ : a x)
  | R (_ : b x).

  Arguments L {_ _ _} _.
  Arguments R {_ _ _} _.

  Inductive P (e : WC -> Type) (T : Type) : Type :=
  | Ret (_ : T)
  | Probe {wt : WC} (p : e wt)
          (_ : forall x : wt.(A),
              P (both e (Indexed (wt.(B) x) (fun _ => wt))) T).

  Arguments Ret {_ _} _.
  Arguments Probe {_ _ _} _ _.

  Fixpoint interpP (e : WC -> Type)
           (eD : forall wt, e wt -> C wt) (* This is a cop-out because I'm using `C` *)
           {t} (p : P e t) {struct p}
  : t.
  refine
    match p with
    | Ret r => r
    | Probe r k =>
      match eD _ r with
      | @Cprobe _ tag values =>
        @interpP _ (fun _ b =>
                      match b with
                      | L l => eD _ l
                      | R r => _
                      end) _ (k tag)
      end
    end; simpl in *.
  destruct r. clear - values x. tauto.
  Defined.




(*

  (* This is essentially `G -> T` *)
  Inductive EffP (G : Type) (T : Type) : Type :=
  | Probe (onRet : T -> W)
          (onInt : forall a, eff a -> (a -> EffP T W -> W) -> W)
          (onDelay : EffP T W)
    : EffP G T.

  Inductive EffF (Eff : Type -> Type) (T : Type) : Type :=
  | retF (_ : T)
  | interactF {A : Type} (_ : eff A) (_ : A -> Eff T)
  | delayF (_ : Eff T).




  Definition probe {T W}
             (onRet : T -> W)
             (onInt : forall a, eff a -> (a -> EffP T W -> W) -> W)
             (onDelay : EffP T W)
    : EffP T W.


  Definition prog_EffF
             (p : forall E : Type -> Type, (forall t, E t -> EffF E t)

(*
  Inductive DEffF (Eff : Type) (W : Type) (T : Type) : Type :=
  { is_interactF : (
*)

  (* Think of this as `Eff T -> W` *)
  Inductive EffP (T : Type) (W : Type) : Type :=
  | Probe (onRet : T -> W)
          (onInt : forall a, eff a -> (a -> EffP T W -> W) -> W)
          (onDelay : EffP T W) : EffP T W.
*)