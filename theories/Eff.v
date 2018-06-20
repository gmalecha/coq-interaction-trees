Section freeD.
  Variable eff : Type -> Type.

  CoInductive freeD (T : Type) : Type :=
  | ret (_ : T)
  | interact {A} (_ : eff A) (_ : A -> freeD T)
  | delay (_ : freeD T).

  Arguments ret {_} _.
  Arguments interact {_ _} _ _.
  Arguments delay {_}.

  Section bind.
    Context {A B : Type} (k : A -> freeD B).

    CoFixpoint bind' (f : freeD A) : freeD B :=
      match f with
      | ret x => k x
      | interact io k' => interact io (fun x => bind' (k' x))
      | delay f => delay (bind' f)
      end.
  End bind.

  Definition bind {A B} (f : freeD A) (k : A -> freeD B) : freeD B :=
    bind' k f.

  (* I should use paco to define this *)
  CoInductive freeD_eq {T} : freeD T -> freeD T -> Prop :=
  | eq_ret : forall t, freeD_eq (ret t) (ret t)
  | eq_interact : forall a (e : eff a) k1 k2,
      (forall x, freeD_eq (k1 x) (k2 x)) ->
      freeD_eq (interact e k1) (interact e k2)
  | eq_delay : forall a b, freeD_eq a b ->
                      freeD_eq (delay a) (delay b).

  CoInductive freeD_sim {T} : freeD T -> freeD T -> Prop :=
  | sim_ret : forall t, freeD_sim (ret t) (ret t)
  | sim_interact : forall a (e : eff a) k1 k2,
      (forall x, freeD_sim (k1 x) (k2 x)) ->
      freeD_sim (interact e k1) (interact e k2)
  | sim_delay : forall a b, freeD_sim a b ->
                       freeD_sim (delay a) (delay b).

End freeD.


Arguments bind {_ _ _} _ _.
Arguments bind' {_ _ _} _ _.
Arguments interact {_ _ _} _ _.
Arguments ret {_ _} _.
Arguments delay {_ _} _.

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

  CoFixpoint injL {T} (c : freeD eff T) : freeD (both eff eff') T :=
    match c with
    | ret x => ret x
    | interact e k => interact (bleft e) (fun x => injL (k x))
    | delay x => delay (injL x)
    end.

  CoFixpoint injR {T} (c : freeD eff' T) : freeD (both eff eff') T :=
    match c with
    | ret x => ret x
    | interact e k => interact (bright e) (fun x => injR (k x))
    | delay x => delay (injR x)
    end.

End inj.

Arguments injL {_} _ {_} _.
Arguments injR {_ _} _ _.

Section interp.

  Context {eff eff' : Type -> Type}.

  Variable do : forall {T}, eff T -> freeD eff' T.

  CoFixpoint interp {T} (c : freeD eff T) : freeD eff' T :=
    match c with
    | ret x => ret x
    | interact e k =>
      match do _ e with
      | ret v => delay (interp (k v))
      | interact e k' =>
        interact e (fun x => bind (k' x) (fun y => interp (k y)))
      | delay v => delay (@bind' _ _ _ (fun x => interp (k x)) v)
      end
    | delay x => delay (interp x)
    end.
End interp.


Section Fix.

  Variable a : Type.

  Inductive fixpoint : Type -> Type :=
  | rec : fixpoint a.

  Variable eff : Type -> Type.

  (** Begin a bunch of variants to try to implement mfix *)

  Section mfix.
    Variable f : freeD (both eff fixpoint) a.

    CoFixpoint finterp_then
           {T b : Type} (k' : T -> freeD eff b)
               (c : freeD (both eff fixpoint) T) : freeD eff b :=
      match c with
      | ret x => delay (k' x)
      | interact (bleft e) k =>
        interact e (fun x => finterp_then k' (k x))
      | interact (bright e) k =>
        delay (finterp_then k' (bind' (fun x => k match e with
                                        | rec => x
                                        end) f))
      | delay x => delay (finterp_then k' x)
      end.

    Definition mfix : freeD eff a := finterp_then ret f.
  End mfix.

  Definition go (mfix : freeD eff a)
    T (X : both eff fixpoint T) : freeD eff T :=
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

End Fix.

Arguments mfix {_} _.

Section stateE.
  Variable s : Type.
  Inductive state : Type -> Type :=
  | Get : state s
  | Put : s -> state unit.

End stateE.

Arguments Get {_}.
Arguments Put {_} _.

Section nothingE.
  Inductive nothing : Type -> Type := .
End nothingE.

(** Testing *)
Definition trial : freeD nothing False :=
  mfix nothing (interact (bright (rec False)) ret).



Goal freeD_eq _ trial (cofix rec := delay rec).
  cofix rec.
  unfold trial. rewrite mfix_unfold.
Admitted.