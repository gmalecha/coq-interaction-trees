Require Import Coq.Lists.List.
Require Import Interaction.Eff.

Require Import ExtLib.Data.HList.

Section Link.

  Inductive Empty : Type -> Type :=.

  (* Foo :: nat -> nat *)
  Inductive Foo : Type -> Type :=
  | callFoo : nat -> Foo nat.

  (* Bar :: bool -> bool *)
  Inductive Bar : Type -> Type :=
  | callBar : bool -> Bar bool.


  Variable foo : nat -> Eff Bar nat.
  Variable bar : bool -> Eff Foo bool.

  Definition link : (nat -> Eff Empty nat) * (bool -> Eff Empty bool).
  refine (
    let res :=
        @mmfixF Empty (   {| dom := nat ; codom := fun _ => nat |}
                       :: {| dom := bool ; codom := fun _ => bool |}
                       :: nil)
                (fun recsT recs =>
                   Hcons (fun x => _) (Hcons _ Hnil)) 
    in (res Fin.F0, res (Fin.FS Fin.F0))).
  refine (
         interp
           (fun (T0 : Type) (H : Bar T0) =>
            match H in (Bar T) return (Eff (both Empty recsT) T) with
            | callBar b =>
              hlist_hd (hlist_tl recs) b
            end) (foo x)).
  refine (fun x =>
         interp
           (fun (T0 : Type) (H : Foo T0) =>
            match H in (Foo T) return (Eff (both Empty recsT) T) with
            | callFoo n =>
              hlist_hd recs n
            end) (bar x)).
  Defined.

End Link.

Print link.