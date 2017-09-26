(* -*- mode: coq; mode: visual-line -*-  *)
(** * Impredicative truncations. *)

Require Import HoTT.Basics HoTT.Types (* UnivalenceImpliesFunext *) HProp.
Local Open Scope path_scope.

Section NoPropResizing.

  Set Printing Universes.

  Eval compute in IsHProp.
  (* for readability replace Top.xxx by i
   = fun A : Type@{i} => forall x y : A, Contr_internal@{i} (x = y)
     : Type@{i} -> Type@{i}
  *)
  
  Definition IsHPropexpl (A : Type@{i}) : Type@{i} :=
    forall x y : A, Contr_internal (x = y).
  
  Definition merely@{i j} (A : Type@{i}) : Type@{i}
    := forall P:Type@{j}, IsHPropexpl P -> (A -> P) -> P.  (* j < i *)

  Definition trm {A} : A -> merely A
    := fun a P HP f => f a.


  Definition ishprop_merely `{Funext} (A : Type@{i}) : IsHPropexpl@{i} (merely@{i j} A).
  Proof.
    exact (@trunc_forall H Type (fun P : Type => IsHPropexpl P -> (A -> P) -> P) 
  (-1)
  (fun P : Type =>
   @trunc_forall H (IsHPropexpl P) (fun _ : IsHPropexpl P => (A -> P) -> P) 
     (-1) (fun p : IsHPropexpl P => @trunc_arrow H (A -> P) P (-1) p))).
  Defined.

  (* the naive definition *)
  Definition merely_rec {A : Type@{i}} {P : Type@{j}} {p:IsHPropexpl@{j} P} (f : A -> P)
    : merely@{i j} A -> P
    := fun ma => ma P p f.

  Definition functor_merely `{Funext} {A B : Type@{k}} (f : A -> B)
    : merely@{j k} A -> merely@{k l} B. (* evidently, k<j and l<k *)
  Proof.
    srefine (merely_rec (trm o f)).
    apply ishprop_merely.
  Defined.

  Definition typeofid (A: Type) := A -> A.

  (* impossible due to universe inconsistency:
  Definition functor_merely_equalargs `{Funext} {A : Type} (f : typeofid A)
    : typeofid(merely A) := functor_merely f.
  The following much weaker definition is possible:  
  *)
  
  Definition functor_merely_equalargs_weak `{Funext} {A : Type} (f : typeofid A)
    : merely A -> merely A := functor_merely f.

End NoPropResizing.
