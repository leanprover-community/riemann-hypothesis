module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteEpsilonOperator
public import Formalism.LocalToGlobal.IndefiniteReal.TransferStatement

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def prin {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) : CxData A := { X with nP := fun _ => 1 }

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

section Prims

variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

variable {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
    {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

end Prims

section Group

variable {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]

def CharsX (τ : ∀ s, Representation K G (Ws s)) (Xc : Finset (G → K)) : Prop :=
  ∀ χ : G → K, χ ∈ Xc ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ

def NearConstantMultiplicities (τ : ∀ s, Representation K G (Ws s)) (P1 : Formalism.IndefR.IndefiniteEpsilonOperator.Pair G K) (nbar de : ℝ) : Prop :=
  ∀ s, (1 - de) * nbar ≤ (Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) P1 : ℝ) ∧ (Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) P1 : ℝ) ≤ (1 + de) * nbar

end Group

end Formalism.IndefR.CxPass
