module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.CoefModB

@[expose] public section

open MvPolynomial NumberField
open Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators

section Numbers

variable {n : ℕ}

def Interlace (lam : DomWeight (n + 1)) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, lam.w i.succ ≤ sg.w i ∧ sg.w i ≤ lam.w i.castSucc

def EqualLast (lam : DomWeight (n + 1)) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, i.val + 1 = n → sg.w i = lam.w (Fin.last n)

def dZero (lam : DomWeight (n + 1)) (sg : DomWeight n) : ℤ := ∑ i : Fin n, (sg.w i - lam.w i.succ)

def rangeSet (lam : DomWeight (n + 1)) (sg : DomWeight n) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam.w i.succ) (min (lam.w i.castSucc) (lam.w i.succ + dZero lam sg))

end Numbers

section Capelli

variable (K : Type) [Field K] (n : ℕ)

variable {n}

end Capelli

section Tensors

variable (K : Type) [Field K] {n : ℕ}

variable {ι : Type} [Fintype ι]

end Tensors

section Maps

variable (K : Type) [Field K] {n : ℕ} {ι : Type} [Fintype ι]

instance finiteVV (lam : ι → DomWeight n) : Module.Finite K (VV K lam) := Module.Finite.of_basis (bVV K lam)

variable [CharZero K]

variable {K}

end Maps

section Statement

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators
