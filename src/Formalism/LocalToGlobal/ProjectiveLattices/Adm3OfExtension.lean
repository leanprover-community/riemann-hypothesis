module

public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (i : ℕ)
  (η : (recB h.toLawsCore).Cusp j (wEt D j i))

def EtCusp : Prop := η ≠ 0 ∧ (recPJ h j hj).NonZeroComp _ η

def EtVal : Prop :=
  ∀ la (y : (recPJ h j hj).Pt la),
    ((2 * i * (recPJ h j hj).phiC la y : ℝ) : EReal) ≤ (recPJ h j hj).vAt la y ((recPJ h j hj).inc _ η)

def EtSup (P : ℝ) : Prop := ∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ η) / i ≤ P

variable (P : ℝ) (Arch : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop)

def ETEx : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j < D.R.m), ∃ i : ℕ, 0 < i ∧ ∃ η : (recB h.toLawsCore).Cusp j (wEt D j i),
    EtCusp h j ⟨h1, h2.le⟩ i η ∧ EtVal h j ⟨h1, h2.le⟩ i η ∧ EtSup h j i η P ∧ Arch j i η

variable {h P Arch}

end Formalism.L2.Pj
