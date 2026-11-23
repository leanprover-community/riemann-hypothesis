module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.UnitNorm

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

def GapAndSizeRange (D : D7) (Cg Cq : ℝ) (L : LocBessel D.R.k D.R.rS) (p : ℕ) : Prop :=
  AllGaps L.lam (Cg * p * ((2 * D.R.rS + 2 : ℕ) : ℝ)) ∧
    (((D.R.rS + 1) * (p + D.R.rS + 2) : ℕ) : ℝ) ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u L.lam

def InBig {k r : ℕ} (L : LocBessel k r) (q : (Fin r → ℂ) × ℂ) : Prop :=
  (∀ i, q.1 i ≠ 0) ∧ Tz k r L.z * Tz k r L.z' < Complex.normSq q.2

end PI.UnitNorm

namespace PI

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.UnitNorm

def UnitNorm (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L L.lam ka b κ → GapAndSizeRange D Cg Cq L p →
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ' : Mx D.R.k D.R.rS → (H →L[ℂ] H)), IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) σ' →
    ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH σ' f' →
      (∃ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q ∧ L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) ≠ 0) →
      ∃ f'' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH σ' f'' ∧ jNorm2 L f'' μsec ≠ 0 ∧ jNorm2 L f'' μsec ≠ ⊤

end PI
