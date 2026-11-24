module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CollapseExponent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

def TLset (j : Fin D.J) (m : Fin D.r) : Finset D.ML :=
  (D.LLj j).image D.mb ∪ (univ.filter fun m' : Fin D.r => m < m').image fun m' => D.mlab (j, m')

def YPset (j : Fin D.J) (m : Fin D.r) : Finset D.ML :=
  (D.LLj j).image D.mb ∪ (univ.filter fun m' : Fin D.r => m < m').image fun m' => D.mtp (j, m')

def SegL (j : Fin D.J) (i : D.ML) : Prop :=
  (∃ b, D.seg b = j ∧ i = D.mb b) ∨ (∃ m, i = D.mlab (j, m)) ∨ (∃ m, i = D.mtp (j, m))

def PreE (j : Fin D.J) (ζ : D.EM) : Prop :=
  (∀ b, D.seg b = j → ldeg ζ (D.mb b) = D.dB b) ∧ (∀ m, ldeg ζ (D.mlab (j, m)) = D.dT (j, m)) ∧
  (∀ m a, ζ (D.mtp (j, m), a) = 0)

def PostE (j : Fin D.J) (ζ : D.EM) : Prop :=
  (∀ b, D.seg b = j → ldeg ζ (D.mb b) = D.dB b) ∧
  (∀ m, ldeg ζ (D.mlab (j, m)) + ldeg ζ (D.mtp (j, m)) = D.dT (j, m)) ∧
  (∀ m, ldeg ζ (D.mtp (j, m)) ≤ D.dLL j) ∧
  (∀ m : Fin D.r, m.val = 0 → ∀ a, ζ (D.mtp (j, m), a) = 0)

end TwistData

def SegStep (K : Type) [Field K] [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ) : Prop :=
  DVRHyp v p → ∀ D : TwistData K, 0 < D.r → 0 < D.J → ∀ j : Fin D.J,
    ∃ Th : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K,
      (∀ ζ : D.EM, D.PreE j ζ → Integral v (Th (monomial ζ 1))) ∧
      (∀ ζ : D.EM, D.PreE j ζ → D.ph p (Th (monomial ζ 1)) = D.ph p (monomial ζ 1)) ∧
      (∀ ζ : D.EM, D.PreE j ζ → ∀ ζ' ∈ (Th (monomial ζ 1)).support,
        D.PostE j ζ' ∧ ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a)) ∧
      (∀ Z : MvPolynomial (D.ML × Fin D.r) K, Integral v Z → (∀ ζ ∈ Z.support, D.PreE j ζ) →
        ∀ (m : Fin D.r) (θ : ℝ), m.val + 2 ≤ D.r →
          vala D.msg (D.TLset j m) θ Z → vala D.msg (D.YPset j m) θ (Th Z)) ∧
      (∀ S : Finset D.ML, (∀ i ∈ S, ¬ D.SegL j i) → ∀ Z : MvPolynomial (D.ML × Fin D.r) K,
        valS D.msg S Z ≤ valS D.msg S (Th Z))

end Formalism.MainNotions.PlaneGram
