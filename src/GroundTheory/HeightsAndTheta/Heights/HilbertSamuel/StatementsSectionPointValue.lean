module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsBoundedAtOfIsBoundedH
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionPointValue.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι),
    IsRelevant (mCoordIdeal y) → ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} →
    ∃ w : ∀ n : ℕ, chartLat y A.a n →+ (((Σ k, ι k) → ℂ) → ℂ),
      (∀ (n : ℕ) (s : chartLat y A.a n), ContinuousOn (w n s) (mcPts (mCoordIdeal y))) ∧
      (∀ (n : ℕ) (s : chartLat y A.a n) (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
        IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + n * A.a k) →
        aeval y g = (s : Ω) * aeval y h → z ∈ mcPts (mCoordIdeal y) →
        eval z (map (Int.castRingHom ℂ) g) =
          w n s z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) ∧
      (∀ (n : ℕ) (s : chartLat y A.a n), ∀ z ∈ mcPts (mCoordIdeal y),
        secNormAt y A n (s : Ω) z = ‖w n s z‖) ∧
      (∀ (n k : ℕ) (s : chartLat y A.a n) (t : chartLat y A.a k) (st : chartLat y A.a (n + k)),
        (st : Ω) = s * t → ∀ z ∈ mcPts (mCoordIdeal y), w (n + k) st z = w n s z * w k t z) ∧
      ∀ (n r : ℕ) (s : Fin r → chartLat y A.a n),
        ∃ (e e' : K → ℕ) (h : MRing ι) (g : Fin r → MRing ι),
          IsMultiHomog h e' ∧ (∀ i, IsMultiHomog (g i) e) ∧ (∀ k, (e k : ℤ) = e' k + n * A.a k) ∧
          aeval y h ≠ 0 ∧ ∀ i, aeval y (g i) = (s i : Ω) * aeval y h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
