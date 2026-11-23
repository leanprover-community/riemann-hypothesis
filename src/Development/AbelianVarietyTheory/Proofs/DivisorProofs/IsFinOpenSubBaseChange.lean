module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory


open Matrix NumberField in
open scoped TensorProduct Classical in
theorem _root_.GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral (K : Type) [Field K] [NumberField K]
    (d D : ℕ) (B : ℝ) (hD : 0 < D) :
    {P : Polynomial K | P.Monic ∧ P.natDegree ≤ d ∧ ∀ k, IsIntegral ℤ ((D : K) * P.coeff k) ∧
      ∀ φ : K →+* ℂ, ‖φ (P.coeff k)‖ ≤ B}.Finite := by
  have hT : {c : K | IsIntegral ℤ ((D : K) * c) ∧ ∀ φ : K →+* ℂ, ‖φ c‖ ≤ B}.Finite := by
    have h := NumberField.Embeddings.finite_of_norm_le K ℂ ((D : ℝ) * B)
    refine (h.image fun x => x / (D : K)).subset ?_
    intro c hc
    refine ⟨(D : K) * c, ⟨hc.1, fun φ => ?_⟩, ?_⟩
    · have := mul_le_mul_of_nonneg_left (hc.2 φ) (Nat.cast_nonneg (α := ℝ) D)
      simpa [norm_mul] using this
    · have hD' : (D : K) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
      field_simp
  have hF : (Set.pi Set.univ fun _ : Fin (d + 1) =>
      {c : K | IsIntegral ℤ ((D : K) * c) ∧ ∀ φ : K →+* ℂ, ‖φ c‖ ≤ B}).Finite :=
    Set.Finite.pi fun _ => hT
  refine Set.Finite.of_finite_image
    (f := fun P : Polynomial K => fun i : Fin (d + 1) => P.coeff i) (hF.subset ?_) ?_
  · rintro _ ⟨P, hP, rfl⟩ i -
    exact ⟨(hP.2.2 i).1, (hP.2.2 i).2⟩
  · intro P hP Q hQ hPQ
    ext n
    by_cases hn : n ≤ d
    · exact congrFun hPQ ⟨n, Nat.lt_succ_of_le hn⟩
    · push_neg at hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.2.1.trans_lt hn),
        Polynomial.coeff_eq_zero_of_natDegree_lt (hQ.2.1.trans_lt hn)]

end GlobalTheory
