module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem exists_ringEquiv_apply_eq_mul_of_transcendental {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsAlgClosed L] {x : L} (hx : Transcendental K x) {c : K} (hc : c ≠ 0) :
    ∃ σ : L ≃+* L, (∀ k : K, σ (algebraMap K L k) = algebraMap K L k) ∧
      σ x = algebraMap K L c * x := by
  have h1 : AlgebraicIndepOn K id ({x} : Set L) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let e : MvPolynomial s K ≃ₐ[K] MvPolynomial s K :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => c • MvPolynomial.X i)
      (MvPolynomial.aeval fun i => c⁻¹ • MvPolynomial.X i)
      (by ext i : 1; simp [smul_smul, hc]) (by ext i : 1; simp [smul_smul, hc])
  obtain ⟨σ, hσ⟩ :=
    GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis hs hs e.toRingEquiv
  refine ⟨σ, fun k => ?_, ?_⟩
  · simpa [e] using hσ (MvPolynomial.C k)
  · have := hσ (MvPolynomial.X ⟨x, hxs rfl⟩)
    rw [← Algebra.smul_def]
    simpa [e] using this

theorem mem_algebraicClosure_of_norm_le :
    ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (x : ℂ) (B : ℝ),
      (∀ ι' : ℂ ≃+* ℂ_[q], (∀ a : algebraicClosure ℚ ℂ, ι' (a : ℂ) = ι (a : ℂ)) → ‖ι' x‖ ≤ B) →
        x ∈ algebraicClosure ℚ ℂ := by
  intro q hq ι x B h
  by_contra hx
  rw [mem_algebraicClosure_iff] at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx isAlgebraic_zero
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hx' : Transcendental (algebraicClosure ℚ ℂ) x := fun ha =>
    hx (ha.restrictScalars ℚ)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
  have hq0 : q ≠ 0 := hq.out.ne_zero
  have hpos : 0 < ‖ι x‖ := by simpa using hx0
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (B / ‖ι x‖) hq1
  have hc : ((q : algebraicClosure ℚ ℂ) ^ j)⁻¹ ≠ 0 := by
    simp [hq0]
  obtain ⟨σ, hσ, hσx⟩ := exists_ringEquiv_apply_eq_mul_of_transcendental hx' hc
  have h2 := h (σ.trans ι) fun a => by
    have := hσ a
    simp only [RingEquiv.trans_apply]
    exact congrArg ι this
  have hn : ‖(q : ℂ_[q])‖ = (q : ℝ)⁻¹ := by
    have h3 : (q : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] (q : ℚ_[q]) := by simp
    rw [h3, norm_algebraMap', Padic.norm_p]
  rw [RingEquiv.trans_apply, hσx] at h2
  simp only [map_mul, map_inv₀, map_pow, map_natCast, norm_mul, norm_inv, norm_pow, hn,
    inv_pow, inv_inv] at h2
  rw [div_lt_iff₀ hpos] at hj
  linarith

end GlobalTheory.MomOne
