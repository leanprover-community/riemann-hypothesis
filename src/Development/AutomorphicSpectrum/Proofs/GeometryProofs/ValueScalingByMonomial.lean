module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartTwist

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

theorem prod_pow_toNat {K : Type} [Fintype K] {F : Type} [Field F] (u : K → F) (hu : ∀ k, u k ≠ 0) (a : K → ℤ) :
    ∏ k, u k ^ (a k).toNat = (∏ k, u k ^ a k) * ∏ k, u k ^ (-a k).toNat := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h := hu k
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h]
  congr 1
  omega

theorem hasVal_twist : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω]
    (y : (Σ k, J k) → Ω) (L : Type) [Field L] (z : (Σ k, J k) → L) (a : K → ℤ) (s : Ω) (w : L),
    Small.HasVal y (0 : K → ℤ) s z w → w ≠ 0 → ∀ c : (k : K) → J k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (∀ k, z ⟨k, c k⟩ ≠ 0) → ∃ v : L, v ≠ 0 ∧ Small.HasVal y a (s * ∏ k, y ⟨k, c k⟩ ^ a k) z v := by
  intro K _ J _ Ω _ y L _ z a s w h hw c hy hz
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hn, ev⟩ := h
  have hM : ∀ m : K → ℕ, aeval z (cMon c m) ≠ 0 := fun m => by
    rw [aeval_cMon]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
  refine ⟨w * ∏ k, z ⟨k, c k⟩ ^ a k,
    mul_ne_zero hw (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hz k)),
    dg + fun k => (a k).toNat, dh + fun k => (-a k).toNat,
    g * cMon c fun k => (a k).toNat, f * cMon c fun k => (-a k).toNat,
    homog_mul hg (homog_cMon c _), homog_mul hf (homog_cMon c _), fun k => ?_, ?_,
    by rw [map_mul]; exact mul_ne_zero hn (hM _), ?_⟩
  · have h1 := hd k
    simp only [Pi.add_apply, Pi.zero_apply] at h1 ⊢
    push_cast
    omega
  · rw [map_mul, map_mul, aeval_cMon, aeval_cMon, e,
      prod_pow_toNat (fun k => y ⟨k, c k⟩) hy a]
    ring
  · rw [map_mul, map_mul, aeval_cMon, aeval_cMon, ev,
      prod_pow_toNat (fun k => z ⟨k, c k⟩) hz a]
    ring

end GlobalTheory.CompanionTheory.Ar.ChartTwist
