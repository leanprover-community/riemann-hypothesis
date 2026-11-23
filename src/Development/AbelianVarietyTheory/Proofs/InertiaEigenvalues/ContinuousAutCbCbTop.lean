module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



noncomputable section
open Filter Topology

namespace GlobalTheory.WeakClosed

theorem continuous_frac_act {A K G : Type} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [TopologicalSpace G] (τ : G → (A ≃+* A))
    (σ : G → (K ≃+* K)) (hσ : ∀ g a, σ g (algebraMap A K a) = algebraMap A K (τ g a))
    (ho : ∀ (x a : A) (g₀ : G), a ≠ 0 → ∀ᶠ g in 𝓝 g₀, ¬ (τ g x - τ g₀ x ∣ a)) :
    letI : Valued K (ValuationRing.ValueGroup A K) := Valued.mk' (ValuationRing.valuation A K)
    Continuous fun p : G × K => σ p.1 p.2 := by
  letI V : Valued K (ValuationRing.ValueGroup A K) := Valued.mk' (ValuationRing.valuation A K)
  have hle : ∀ x y : K, Valued.v x ≤ Valued.v y ↔ ∃ c : A, algebraMap A K c * y = x := by
    intro x y
    change (∃ c : A, c • y = x) ↔ _
    simp only [Algebra.smul_def]
  have hinj := IsFractionRing.injective A K
  refine GlobalTheory.WeakTop.continuous_act_of_orbits σ ?_ ?_
  · intro g x y
    simp only [← not_le, hle]
    rintro h ⟨c, hc⟩
    refine h ⟨(τ g).symm c, (σ g).injective ?_⟩
    rw [map_mul, hσ, RingEquiv.apply_symm_apply, hc]
  · have hA : ∀ x : A, Continuous fun g => σ g (algebraMap A K x) := by
      intro x
      rw [continuous_iff_continuousAt]
      intro g₀ s hs
      obtain ⟨c, hc, hs⟩ := GlobalTheory.WeakTop.mem_nhds_iff_lt.1 hs
      obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective A c
      have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hc
      rw [mem_map]
      filter_upwards [ho x a g₀ ha] with g hg
      apply hs
      change Valued.v (σ g (algebraMap A K x) - σ g₀ (algebraMap A K x)) < _
      rw [← not_le, hle, hσ, hσ, ← map_sub]
      rintro ⟨e, he⟩
      refine hg ⟨e * d, hinj ?_⟩
      rw [eq_div_iff hd0] at he
      rw [← he, map_mul, map_mul]
      ring
    intro x
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective A x
    have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    simp only [map_div₀]
    exact (hA a).div (hA d) fun g => by simpa using hd0

theorem continuous_autCb_cbTop : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P),
    letI := cbTop l; Continuous fun q : GQ l × Cb l => autCb l (AI.actT q.1) q.2 := by
  intro l _ P AI
  refine continuous_frac_act (A := OCb l) (fun g => AI.actT g) (fun g => autCb l (AI.actT g))
    (fun g a => autCb_alg l _ a) fun x a g₀ ha => ?_
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n a ≠ 0 := by
    by_contra! h
    refine ha (Perfection.ext fun n => ?_)
    change PreTilt.coeff n a = PreTilt.coeff n 0
    rw [h, map_zero]
  filter_upwards [GlobalTheory.WeakTop.eventually_coeff_eq AI x n g₀] with g hg
  rintro ⟨c, hc⟩
  apply hn
  rw [hc, map_mul, map_sub, hg, sub_self, zero_mul]

end GlobalTheory.WeakClosed
