module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallySubMemPow
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.OCrCont

open Filter Topology

theorem galOCr_sub_smul_eventually {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    (r : OCr l O) (m : ℕ) :
    ∀ᶠ h in nhds (1 : GQ l), ∃ w : OCr l O, galOCr O h r - r = ((l : O) ^ m) • w := by
  induction r using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun h => ⟨0, by simp⟩
  | tmul o a =>
    filter_upwards [GlobalTheory.AcrisGal.galC_sub_dvd_mem_nhds l a m] with h hh
    obtain ⟨c, hc⟩ := hh
    refine ⟨o ⊗ₜ c, ?_⟩
    have e1 : galOCr O h (o ⊗ₜ[ℤ_[l]] a) = o ⊗ₜ galC h a := rfl
    rw [e1, ← TensorProduct.tmul_sub, hc, TensorProduct.smul_tmul', smul_eq_mul]
    have e2 : ((l : Per.Acris l) ^ m * c) = ((l : ℤ_[l]) ^ m) • c := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [e2, ← TensorProduct.smul_tmul, Algebra.smul_def, map_pow, map_natCast]
  | add x y hx hy =>
    filter_upwards [hx, hy] with h ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    rw [map_add (f := _), smul_add, ← hu, ← hv]; abel

theorem twact_sub_smul_eventually : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G]
    (s : G →* GQ l), Continuous s → ∀ (T : LocLat G ℚ_[l] K O),
    (∀ t ∈ T.L.T, ∀ m : ℕ, ∀ᶠ g in nhds (1 : G), ∃ t' ∈ T.L.T, T.ρ g t - t = ((l : O) ^ m) • t') →
    ∀ (β : TW (OCr l O) T) (m : ℕ), ∀ᶠ g in nhds (1 : G), ∃ γ : TW (OCr l O) T,
      TWact (galOCr O (s g)) T g β - β = ((l : O) ^ m) • γ := by
  intro l _ O K _ _ _ _ _ _ G _ _ s hs T hT β m
  have hts : Tendsto s (nhds 1) (nhds 1) := by
    simpa [map_one] using hs.tendsto (1 : G)
  induction β using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun g => ⟨0, by simp⟩
  | tmul r t =>
    filter_upwards [hts.eventually (galOCr_sub_smul_eventually r m), hT t.1 t.2 m] with g ⟨w, hw⟩ ⟨t', ht', htt⟩
    refine ⟨w ⊗ₜ T.actT g t + r ⊗ₜ ⟨t', ht'⟩, ?_⟩
    have e1 : TWact (galOCr O (s g)) T g (r ⊗ₜ[O] t) = galOCr O (s g) r ⊗ₜ T.actT g t := rfl
    have e2 : T.actT g t - t = ((l : O) ^ m) • (⟨t', ht'⟩ : ↥T.L.T) := Subtype.ext (by
      rw [Submodule.coe_sub, Submodule.coe_smul]; exact htt)
    have e3 : galOCr O (s g) r ⊗ₜ[O] T.actT g t - r ⊗ₜ[O] t
        = (galOCr O (s g) r - r) ⊗ₜ[O] T.actT g t + r ⊗ₜ[O] (T.actT g t - t) := by
      rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
    rw [e1, e3, hw, e2, smul_add, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  | add x y hx hy =>
    filter_upwards [hx, hy] with g ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    rw [map_add (f := _), smul_add, ← hu, ← hv]; abel

end GlobalTheory.OCrCont
