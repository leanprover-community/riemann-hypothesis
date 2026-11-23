module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqOnMirabolicFin
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Topology

noncomputable section

namespace GlobalTheory.JSW.KirFin

theorem exists_charSum_eq_on_compact : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 →
    ∀ {ι : Type} [Fintype ι] (K : Set (ι → F)), IsCompact K → ∀ Φ : (ι → F) → ℂ, IsLocallyConstant Φ →
    ∃ T : (ι → F) →₀ ℂ, ∀ r ∈ K, (T.sum fun v c => c * ψ (r ⬝ᵥ v)) = Φ r := by
  intro F _ ψ hψ hψ1 ι _ K hK Φ hΦ
  classical
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ1 (AddChar.ext _ _ h)
  let χ : (ι → F) → (ι → F) → ℂ := fun v r => ψ (r ⬝ᵥ v)
  let S : Set ((ι → F) → ℂ) := Set.range χ
  have hχmul : ∀ v w, χ v * χ w = χ (v + w) := by
    intro v w; funext r; simp [χ, dotProduct_add, AddChar.map_add_eq_mul]
  have hχ0 : χ 0 = 1 := by funext r; simp [χ]
  have hlc : ∀ v, IsLocallyConstant (χ v) := fun v =>
    hψ.comp_continuous (continuous_id.dotProduct continuous_const)
  let L : Subalgebra ℂ ((ι → F) → ℂ) :=
    { carrier := {a | IsLocallyConstant a}
      mul_mem' := fun ha hb => IsLocallyConstant.mul ha hb
      add_mem' := fun ha hb => IsLocallyConstant.add ha hb
      algebraMap_mem' := fun c => IsLocallyConstant.const _ }
  let A := Algebra.adjoin ℂ S
  have hAL : A ≤ L := Algebra.adjoin_le (by rintro _ ⟨v, rfl⟩; exact hlc v)
  have hAspan : ∀ a ∈ A, a ∈ Submodule.span ℂ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.subset_span hx
    | algebraMap c =>
      have : algebraMap ℂ ((ι → F) → ℂ) c = c • χ 0 := by
        rw [hχ0, Algebra.algebraMap_eq_smul_one]
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
      exact ⟨v + w, (hχmul v w).symm⟩
  let ρ : ((ι → F) → ℂ) →ₐ[ℂ] (K → ℂ) :=
    { toFun := fun a x => a x.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨a, ha, e⟩ := mem_of_separates (A.map ρ)
    (by rintro _ ⟨a, ha, rfl⟩; exact (hAL ha).comp_continuous continuous_subtype_val)
    (by
      intro x y hxy
      obtain ⟨i, hi⟩ := Function.ne_iff.1 (Subtype.coe_ne_coe.2 hxy)
      refine ⟨ρ (χ (Pi.single i (t / (x.1 i - y.1 i)))), ⟨_, Algebra.subset_adjoin ⟨_, rfl⟩, rfl⟩,
        fun h => ht ?_⟩
      change ψ (x.1 ⬝ᵥ _) = ψ (y.1 ⬝ᵥ _) at h
      rw [dotProduct_single, dotProduct_single] at h
      have h2 : x.1 i * (t / (x.1 i - y.1 i)) = t + y.1 i * (t / (x.1 i - y.1 i)) := by
        have := sub_ne_zero.2 hi
        field_simp
        ring
      rw [h2, AddChar.map_add_eq_mul] at h
      exact (mul_eq_right₀ (ψ.val_isUnit _).ne_zero).1 h)
    (hΦ.comp_continuous continuous_subtype_val)
  obtain ⟨T, hT⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hAspan a ha)
  refine ⟨T, fun r hr => ?_⟩
  have h1 := congrFun e ⟨r, hr⟩
  change a r = Φ r at h1
  rw [← h1, ← hT]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, χ]

end GlobalTheory.JSW.KirFin
