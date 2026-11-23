module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Topology.Sheaves.Presheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.Algebra.Hom.Rat

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.DiffBaseChange

theorem sum_emb_mul_dual {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ E) (σ τ : E →ₐ[ℚ] ℂ) [Decidable (σ = τ)] :
    ∑ i, σ (b i) * τ (b.traceDual i) = if σ = τ then 1 else 0 := by
  classical
  have hli := Fintype.linearIndependent_iff.1 (linearIndependent_algHom_toLinearMap ℚ E ℂ)
    (fun σ : E →ₐ[ℚ] ℂ => (∑ i, σ (b i) * τ (b.traceDual i)) - if σ = τ then 1 else 0) ?_ σ
  · convert sub_eq_zero.1 hli
  · ext x
    have h1 : τ x = ∑ i, (∑ σ : E →ₐ[ℚ] ℂ, σ (x * b i)) * τ (b.traceDual i) := by
      conv_lhs => rw [← b.traceDual.sum_repr x]

      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, τ.commutes, b.traceDual_repr_apply, Algebra.traceForm_apply,
        ← trace_eq_sum_embeddings ℂ]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
      smul_eq_mul, LinearMap.zero_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h1, sub_eq_zero]
    simp only [Finset.sum_mul, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem eq_sum_trace_mul_dual {F E L : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field L] [NumberField L]
    [Algebra F L] (j : E →+* L) (u : L →+* ℂ)
    (hgen : ∀ ρ : L →+* ℂ, (∀ x : F, ρ (algebraMap F L x) = u (algebraMap F L x)) →
      (∀ x : E, ρ (j x) = u (j x)) → ρ = u)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (y : L) :
    y = ∑ i, algebraMap F L (Algebra.trace F L (y * j (b i))) * j (b.traceDual i) := by
  classical
  letI : Algebra L ℂ := u.toAlgebra
  letI : Algebra F ℂ := (u.comp (algebraMap F L)).toAlgebra
  haveI : IsScalarTower F L ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply u.injective

  rw [map_sum]
  have h1 : ∀ i, u (algebraMap F L (Algebra.trace F L (y * j (b i))) * j (b.traceDual i)) =
      ∑ ρ : L →ₐ[F] ℂ, ρ y * (ρ (j (b i)) * u (j (b.traceDual i))) := by
    intro i
    have := trace_eq_sum_embeddings (K := F) ℂ (x := y * j (b i))
    rw [map_mul]
    change algebraMap F ℂ _ * _ = _
    rw [this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => by rw [map_mul, mul_assoc]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ ρ : L →ₐ[F] ℂ, ∑ i, ρ y * (ρ (j (b i)) * u (j (b.traceDual i))) =
      if ρ = IsScalarTower.toAlgHom F L ℂ then u y else 0 := by
    intro ρ
    rw [← Finset.mul_sum]
    have := sum_emb_mul_dual b ((ρ : L →+* ℂ).comp j).toRatAlgHom (u.comp j).toRatAlgHom
    simp only [RingHom.toRatAlgHom_apply, RingHom.comp_apply, RingHom.coe_coe] at this
    rw [this]
    by_cases h : ρ = IsScalarTower.toAlgHom F L ℂ
    · subst h
      rw [if_pos rfl, if_pos (by rfl), mul_one]
      rfl
    · rw [if_neg h, if_neg, mul_zero]
      intro h'
      apply h
      have := hgen (ρ : L →+* ℂ) (fun x => ρ.commutes x) (fun x => DFunLike.congr_fun h' x)
      ext x
      exact DFunLike.congr_fun this x
  simp [h2]

theorem map_different_le {F E L : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field L] [NumberField L]
    [Algebra F L] (j : E →+* L) (u : L →+* ℂ)
    (hgen : ∀ ρ : L →+* ℂ, (∀ x : F, ρ (algebraMap F L x) = u (algebraMap F L x)) →
      (∀ x : E, ρ (j x) = u (j x)) → ρ = u) :
    (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom j) ≤ differentIdeal (𝓞 F) (𝓞 L) := by
  classical
  rw [Ideal.map_le_iff_le_comap]
  intro δ hδ
  rw [Ideal.mem_comap]
  have h1 : algebraMap (𝓞 E) E δ ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) :=
    (IsLocalization.mem_coeSubmodule _ _).2 ⟨δ, hδ, rfl⟩
  rw [coeSubmodule_differentIdeal ℤ ℚ (𝓞 E), Submodule.mem_div_iff_forall_mul_mem] at h1
  have hb : ∀ i, (integralBasis E).traceDual i ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    intro i
    rw [← Submodule.restrictScalars_mem ℤ, Submodule.traceDual_span_of_basis ℤ _ (integralBasis E)]
    · exact Submodule.subset_span ⟨i, rfl⟩
    · ext x
      rw [mem_span_integralBasis, Submodule.restrictScalars_mem, Submodule.mem_one]
      rfl
  suffices h : algebraMap (𝓞 L) L (RingOfIntegers.mapRingHom j δ) ∈
      IsLocalization.coeSubmodule L (differentIdeal (𝓞 F) (𝓞 L)) by
    obtain ⟨y, hy, hyx⟩ := (IsLocalization.mem_coeSubmodule _ _).1 h
    obtain rfl := IsFractionRing.injective (𝓞 L) L hyx
    exact hy
  rw [coeSubmodule_differentIdeal (𝓞 F) F (𝓞 L), Submodule.mem_div_iff_forall_mul_mem]
  intro y hy
  rw [eq_sum_trace_mul_dual (F := F) j u hgen (integralBasis E) y, Finset.mul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (h1 _ (hb i))
  obtain ⟨t, ht⟩ := Submodule.mem_traceDual.1 hy (j (integralBasis E i))
    (Submodule.mem_one.2 ⟨RingOfIntegers.mapRingHom j (RingOfIntegers.basis E i), by
      rw [integralBasis_apply]; rfl⟩)
  rw [Algebra.traceForm_apply] at ht
  refine Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 L) t * RingOfIntegers.mapRingHom j c, ?_⟩
  have e1 : ∀ z : 𝓞 E, algebraMap (𝓞 L) L (RingOfIntegers.mapRingHom j z) = j (algebraMap (𝓞 E) E z) := fun _ => rfl
  rw [map_mul, e1, e1, hc, map_mul, ← ht, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  ring

theorem map_different_le_sup (F F' : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField ↥(F ⊔ F')] :
    letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
    (differentIdeal ℤ (𝓞 F')).map
      (RingOfIntegers.mapRingHom (IntermediateField.inclusion (le_sup_right : F' ≤ F ⊔ F')).toRingHom) ≤
      differentIdeal (𝓞 F) (𝓞 ↥(F ⊔ F')) := by
  letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  refine map_different_le (F := F) _ (F ⊔ F').val.toRingHom fun ρ h1 h2 => ?_
  ext ⟨x, hx⟩
  change ρ ⟨x, hx⟩ = x
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact h1 ⟨x, hx⟩
    · exact h2 ⟨x, hx⟩
  | algebraMap q => exact h1 (algebraMap ℚ F q)
  | add x y hx hy ihx ihy => exact (map_add ρ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [ihx, ihy])
  | inv x hx ih => exact (map_inv₀ ρ ⟨x, hx⟩).trans (by rw [ih])
  | mul x y hx hy ihx ihy => exact (map_mul ρ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [ihx, ihy])

end GlobalTheory.DiffBaseChange
