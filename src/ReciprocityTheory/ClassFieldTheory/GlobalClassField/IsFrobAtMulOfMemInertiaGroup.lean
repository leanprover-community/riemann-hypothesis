module

public import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.NumberTheory.RamificationInertia.Galois
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

noncomputable section

open NumberField IsDedekindDomain Neutral.B1
open scoped Pointwise

namespace ReciprocityTheory.DiscreteGroups.GlobalClassField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def inertiaGroup (Q : Ideal (𝓞 L)) : Subgroup (L ≃ₐ[K] L) :=
  (Q.toAddSubgroup.inertia (𝓞 L ≃ₐ[𝓞 K] 𝓞 L)).comap (galRestrict (𝓞 K) K L (𝓞 L)).toMonoidHom

variable {K L}

theorem mem_inertiaGroup {Q : Ideal (𝓞 L)} {τ : L ≃ₐ[K] L} :
    τ ∈ inertiaGroup K L Q ↔ ∀ x : 𝓞 L, galRestrict (𝓞 K) K L (𝓞 L) τ x - x ∈ Q :=
  Iff.rfl

theorem galRestrict_apply_eq_smul (τ : L ≃ₐ[K] L) (x : 𝓞 L) :
    galRestrict (𝓞 K) K L (𝓞 L) τ x = τ • x := by
  apply RingOfIntegers.ext
  exact algebraMap_galRestrict_apply (𝓞 K) τ x

theorem inertiaGroup_eq_inertia (Q : Ideal (𝓞 L)) :
    inertiaGroup K L Q = Q.toAddSubgroup.inertia (L ≃ₐ[K] L) := by
  ext τ
  rw [mem_inertiaGroup]
  simp only [galRestrict_apply_eq_smul]
  rfl

theorem isFrobAt_iff_forall (τ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) :
    IsFrobAt K L τ Q ↔ ∀ x : 𝓞 L, τ • x - x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ∈ Q := by
  simp only [← galRestrict_apply_eq_smul]
  rfl

theorem under_smul_ideal (σ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) : (σ • Q).under (𝓞 K) = Q.under (𝓞 K) := by
  ext a
  rw [Ideal.mem_under, Ideal.mem_under, Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  have : σ⁻¹ • (algebraMap (𝓞 K) (𝓞 L) a) = algebraMap (𝓞 K) (𝓞 L) a := by
    rw [← galRestrict_apply_eq_smul, AlgEquiv.commutes]
  exact iff_of_eq (congrArg (· ∈ Q) this)

theorem isFrobAt_smul (σ τ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) (h : IsFrobAt K L τ Q) :
    IsFrobAt K L (σ * τ * σ⁻¹) (σ • Q) := by
  rw [isFrobAt_iff_forall] at h ⊢
  intro x
  rw [under_smul_ideal, Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  simpa [smul_sub, mul_smul] using h (σ⁻¹ • x)

section Over

variable (v : HeightOneSpectrum (𝓞 K)) (Q Q' : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]

theorem exists_liesOver (L : Type) [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver v.asIdeal := by
  obtain ⟨⟨Q, h1, h2⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
  exact ⟨Q, h1, h2⟩

theorem isFrobAt_unique (hv : IsUnramifiedIn K v L) (τ τ' : L ≃ₐ[K] L) (h : IsFrobAt K L τ Q)
    (h' : IsFrobAt K L τ' Q) : τ = τ' := by
  have : Algebra.IsUnramifiedAt (𝓞 K) Q :=
    Ideal.ramificationIdx_eq_one_iff.mp (hv Q inferInstance inferInstance)
  have e := h.eq_of_isUnramifiedAt h' Q.primeCompl_le_nonZeroDivisors
  apply (galRestrict (𝓞 K) K L (𝓞 L)).injective
  exact AlgEquiv.ext fun x => DFunLike.congr_fun e x

variable [IsGalois K L]

theorem exists_smul_eq [Q'.IsPrime] [Q'.LiesOver v.asIdeal] : ∃ σ : L ≃ₐ[K] L, σ • Q = Q' :=
  Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal Q Q' (L ≃ₐ[K] L)

include v in
theorem card_inertiaGroup : Nat.card (inertiaGroup K L Q) = Q.ramificationIdx (𝓞 K) := by
  rw [inertiaGroup_eq_inertia]
  exact (Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal Q).trans
    (Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (L ≃ₐ[K] L))

theorem isFrobAt_of_comm (hc : ∀ a b : L ≃ₐ[K] L, a * b = b * a) [Q'.IsPrime]
    [Q'.LiesOver v.asIdeal] (τ : L ≃ₐ[K] L) (h : IsFrobAt K L τ Q) : IsFrobAt K L τ Q' := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq v Q Q'
  have := isFrobAt_smul σ τ Q h
  rwa [hc σ τ, mul_inv_cancel_right] at this

end Over

end ReciprocityTheory.DiscreteGroups.GlobalClassField
