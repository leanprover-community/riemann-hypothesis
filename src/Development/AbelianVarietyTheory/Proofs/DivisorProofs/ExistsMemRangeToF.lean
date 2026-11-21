import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantEuclideanComplex
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel

noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.OneFormTest

section Abstract

variable {K : Type} [Field K] {σ : K →+* ℂ} {E : Type} [AddCommGroup E] [Module ℂ E]
  {V : Type} [AddCommGroup V] [Module K V]

theorem exists_coord {I : Type} (ψ : I → E →ₗ[ℂ] ℂ) (ι : V →ₛₗ[σ] E) (h : ∀ x a, ∃ z : K, σ z = ψ a (ι x)) :
    ∃ f : V →ₗ[K] (I → K), ∀ x a, σ (f x a) = ψ a (ι x) := by
  choose f hf using h
  refine ⟨⟨⟨f, fun x y => funext fun a => σ.injective ?_⟩, fun c x => funext fun a => σ.injective ?_⟩, hf⟩
  · rw [Pi.add_apply, map_add, hf, hf, hf, map_add, map_add]
  · simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, hf, map_smulₛₗ]



theorem exists_orth [FiniteDimensional K V] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : V →ₛₗ[σ] H)
    (hj : Function.Injective j) (hr : ∀ x y, ∃ z : K, σ z = ⟪j x, j y⟫_ℂ) (U : Submodule K V) (x : V) :
    ∃ k ∈ U, ∀ k' ∈ U, ⟪j k', j (x - k)⟫_ℂ = 0 := by
  let b := Module.finBasis K U
  obtain ⟨f, hf⟩ := exists_coord (fun i => innerₛₗ ℂ (j (b i : V))) j fun y i => hr _ y
  have horth : ∀ y, f y = 0 → ∀ k' ∈ U, ⟪j k', j y⟫_ℂ = 0 := by
    intro y hy k' hk'
    have e : k' = ∑ i, b.repr ⟨k', hk'⟩ i • (b i : V) := by
      have := congrArg U.subtype (b.sum_repr ⟨k', hk'⟩)
      rw [map_sum] at this
      exact this.symm
    rw [e, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : ⟪j (b i : V), j y⟫_ℂ = 0 := by
      have := hf y i
      rw [hy, Pi.zero_apply, map_zero] at this
      exact this.symm
    rw [map_smulₛₗ, inner_smul_left, h0, mul_zero]
  have hinj : Function.Injective (f ∘ₗ U.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have := horth u hu u u.2
    rw [inner_self_eq_zero, ← map_zero j] at this
    exact Subtype.ext (hj this)
  have hsurj : Function.Surjective (f ∘ₗ U.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨k, hk⟩ := hsurj (f x)
  exact ⟨k, k.2, horth _ (by rw [map_sub, ← hk]; exact sub_self _)⟩

end Abstract

section Coord

variable {K : Type} [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K) {E : Type} [AddCommGroup E] [Module ℂ E]


end Coord

section Family

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] {F : DefFam K G Pl0 T J} (X : CxData F.amb)

structure FormsTie : Prop where

  inner_eq : ∀ t (x y : (F.R t).S.Forms),
    ⟪X.jR t x, X.jR t y⟫_ℂ = F.v0.embedding ((F.R t).S.csum (x : (F.R t).S.Cl → (F.R t).S.V) (y : (F.R t).S.Cl → (F.R t).S.V))

  inj : ∀ t, Function.Injective (X.jR t)

  span : ∀ t, Submodule.span ℂ (Set.range (X.jR t)) = ⊤

def ThroughGood : Prop :=
  ∀ t (x : (F.R t).S.Forms), X.Θ t (X.jR t ((F.R t).S.gaOp (F.R t).r (goodAt F.X ⊥ 1) x)) = X.Θ t (X.jR t x)

omit X in
theorem csum_gaOp_good (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (hB : B.Ok s)
    {Y : Finset (G → K)} (hY : ∀ χ ∈ Y, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) (x y : B.S.Forms) :
    B.S.csum (B.S.gaOp B.r (goodAt Y P ψ) x : B.S.Cl → B.S.V) (y : B.S.Cl → B.S.V) =
      B.S.csum (x : B.S.Cl → B.S.V) (B.S.gaOp B.r (goodAt Y P ψ) y : B.S.Cl → B.S.V) := by
  have hp := good_at_spec K v0 hv0 G Y hY P ψ
  have hadj := group_action_matrix_adjoint K B.S G B.r hB.act (goodAt Y P ψ)
  rw [hp.selfAdj] at hadj
  have e : ∀ a b : B.S.Forms, B.S.csum (a : B.S.Cl → B.S.V) (b : B.S.Cl → B.S.V) =
      hform B.S.H (B.S.basis.equivFun a) (B.S.basis.equivFun b) := fun a b => by
    have := B.S.isClassSum (B.S.basis.equivFun a) (B.S.basis.equivFun b)
    rw [CSD.I_apply, CSD.I_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at this
    exact this.symm
  rw [e, e, ← CSD.gaMat_mulVec_equivFun, ← CSD.gaMat_mulVec_equivFun, RationalHermitianForm.hform_eq_dot, RationalHermitianForm.hform_eq_dot,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hadj]

variable {X}



end Family

end GlobalTheory.OneFormTest
