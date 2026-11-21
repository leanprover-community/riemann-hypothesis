import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module

section Lin
variable {K : Type*} [Field K]

lemma exists_equiv_comp {A V : Type*} [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
    [FiniteDimensional K A] (i i' : A →ₗ[K] V) (hi : Function.Injective i)
    (hi' : Function.Injective i') : ∃ g : V ≃ₗ[K] V, ∀ x, g (i x) = i' x := by
  let f : LinearMap.range i ≃ₗ[K] LinearMap.range i' :=
    (LinearEquiv.ofInjective i hi).symm ≪≫ₗ LinearEquiv.ofInjective i' hi'
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, fun x => ?_⟩
  have h1 := hg ⟨i x, LinearMap.mem_range_self i x⟩
  have h2 : (LinearEquiv.ofInjective i hi).symm ⟨i x, LinearMap.mem_range_self i x⟩ = x := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [f, LinearEquiv.trans_apply, h2] at h1
  rw [← h1]; rfl

lemma exists_factor {A B U : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (R : A →ₗ[K] B) (f : A →ₗ[K] U)
    (h : LinearMap.ker R ≤ LinearMap.ker f) : ∃ S : B →ₗ[K] U, ∀ x, S (R x) = f x := by
  obtain ⟨σ, hσ⟩ := R.rangeRestrict.exists_rightInverse_of_surjective R.range_rangeRestrict
  obtain ⟨τ, hτ⟩ := LinearMap.exists_extend σ
  refine ⟨f ∘ₗ τ, fun x => ?_⟩
  have h1 : τ (R x) = σ ⟨R x, LinearMap.mem_range_self R x⟩ := by
    rw [← hτ]; rfl
  have h2 : R (σ ⟨R x, LinearMap.mem_range_self R x⟩) = R x := by
    have := congrArg (fun φ => ((φ ⟨R x, LinearMap.mem_range_self R x⟩ : LinearMap.range R) : B)) hσ
    simpa using this
  have h3 : σ ⟨R x, LinearMap.mem_range_self R x⟩ - x ∈ LinearMap.ker f := by
    apply h; simp [h2]
  rw [LinearMap.comp_apply, h1]
  have := LinearMap.mem_ker.mp h3
  rw [map_sub, sub_eq_zero] at this
  exact this

lemma card_injective [Fintype K] (W U : Type*) [AddCommGroup W] [Module K W] [AddCommGroup U]
    [Module K U] [Finite W] [Finite U] :
    Nat.card {f : W →ₗ[K] U // Function.Injective f} =
      ∏ j ∈ range (finrank K W), (Fintype.card K ^ finrank K U - Fintype.card K ^ j) := by
  classical
  let b := Module.finBasis K W
  have key : ∀ s : Fin (finrank K W) → U,
      LinearIndependent K s ↔ Function.Injective (b.constr K s : W →ₗ[K] U) := by
    intro s
    show Function.Injective (Finsupp.linearCombination K s) ↔ _
    have : ((b.constr K s : W →ₗ[K] U) : W → U) = (Finsupp.linearCombination K s) ∘ b.repr := by
      funext x
      rw [Basis.constr_apply, Function.comp_apply, Finsupp.linearCombination_apply]
    rw [this]
    exact (EquivLike.injective_comp b.repr _).symm
  have e : {f : W →ₗ[K] U // Function.Injective f} ≃
      {s : Fin (finrank K W) → U // LinearIndependent K s} :=
    ((b.constr K (M' := U)).toEquiv.subtypeEquiv (p := fun s => LinearIndependent K s)
      (q := fun f : W →ₗ[K] U => Function.Injective f) key).symm
  rw [Nat.card_congr e]
  by_cases hk : finrank K W ≤ finrank K U
  · rw [card_linearIndependent hk, Finset.prod_range]
  · rw [not_le] at hk
    rw [Finset.prod_eq_zero (Finset.mem_range.mpr hk) (by simp)]
    rw [Nat.card_eq_zero]; left
    constructor
    rintro ⟨s, hs⟩
    have := hs.fintype_card_le_finrank
    simp at this
    omega

end Lin
end Formalism.FourierDecayAlt.P.S3x4

namespace Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module

section Lin
variable {K : Type*} [Field K]

lemma card_ker_inf [Fintype K] {A B : Type*} (U : Type*) [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup U] [Module K U] [Finite A] [Finite U]
    (R : A →ₗ[K] B) :
    Nat.card {Y : A →ₗ[K] U // LinearMap.ker R ⊓ LinearMap.ker Y = ⊥} =
      Fintype.card K ^ (finrank K U * finrank K (LinearMap.range R)) *
      ∏ j ∈ range (finrank K (LinearMap.ker R)),
        (Fintype.card K ^ finrank K U - Fintype.card K ^ j) := by
  classical
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (LinearMap.ker R)
  have key : ∀ φψ : (LinearMap.ker R →ₗ[K] U) × (W' →ₗ[K] U),
      Function.Injective φψ.1 ↔
        LinearMap.ker R ⊓ LinearMap.ker (LinearMap.ofIsComplProdEquiv hW' φψ) = ⊥ := by
    rintro ⟨φ, ψ⟩
    rw [Submodule.eq_bot_iff, ← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    constructor
    · rintro h x ⟨hx1, hx2⟩
      have := h ⟨x, hx1⟩ (by
        rw [LinearMap.mem_ker]
        have h3 := LinearMap.mem_ker.mp hx2
        simpa [LinearMap.ofIsComplProdEquiv] using
          (LinearMap.ofIsCompl_apply_left hW' (φ := φ) (ψ := ψ) ⟨x, hx1⟩).symm.trans h3)
      simpa using congrArg Subtype.val this
    · rintro h ⟨x, hx1⟩ hx2
      have := h x ⟨hx1, by
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        have h3 := LinearMap.mem_ker.mp hx2
        exact (LinearMap.ofIsCompl_apply_left hW' (φ := φ) (ψ := ψ) ⟨x, hx1⟩).trans h3⟩
      exact Subtype.ext this
  have e : {Y : A →ₗ[K] U // LinearMap.ker R ⊓ LinearMap.ker Y = ⊥} ≃
      {φ : LinearMap.ker R →ₗ[K] U // Function.Injective φ} × (W' →ₗ[K] U) :=
    (((LinearMap.ofIsComplProdEquiv hW' (F := U)).toEquiv.subtypeEquiv
      (p := fun φψ : (LinearMap.ker R →ₗ[K] U) × (W' →ₗ[K] U) => Function.Injective φψ.1)
      (q := fun Y : A →ₗ[K] U => LinearMap.ker R ⊓ LinearMap.ker Y = ⊥) key).symm).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd
        (p := fun φ : LinearMap.ker R →ₗ[K] U => Function.Injective φ))
  have : Finite (W' →ₗ[K] U) := Module.finite_of_finite K
  let _ : Fintype (W' →ₗ[K] U) := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_prod, card_injective, mul_comm]
  congr 1
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), Module.finrank_linearMap]
  have h1 := Submodule.finrank_add_eq_of_isCompl hW'
  have h2 := LinearMap.finrank_range_add_finrank_ker R
  congr 1
  rw [mul_comm]; congr 1; omega

variable {V A A' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup A] [Module K A]
  [AddCommGroup A'] [Module K A']

def kerPart (π : V →ₗ[K] A) (σ : A →ₗ[K] V) (hσ : ∀ x, π (σ x) = x) (j : A' →ₗ[K] V) :
    A' →ₗ[K] LinearMap.ker π :=
  LinearMap.codRestrict _ (j - σ ∘ₗ π ∘ₗ j) (fun x => by simp [hσ])

lemma kerPart_coe (π : V →ₗ[K] A) (σ : A →ₗ[K] V) (hσ : ∀ x, π (σ x) = x) (j : A' →ₗ[K] V)
    (x : A') : (kerPart π σ hσ j x : V) = j x - σ (π (j x)) := rfl

lemma injective_iff_kerPart (π : V →ₗ[K] A) (σ : A →ₗ[K] V) (hσ : ∀ x, π (σ x) = x)
    (j : A' →ₗ[K] V) :
    Function.Injective j ↔ LinearMap.ker (π ∘ₗ j) ⊓ LinearMap.ker (kerPart π σ hσ j) = ⊥ := by
  rw [Submodule.eq_bot_iff, ← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  constructor
  · rintro h x ⟨hx1, hx2⟩
    apply h
    have h1 : π (j x) = 0 := hx1
    have h2 : (kerPart π σ hσ j x : V) = 0 := by
      rw [LinearMap.mem_ker.mp hx2]; rfl
    rw [kerPart_coe, h1, map_zero, sub_zero] at h2
    exact h2
  · rintro h x hx
    have hx' : j x = 0 := hx
    apply h
    refine ⟨?_, ?_⟩
    · show π (j x) = 0
      rw [hx', map_zero]
    · show kerPart π σ hσ j x = 0
      apply Subtype.ext
      rw [kerPart_coe, hx']; simp

def fibEquiv (π : V →ₗ[K] A) (σ : A →ₗ[K] V) (hσ : ∀ x, π (σ x) = x) (R : A' →ₗ[K] A) :
    {j : A' →ₗ[K] V // Function.Injective j ∧ π ∘ₗ j = R} ≃
      {Y : A' →ₗ[K] LinearMap.ker π // LinearMap.ker R ⊓ LinearMap.ker Y = ⊥} where
  toFun j := ⟨kerPart π σ hσ j.1, by
    have := (injective_iff_kerPart π σ hσ j.1).mp j.2.1
    rwa [j.2.2] at this⟩
  invFun Y := ⟨(LinearMap.ker π).subtype ∘ₗ Y.1 + σ ∘ₗ R, by
    have h1 : π ∘ₗ ((LinearMap.ker π).subtype ∘ₗ Y.1 + σ ∘ₗ R) = R := by
      ext x; simp [hσ]
    have h2 : kerPart π σ hσ ((LinearMap.ker π).subtype ∘ₗ Y.1 + σ ∘ₗ R) = Y.1 := by
      ext x; rw [kerPart_coe]; simp [hσ]
    refine ⟨?_, h1⟩
    rw [injective_iff_kerPart π σ hσ, h1, h2]
    exact Y.2⟩
  left_inv j := by
    apply Subtype.ext
    ext x
    have := j.2.2
    simp [kerPart_coe, ← this]
  right_inv Y := by
    apply Subtype.ext
    ext x; rw [kerPart_coe]; simp [hσ]

lemma exists_over [FiniteDimensional K A'] (π : V →ₗ[K] A) (hπ : Function.Surjective π)
    (j j' : A' →ₗ[K] V) (hj : Function.Injective j) (hj' : Function.Injective j')
    (hjj : π ∘ₗ j = π ∘ₗ j') :
    ∃ h : V →ₗ[K] V, Function.Injective h ∧ π ∘ₗ h = π ∧ h ∘ₗ j' = j := by
  obtain ⟨σ, hσ0⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hσ : ∀ x, π (σ x) = x := fun x => by
    simpa using congrArg (fun φ => φ x) hσ0
  set R := π ∘ₗ j' with hR
  set y := kerPart π σ hσ j with hy
  set y' := kerPart π σ hσ j' with hy'
  have hy1 := (injective_iff_kerPart π σ hσ j).mp hj
  have hy1' := (injective_iff_kerPart π σ hσ j').mp hj'
  rw [hjj] at hy1
  have inj : ∀ z : A' →ₗ[K] LinearMap.ker π, LinearMap.ker R ⊓ LinearMap.ker z = ⊥ →
      Function.Injective (z ∘ₗ (LinearMap.ker R).subtype) := by
    intro z hz
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ hx2
    apply Subtype.ext
    exact (Submodule.eq_bot_iff _).mp hz x ⟨hx, hx2⟩
  obtain ⟨T, hT⟩ := exists_equiv_comp _ _ (inj y' hy1') (inj y hy1)
  obtain ⟨S, hS⟩ := exists_factor R (y - T.toLinearMap ∘ₗ y') (by
    intro x hx
    have := hT ⟨x, hx⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    simp [this])
  let P : V →ₗ[K] LinearMap.ker π := kerPart π σ hσ LinearMap.id
  have hP : ∀ v, (P v : V) = v - σ (π v) := fun v => rfl
  refine ⟨(LinearMap.ker π).subtype ∘ₗ (T.toLinearMap ∘ₗ P + S ∘ₗ π) + σ ∘ₗ π, ?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : ((T (P v) + S (π v) : LinearMap.ker π) : V) + σ (π v) = 0 := hv
    have h1 : π v = 0 := by
      have := congrArg π hv'
      simpa [hσ] using this
    rw [h1] at hv'
    simp only [map_zero, add_zero] at hv'
    have h2 : P v = 0 := by
      have : T (P v) = 0 := Subtype.ext hv'
      simpa using this
    have h3 := hP v
    rw [h2, h1] at h3
    simpa using h3.symm
  · ext v; simp [hσ]
  · ext x
    have h1 : P (j' x) = y' x := rfl
    have h2 := hS x
    have h3 : π (j' x) = R x := rfl
    have h4 : π (j x) = R x := by rw [← hjj]; rfl
    simp only [LinearMap.comp_apply, LinearMap.add_apply, Submodule.subtype_apply, h1, h3, h2,
      LinearMap.sub_apply, LinearEquiv.coe_coe]
    simp only [add_sub_cancel, hy, kerPart_coe, h4]
    simp

end Lin
end Formalism.FourierDecayAlt.P.S3x4

namespace Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module

section Mat
variable {K : Type} [Field K]

lemma rank_eq_iff_injective {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) :
    X.rank = a ↔ Function.Injective (Matrix.toLin' X) := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' X)
  rw [Module.finrank_fin_fun] at h
  have h0 : X.rank = finrank K (LinearMap.range (Matrix.toLin' X)) := by
    rw [Matrix.rank, Matrix.toLin'_apply']
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero, h0]
  omega

lemma surjective_of_rank {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) (hX : X.rank = a) :
    Function.Surjective (Matrix.toLin' Xᵀ) := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have h := Matrix.rank_transpose X
  rw [Matrix.rank, ← Matrix.toLin'_apply', hX] at h
  rw [Module.finrank_fin_fun, h]

lemma finrank_ker_of_rank {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) (hX : X.rank = a) :
    finrank K (LinearMap.ker (Matrix.toLin' Xᵀ)) = n - a := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' Xᵀ)
  rw [Module.finrank_fin_fun, LinearMap.range_eq_top.mpr (surjective_of_rank X hX), finrank_top,
    Module.finrank_fin_fun] at h
  omega


lemma card_fibre [Fintype K] (n a : ℕ) (R : Matrix (Fin a) (Fin a) K)
    (X₁ : Matrix (Fin n) (Fin a) K) (hX : X₁.rank = a) :
    Nat.card {X₂ : Matrix (Fin n) (Fin a) K // X₂.rank = a ∧ X₂ᵀ * X₁ = Rᵀ} =
      Fintype.card K ^ ((n - a) * R.rank) *
        ∏ j ∈ range (a - R.rank), (Fintype.card K ^ (n - a) - Fintype.card K ^ j) := by
  obtain ⟨σ, hσ0⟩ := (Matrix.toLin' X₁ᵀ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (surjective_of_rank X₁ hX))
  have hσ : ∀ x, Matrix.toLin' X₁ᵀ (σ x) = x := fun x => by
    simpa using congrArg (fun φ => φ x) hσ0
  have e : {X₂ : Matrix (Fin n) (Fin a) K // X₂.rank = a ∧ X₂ᵀ * X₁ = Rᵀ} ≃
      {j : (Fin a → K) →ₗ[K] (Fin n → K) //
        Function.Injective j ∧ Matrix.toLin' X₁ᵀ ∘ₗ j = Matrix.toLin' R} :=
    (Matrix.toLin' (R := K) (m := Fin n) (n := Fin a)).toEquiv.subtypeEquiv
      (p := fun X₂ : Matrix (Fin n) (Fin a) K => X₂.rank = a ∧ X₂ᵀ * X₁ = Rᵀ)
      (q := fun j : (Fin a → K) →ₗ[K] (Fin n → K) =>
        Function.Injective j ∧ Matrix.toLin' X₁ᵀ ∘ₗ j = Matrix.toLin' R)
      (fun X₂ => by
        refine and_congr (rank_eq_iff_injective X₂) ?_
        show _ ↔ Matrix.toLin' X₁ᵀ ∘ₗ Matrix.toLin' X₂ = Matrix.toLin' R
        rw [← Matrix.toLin'_mul, (Matrix.toLin' (R := K)).injective.eq_iff,
          ← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.transpose_transpose])
  rw [Nat.card_congr e, Nat.card_congr (fibEquiv _ σ hσ _), card_ker_inf,
    finrank_ker_of_rank X₁ hX]
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' R)
  rw [Module.finrank_fin_fun] at h
  have h0 : R.rank = finrank K (LinearMap.range (Matrix.toLin' R)) := by
    rw [Matrix.rank, Matrix.toLin'_apply']
  rw [← h0] at h ⊢
  have h1 : finrank K (LinearMap.ker (Matrix.toLin' R)) = a - R.rank := by omega
  rw [h1]

end Mat
end Formalism.FourierDecayAlt.P.S3x4

namespace Formalism.FourierDecayAlt.P
open Matrix Finset Module Formalism.FourierDecayAlt.P.S3x4



end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module Formalism.FourierDecayAlt.S3





end Formalism.FourierDecayAlt.P.S3x4

namespace Formalism.FourierDecayAlt.P
open Matrix Finset Module Formalism.FourierDecayAlt.P.S3x4 Formalism.FourierDecayAlt.S3


end Formalism.FourierDecayAlt.P
