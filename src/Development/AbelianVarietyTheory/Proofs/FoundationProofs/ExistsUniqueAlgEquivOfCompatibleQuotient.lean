import Mathlib

noncomputable section

namespace GlobalTheory

open TensorProduct

theorem isPrecomplete_of_finite {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t with
  | zero => exact ⟨0, by simp⟩
  | tmul a m =>
    obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective I R a
    refine ⟨r • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, show AdicCompletion.of I R r =
      algebraMap R (AdicCompletion I R) r by simp [AdicCompletion.algebraMap_apply],
      algebraMap_smul, map_smul]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simp [hu, hv]⟩

theorem isAdicComplete_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M where
  toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  toIsPrecomplete := isPrecomplete_of_finite I M

theorem isAdicComplete_map_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (I.map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff]
  exact isAdicComplete_of_finite I S

section Tower

variable {R : Type*} [CommRing R] (I : Ideal R)



end Tower

section Quotient

variable {R : Type*} [CommRing R] (I : Ideal R)

abbrev adicQuotTransition (A : Type*) [CommRing A] [Algebra R A] (n : ℕ) :
    (A ⧸ (I ^ (n + 1)).map (algebraMap R A)) →ₐ[R] A ⧸ (I ^ n).map (algebraMap R A) :=
  Ideal.Quotient.factorₐ R (Ideal.map_mono (Ideal.pow_le_pow_right n.le_succ))

variable [IsNoetherianRing R] [IsAdicComplete I R] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]



end Quotient

section Tensor

variable {R : Type*} [CommRing R] (I : Ideal R)

abbrev adicTensorTransition (A : Type*) [Ring A] [Algebra R A] (n : ℕ) :
    (R ⧸ I ^ (n + 1)) ⊗[R] A →ₐ[R] (R ⧸ I ^ n) ⊗[R] A :=
  Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ))
    (AlgHom.id R A)


variable [IsNoetherianRing R] [IsAdicComplete I R]


section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]



end

omit [IsNoetherianRing R] [IsAdicComplete I R] in

theorem comul_one_tmul_eq_distribBaseChange (S : Type*) [CommRing S] [Algebra R S] {A : Type*}
    [AddCommGroup A] [Module R A] [Coalgebra R A] (a : A) :
    Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] a) =
      AlgebraTensorModule.distribBaseChange R S A A (1 ⊗ₜ Coalgebra.comul a) := by
  rw [TensorProduct.comul_tmul]
  induction (Coalgebra.comul a : A ⊗[R] A) with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

section

variable {A B : Type*} [Ring A] [Ring B] [Bialgebra R A] [Bialgebra R B]



end

end Tensor

end GlobalTheory
