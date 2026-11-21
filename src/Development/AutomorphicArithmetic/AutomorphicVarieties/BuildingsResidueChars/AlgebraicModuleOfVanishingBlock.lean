import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.DivisorFrames.AlgebraicModSubmoduleQdetBlockOfGlRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotOfMemAdjoinCommuting
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QdetGeneratesUniversalEnvelopingCentre
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockDiagConjUnipotentLinear

section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.QuantumDetLeviBlocks

private theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}
    (φ : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp, Formalism.REAL.Tm]
  split_ifs <;> simp

private def pw (ι V : Type) [AddCommGroup V] [Module ℂ V] :
    Module.End ℂ V →ₐ[ℂ] Module.End ℂ (ι → V) where
  toFun f := LinearMap.compLeft f ι
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem algMod_of_ne_zero {M : Type} [AddCommGroup M] [Module ℂ M] (S N : Submodule ℂ M)
    (T : Module.End ℂ M) (P : Polynomial ℂ) (hP : P ≠ 0)
    (h : ∀ x ∈ S, Polynomial.aeval T P x ∈ N) : AlgMod S N T := by
  refine ⟨P * Polynomial.C (P.leadingCoeff)⁻¹, Polynomial.monic_mul_leadingCoeff_inv hP, fun x hx => ?_⟩
  rw [mul_comm, map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]
  exact N.smul_mem _ (h x hx)

end UpperTheory.V.QuantumDetLeviBlocks

open UpperTheory.V.QuantumDetLeviBlocks in
theorem UpperTheory.algMod_quantumDet_leviBlocks_of_parabolic :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (r s : ℕ) (X : Fin (r + s) → Fin (r + s) → Module.End ℂ M), Formalism.REAL.GlRel X → ∀ W Z S : Submodule ℂ M, S ≤ W → (∀ p q, ∀ x ∈ W, X p q x ∈ W) → (∀ (p : Fin r) (q : Fin s), ∀ x ∈ W, X (Fin.castAdd s p) (Fin.natAdd r q) x ∈ Z) → (∀ u, AlgMod S ⊥ (Formalism.REAL.qdet X u)) → ∀ u, AlgMod S Z (Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd s p) (Fin.castAdd s q)) u) ∧ AlgMod S Z (Formalism.REAL.qdet (fun p q : Fin s => X (Fin.natAdd r p) (Fin.natAdd r q)) u) := by
  intro M _ _ r s U hU W Z S hs hW hZ hc u
  let φ := pw S M
  let X : Fin (r + s) → Fin (r + s) → Module.End ℂ (S → M) := fun p q => φ (U p q)
  have hX : Formalism.REAL.GlRel X := by
    intro a b c d
    have := congrArg φ (hU a b c d)
    split_ifs at this ⊢ <;> simpa [X] using this
  let W' : Submodule ℂ (S → M) := Submodule.pi Set.univ fun _ => W
  let N' : Submodule ℂ (S → M) := ⊥ ⊔ Submodule.span ℂ {y | ∃ (p : Fin r) (q : Fin s), ∃ x ∈ W',
    y = X (Fin.castAdd s p) (Fin.natAdd r q) x}
  have hle : N' ≤ Submodule.pi Set.univ fun _ => Z := by
    refine sup_le bot_le (Submodule.span_le.2 ?_)
    rintro _ ⟨p, q, x, hx, rfl⟩ i hi
    exact hZ p q _ (hx i hi)
  obtain ⟨-, h1, h2⟩ := UpperTheory.algebraicModSubmodule_qdet_block_of_glRel (S → M) r s X hX W' ⊥ N'
    (fun p q x hx i hi => hW p q _ (hx i hi))
    (fun p q x hx => by rw [(Submodule.mem_bot ℂ).1 hx, map_zero]; exact Submodule.zero_mem _)
    rfl (fun i => i.1) (fun i _ => hs i.2) (fun u => by
      obtain ⟨P, hP, h⟩ := hc u
      refine ⟨P, hP.ne_zero, (Submodule.mem_bot ℂ).2 ?_⟩
      funext i
      rw [← map_qdet φ U u, Polynomial.aeval_algHom_apply]
      exact (Submodule.mem_bot ℂ).1 (h i.1 i.2))
  constructor
  · obtain ⟨P, hP, h⟩ := h1 u
    refine algMod_of_ne_zero _ _ _ P hP fun v hv => ?_
    have h3 := hle h ⟨v, hv⟩ trivial
    simp only [X] at h3
    rw [← map_qdet φ (fun p q : Fin r => U (Fin.castAdd s p) (Fin.castAdd s q)) u,
      Polynomial.aeval_algHom_apply] at h3
    exact h3
  · obtain ⟨P, hP, h⟩ := h2 u
    refine algMod_of_ne_zero _ _ _ P hP fun v hv => ?_
    have h3 := hle h ⟨v, hv⟩ trivial
    simp only [X] at h3
    rw [← map_qdet φ (fun p q : Fin s => U (Fin.natAdd r p) (Fin.natAdd r q)) u,
      Polynomial.aeval_algHom_apply] at h3
    exact h3
end

section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.uAction_mem_unipotentInvariant :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (u : UEnv K n), ∀ ψ ∈ NInv K n r, uAction u ψ ∈ NInv K n r := by
  intro K _ _ n r u ψ hψ X g
  have h : ∀ y, ψ.1 (unipGL X * y) = ψ.1 y := hψ X
  have e : sliceL (unipGL X * g) ψ = sliceL g ψ :=
    Subtype.ext (funext fun x => by simp only [coe_sliceL, archSlice_apply, mul_assoc, h])
  simp only [coe_uAction, uActFun, e]
end

section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

open GroundTheory.Automorphic.CuspidalSpectrum in
private theorem archExp_single (K : Type) [Field K] [NumberField K] (r s : ℕ) (i : Fin r) (j : Fin s)
    (x : mixedSpace K) :
    ∃ P : UPos (r + s) r → AdeleRing (𝓞 K) K,
      archExp (K := K) (n := r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) = unipGL P := by
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let P : UPos (r + s) r → AdeleRing (𝓞 K) K := fun p =>
    if p.1 = (Fin.castAdd s i, Fin.natAdd r j) then ((e.symm x, 0) : AdeleRing (𝓞 K) K) else 0
  refine ⟨P, ?_⟩
  have h0 : ∀ p, (P p).2 = 0 := by
    intro p
    by_cases hp : p.1 = (Fin.castAdd s i, Fin.natAdd r j)
    · simp [P, hp]
    · simp only [P, hp, if_false]
      rfl
  have hc := conj_unipGL_eq_archExp (1 : AdelicGLn.AdelicGL K (r + s)) P h0
  simp only [inv_one, one_mul, mul_one] at hc
  rw [hc]
  congr 1
  refine Matrix.ext fun a b => ?_
  simp [conjArch, archMat, archMatrixEquiv, Matrix.single_apply]
  show _ = e ((blockEntry P a b).1)
  rw [blockEntry_apply]
  by_cases hab : Fin.castAdd s i = a ∧ Fin.natAdd r j = b
  · obtain ⟨rfl, rfl⟩ := hab
    have hh : ((Fin.castAdd s i : Fin (r + s)) : ℕ) < r ∧ r ≤ ((Fin.natAdd r j : Fin (r + s)) : ℕ) :=
      ⟨by simp, by simp⟩
    rw [dif_pos hh, if_pos ⟨rfl, rfl⟩]
    simp [P, e]
  · rw [if_neg hab]
    split_ifs with hh
    · have hne : ¬ ((a, b) : Fin (r + s) × Fin (r + s)) = (Fin.castAdd s i, Fin.natAdd r j) := by
        intro heq
        apply hab
        simp only [Prod.mk.injEq] at heq
        exact ⟨heq.1.symm, heq.2.symm⟩
      simp only [P, hne, if_false]
      exact (map_zero e).symm
    · exact (map_zero e).symm

open GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.archExp_single_unipotent_embedding :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (i : Fin r) (j : Fin s) (x : mixedSpace K), ∀ ψ ∈ NInv K (r + s) r, lam K (r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) ψ ∈ Van K r s := by
  intro K _ _ r s i j x ψ hψ
  classical
  have hψ' : ∀ (X : UPos (r + s) r → AdeleRing (𝓞 K) K) (g : AdelicGLn.AdelicGL K (r + s)),
      ψ.1 (unipGL X * g) = ψ.1 g := hψ
  show ∀ (m₁ : GL (Fin r) (AdeleRing (𝓞 K) K)) (m₂ : GL (Fin s) (AdeleRing (𝓞 K) K)),
    (lam K (r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) ψ).1 (blk m₁ m₂) = 0
  intro m₁ m₂
  let Y : ArchMatrix K (r + s) := Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x
  let g : AdelicGLn.AdelicGL K (r + s) := blk m₁ m₂
  have hd := CuspidalSpectrum.hasDerivAt_archExp ψ g Y 0
  simp only [zero_smul, CuspidalSpectrum.archExp_zero, mul_one] at hd
  obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear (AdeleRing (𝓞 K) K) r s m₁ m₂
  have hmap : Matrix.GeneralLinearGroup.map (RingHom.id (AdeleRing (𝓞 K) K)) (blk m₁ m₂) = blk m₁ m₂ := by
    ext
    rfl
  have hconst : (fun t : ℝ => ψ.1 (g * CuspidalSpectrum.archExp (t • Y))) = fun _ => ψ.1 g := by
    funext t
    have hsY : t • Y = Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) (t • x) :=
      Matrix.smul_single _ _ _ _
    obtain ⟨P, hP⟩ := archExp_single K r s i j (t • x)
    rw [hsY, hP]
    have h1 := hc (AdeleRing (𝓞 K) K) (RingHom.id _) P
    rw [hmap] at h1
    show ψ.1 (blk m₁ m₂ * unipGL P) = ψ.1 (blk m₁ m₂)
    rw [h1, hψ']
  rw [hconst] at hd
  have h2 := hd.unique (hasDerivAt_const (0 : ℝ) (ψ.1 g))
  exact h2
end

section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private def carry {M : Type} [AddCommGroup M] [Module ℂ M] (W Z : Submodule ℂ M) : Submodule ℂ (Module.End ℂ M) where
  carrier := {T | ∀ x ∈ W, T x ∈ Z}
  add_mem' h1 h2 x hx := Z.add_mem (h1 x hx) (h2 x hx)
  zero_mem' _ _ := Z.zero_mem
  smul_mem' c _ h x hx := Z.smul_mem c (h x hx)

theorem UpperTheory.algebraic_module_of_vanishing_block :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), S ≤ NInv K (r + s) r → Centre S → ∀ (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι) (τ : ι) (u : ℂ), AlgMod S (Van K r s) (archCapBlock D (e1 r s) τ u) ∧ AlgMod S (Van K r s) (archCapBlock D (e2 r s) τ u) := by
  intro K _ _ r s S hS hC ι _ D τ u
  have hrel : Formalism.REAL.GlRel (gen D (lam K (r + s)) τ) :=
    (UpperTheory.gen_glRelations_and_commute_of_isLie _ ι (r + s) _ D (lam K (r + s)) (isLie_lam K (r + s))).1 τ
  have hW : ∀ p q, ∀ x ∈ NInv K (r + s) r, gen D (lam K (r + s)) τ p q x ∈ NInv K (r + s) r := fun p q =>
    gen_mem D (lam K (r + s)) τ p q (carry (NInv K (r + s) r) (NInv K (r + s) r))
      fun y x hx => UpperTheory.uAction_mem_unipotentInvariant K (r + s) r _ x hx
  have hZ : ∀ (p : Fin r) (q : Fin s), ∀ x ∈ NInv K (r + s) r,
      gen D (lam K (r + s)) τ (Fin.castAdd s p) (Fin.natAdd r q) x ∈ Van K r s := fun p q =>
    gen_mem D (lam K (r + s)) τ _ _ (carry (NInv K (r + s) r) (Van K r s))
      fun y x hx => UpperTheory.archExp_single_unipotent_embedding K r s p q y x hx
  have hq : ∀ v, AlgMod S ⊥ (Formalism.REAL.qdet (gen D (lam K (r + s)) τ) v) := fun v => by
    refine UpperTheory.algMod_bot_of_mem_adjoin_commuting _ S (uAction '' ((isExpLieAlgebra K (r + s)).centerU : Set (UEnv K (r + s)))) ?_ ?_ _
      (UpperTheory.qdet_generates_universalEnveloping_centre K (r + s) ι D τ v)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact Zc_comm (uAction_mem_Zc hx) (uAction_mem_Zc hy)
    · rintro _ ⟨z, hz, rfl⟩
      exact hC z hz
  exact UpperTheory.algMod_quantumDet_leviBlocks_of_parabolic _ r s (gen D (lam K (r + s)) τ) hrel (NInv K (r + s) r) (Van K r s) S hS hW hZ hq u
end
