import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreFurther
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.RepSingle

section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.msp :
    ∀ (O B κ : Type) [CommRing O] [CommRing B] [Algebra O B] [Fintype κ] (n : ℕ) (x : B →ₐ[O] O) (P : κ → Polynomial B) (α : κ → Fin n → O), (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → ∀ a : MvPolynomial (κ × Fin n) B, MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) a = 0 → Ideal.Quotient.mk (mSplitIdeal P n) ((∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) * a) ∈ (RingHom.ker x).map (algebraMap B (MSplitAlg P n)) := by
  intro O B κ _ _ _ _ n x P α hP a ha
  classical
  set J : Ideal (MSplitAlg P n) := (RingHom.ker x).map (algebraMap B (MSplitAlg P n)) with hJ
  let ψ : MvPolynomial (κ × Fin n) B →+* (MSplitAlg P n ⧸ J) :=
    (Ideal.Quotient.mk J).comp (Ideal.Quotient.mk (mSplitIdeal P n))
  let g : B →+* (MSplitAlg P n ⧸ J) := ψ.comp MvPolynomial.C
  let h : O →+* (MSplitAlg P n ⧸ J) := g.comp (algebraMap O B)
  have hg : ∀ b : B, g b = (Ideal.Quotient.mk J) (algebraMap B (MSplitAlg P n) b) := by
    intro b
    show (Ideal.Quotient.mk J) ((Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.C b)) = _
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  have hgx : g = h.comp (x : B →+* O) := by
    ext b
    show g b = g (algebraMap O B (x b))
    rw [← sub_eq_zero, ← map_sub, hg, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.mem_map_of_mem
    rw [RingHom.mem_ker]
    simp
  have hg' : (Ideal.Quotient.mk J).comp (algebraMap B (MSplitAlg P n)) = h.comp (x : B →+* O) := by
    rw [← hgx]
    ext b
    exact (hg b).symm
  have hroot : ∀ j i, ∏ k, (ψ (MvPolynomial.X (j, i)) - h (α j k)) = 0 := by
    intro j i
    have e := MSplitAlg.prod_root P n j
    have e2 := congrArg (fun q => Polynomial.eval (ψ (MvPolynomial.X (j, i))) (q.map (Ideal.Quotient.mk J))) e
    rw [Polynomial.map_map, hg', ← Polynomial.map_map, hP j] at e2
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at e2
    rw [← e2]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  have hh : ∀ c : O, ψ (MvPolynomial.C (algebraMap O B c)) = h c := fun _ => rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change ψ (_ * a) = 0
  rw [map_mul]
  set δ := ψ (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
    (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) with hδ
  have hδX : ∀ p : κ × Fin n, δ * (ψ (MvPolynomial.X p) - h (α p.1 p.2)) = 0 := by
    rintro ⟨j, i⟩
    obtain ⟨q, hq⟩ : (∏ k ∈ Finset.univ.erase i,
        (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) : MvPolynomial (κ × Fin n) B) ∣
        ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) :=
      (Finset.dvd_prod_of_mem (fun i => ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) (Finset.mem_univ i)).trans
        (Finset.dvd_prod_of_mem (fun j => ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) (Finset.mem_univ j))
    rw [hδ, hq, map_mul, mul_right_comm]
    simp only [map_prod, map_sub, hh]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i), hroot, zero_mul]
  have key : ∀ b : MvPolynomial (κ × Fin n) B,
      δ * (ψ b - h (MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) b)) = 0 := by
    intro b
    refine MvPolynomial.induction_on
      (motive := fun b => δ * (ψ b - h (MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) b)) = 0)
      b ?_ ?_ ?_
    · intro c
      have hc : ψ (MvPolynomial.C c) = h ((x : B →+* O) c) := by
        show g c = _
        rw [hgx]
        rfl
      rw [MvPolynomial.eval₂_C, hc, sub_self, mul_zero]
    · intro p q hp hq
      rw [map_add, MvPolynomial.eval₂_add, map_add]
      linear_combination hp + hq
    · intro p v hp
      rw [map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul]
      beta_reduce
      linear_combination (ψ (MvPolynomial.X v)) * hp +
        h (MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) p) * hδX v
  have hk := key a
  rw [ha, map_zero, sub_zero] at hk
  exact hk
end

section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.kill :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [CommRing B] [Algebra O R] [Algebra O B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →ₐ[O] B) (x : B →ₐ[O] O) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (f : PU R q n) (α : Fin q → Fin n → O) (I : Ideal R) (t₀ : R), Function.Surjective β → TwoMaps (M := M) β.toRingHom P act f → (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → (∀ a : B, x a = 0 → ∀ m : M, (β t₀ * a) • m ∈ (I.map β • ⊤ : Submodule B M)) → ∀ a : PU R q n, MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) a = 0 → ∀ v : V, act (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))) * f * a) v ∈ (I • ⊤ : Submodule R V) := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β x P act f α I t₀ hβ hTM hP hker a ha v
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := hTM
  have hπC : ∀ b : B, (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.C b) =
      algebraMap B (MSplitAlg P n) b := fun b => rfl
  have key : ∀ i ∈ I, ∀ w : MSplitAlg P n ⊗[B] M, φ ((β i) • w) ∈ (I • ⊤ : Submodule R V) := by
    intro i hi w
    have e1 : (β i) • w = (Ideal.Quotient.mk (mSplitIdeal P n))
        ((MvPolynomial.map β.toRingHom) (MvPolynomial.C i)) • w := by
      rw [MvPolynomial.map_C, hπC, algebraMap_smul]
      rfl
    rw [e1, h1, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]
    exact Submodule.smul_mem_smul hi trivial
  have claim : ∀ b : B, x b = 0 → ∀ z : MSplitAlg P n ⊗[B] M,
      φ (algebraMap B (MSplitAlg P n) (β t₀ * b) • z) ∈ (I • ⊤ : Submodule R V) := by
    intro b hb z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      rw [algebraMap_smul, ← TensorProduct.tmul_smul]
      refine Submodule.smul_induction_on (p := fun y => φ (s ⊗ₜ[B] y) ∈ (I • ⊤ : Submodule R V))
        (hker b hb m) ?_ ?_
      · intro r hr m' _
        obtain ⟨i, hi, rfl⟩ := (Ideal.mem_map_iff_of_surjective β hβ).mp hr
        rw [TensorProduct.tmul_smul]
        exact key i hi _
      · intro y1 y2 k1 k2
        rw [TensorProduct.tmul_add, map_add]
        exact add_mem k1 k2
    | add z1 z2 k1 k2 =>
      rw [smul_add, map_add]
      exact add_mem k1 k2
  have gen : ∀ y ∈ Ideal.map (algebraMap B (MSplitAlg P n)) (RingHom.ker x), ∀ z : MSplitAlg P n ⊗[B] M,
      φ ((algebraMap B (MSplitAlg P n) (β t₀) * y) • z) ∈ (I • ⊤ : Submodule R V) := by
    intro y hy
    unfold Ideal.map at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      intro z
      rw [← map_mul]
      exact claim b (RingHom.mem_ker.mp hb) z
    | zero => intro z; simp
    | add y1 y2 _ _ k1 k2 =>
      intro z
      rw [mul_add, add_smul, map_add]
      exact add_mem (k1 z) (k2 z)
    | smul r y _ k =>
      intro z
      rw [smul_eq_mul, mul_left_comm, mul_comm r, mul_smul]
      exact k _
  have hE : MvPolynomial.map β.toRingHom (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k))) : PU R q n) =
      ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) := by
    simp [map_prod]
  have hmem := Sp.msp O B (Fin q) n x P α hP (MvPolynomial.map β.toRingHom a)
    (by rw [MvPolynomial.eval₂_map]; exact ha)
  have e3 : act (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))) * f * a) v =
      φ (((Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom (MvPolynomial.C t₀ *
        (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))))) *
        (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom a)) • ψ v) := by
    rw [mul_smul, ← h2, h1, h3]
    simp only [map_mul, Module.End.mul_apply]
  rw [e3]
  have e4 : (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom (MvPolynomial.C t₀ *
        (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))))) *
        (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom a) =
      algebraMap B (MSplitAlg P n) (β t₀) * (Ideal.Quotient.mk (mSplitIdeal P n))
        ((∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) *
          MvPolynomial.map β.toRingHom a) := by
    rw [map_mul (MvPolynomial.map β.toRingHom), hE, MvPolynomial.map_C, ← hπC, ← map_mul, ← map_mul,
      mul_assoc]
    rfl
  rw [e4]
  exact gen _ hmem _
end

section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.lamW :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [CommRing B] [Algebra O R] [Algebra O B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →ₐ[O] B) (x : B →ₐ[O] O) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (f : PU R q n) (α : Fin q → Fin n → O) (lam : M →+ O) (m₀ : M), TwoMaps (M := M) β.toRingHom P act f → (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → (∀ (a : B) m, lam (a • m) = x a * lam m) → ∃ (lw : V →+ O) (v : V), (∀ τ w, lw (act τ w) = MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) τ * lw w) ∧ lw v = MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) f * lam m₀ := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β x P act f α lam m₀ hT hP hlam
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := hT
  letI : Algebra B O := (x : B →+* O).toAlgebra
  let ε : MSplitAlg P n →ₐ[B] O := MSplitAlg.lift P n (fun j i => α j i) (fun j => (hP j).symm)
  have hε : ∀ t : PU R q n, ε (Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β.toRingHom t)) =
      MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) t := by
    intro t
    show MvPolynomial.aeval (fun p : Fin q × Fin n => α p.1 p.2) (MvPolynomial.map β.toRingHom t) = _
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    rfl
  let lamL : M →ₗ[B] O :=
    { toFun := lam
      map_add' := lam.map_add
      map_smul' := fun a m => hlam a m }
  let Λ : MSplitAlg P n ⊗[B] M →ₗ[B] O :=
    TensorProduct.lift ((LinearMap.mul B O).compl₁₂ ε.toLinearMap lamL)
  have hΛt : ∀ a m, Λ (a ⊗ₜ m) = ε a * lam m := by
    intro a m
    show TensorProduct.lift _ (a ⊗ₜ m) = _
    rw [TensorProduct.lift.tmul]
    rfl
  have hΛs : ∀ (a : MSplitAlg P n) z, Λ (a • z) = ε a * Λ z := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, mul_zero]
    | tmul a' m => rw [TensorProduct.smul_tmul', smul_eq_mul, hΛt, hΛt, map_mul, mul_assoc]
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, mul_add]
  refine ⟨Λ.toAddMonoidHom.comp ψ, φ (1 ⊗ₜ m₀), ?_, ?_⟩
  · intro τ w
    show Λ (ψ (act τ w)) = _ * Λ (ψ w)
    rw [h2, hΛs, hε]
  · show Λ (ψ (φ (1 ⊗ₜ m₀))) = _
    rw [h4, hΛs, hε, hΛt, map_one, one_mul]
end

section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.trans :
    ∀ (R M W : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W] (q n : ℕ) (act1 : PUY R q n →ₐ[R] Module.End R M) (actw : PU R q n →ₐ[R] Module.End R W) (tr : M →ₗ[R] W), Function.Surjective tr → LinearMap.ker tr = ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) → (∀ j i m, tr (act1 (uV R j i) m) = actw (MvPolynomial.X (j, i)) (tr m)) → (∀ τ m, tr (act1 τ m) = actw (MvPolynomial.aeval (Sum.elim MvPolynomial.X 0) τ) (tr m)) ∧ ∀ (I : Ideal R) m, tr m ∈ (I • ⊤ : Submodule R W) → m ∈ (I • ⊤ : Submodule R M) ⊔ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) := by
  intro R M W _ _ _ _ _ q n act1 actw tr hsurj hker hu
  have hy : ∀ p : Fin q × Fin n, ∀ m, tr (act1 (yV R p.1 p.2) m) = 0 := by
    intro p m
    rw [← LinearMap.mem_ker, hker]
    exact Submodule.mem_iSup_of_mem p (LinearMap.mem_range_self _ m)
  refine ⟨fun τ => ?_, fun I m hm => ?_⟩
  · induction τ using MvPolynomial.induction_on with
    | C a =>
        intro m
        rw [MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
        simp
    | add p r hp hr =>
        intro m
        simp [map_add, hp, hr]
    | mul_X p s hp =>
        intro m
        rcases s with ⟨j, i⟩ | ⟨j, i⟩
        · rw [map_mul, Module.End.mul_apply, hp, map_mul, map_mul, Module.End.mul_apply,
            MvPolynomial.aeval_X, Sum.elim_inl]
          exact congrArg _ (hu j i m)
        · rw [map_mul, Module.End.mul_apply, hp, map_mul, MvPolynomial.aeval_X, Sum.elim_inr,
            show tr (act1 (MvPolynomial.X (Sum.inr (j, i))) m) = 0 from hy (j, i) m]
          simp
  · have htop : (I • ⊤ : Submodule R W) = (I • ⊤ : Submodule R M).map tr := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
    rw [htop] at hm
    obtain ⟨m', hm', he⟩ := hm
    have hk : m - m' ∈ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) := by
      rw [← hker, LinearMap.mem_ker, map_sub, he, sub_self]
    have hmm : m = m' + (m - m') := by abel
    rw [hmm]
    exact Submodule.add_mem_sup hm' hk
end

section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.betaLam :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N), ∀ a : abelian₂ O Empty D, A.β (algebraMap (abelian₂ O Empty D) A.R a) = b.lam a := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A a
  haveI hOO : IsCO O O :=
    { complete := IsCoef.complete
      isLocalHom := ⟨fun x hx => by simpa using hx⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hL : IsCO O (abelian₂ O Empty D) := co_mvps O O (Empty ⊕ Fin D)
  have hmax : ∀ s : Empty ⊕ Fin D, b.lam (MvPowerSeries.X s) ∈ maximalIdeal B := by
    intro s
    rw [← res_eq_zero_iff O B, res_map, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    intro hu
    have h0 := hu.map MvPowerSeries.constantCoeff
    simp at h0
  obtain ⟨F, _, huniq⟩ :=
    co_ev O O B (Empty ⊕ Fin D) (Algebra.ofId O B) (fun s => b.lam (MvPowerSeries.X s)) hmax
  let F1 : abelian₂ O Empty D →ₐ[O] B :=
    A.β.comp (IsScalarTower.toAlgHom O (abelian₂ O Empty D) A.R)
  have e1 : F1 = F := by
    apply huniq
    refine ⟨fun x => ?_, fun s => ?_⟩
    · rw [MvPowerSeries.c_eq_algebraMap]
      exact F1.commutes x
    · rcases s with e | k
      · exact e.elim
      · show A.β (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (Sum.inr k))) = _
        rw [A.segmentWeightExponent k, b.segmentWeightExponent k, map_sub, map_mul, map_one, AlgHom.commutes]
        congr 2
        have hp := congrArg (fun χ => ((χ (b.wt.γ k) : Bˣ) : B)) (A.β_pair.2 (b.wt.v k) (b.wt.i k))
        simpa [pushCh] using hp
  have e2 : b.lam = F := by
    apply huniq
    refine ⟨fun x => ?_, fun s => rfl⟩
    rw [MvPowerSeries.c_eq_algebraMap]
    exact b.lam.commutes x
  have := congrArg (fun φ : abelian₂ O Empty D →ₐ[O] B => φ a) (e1.trans e2.symm)
  simpa [F1] using this
end

section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem mem_iff {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (y : R) :
    f y ∈ maximalIdeal R' ↔ y ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem surj_of_gen {O : Type} [CommRing O] [IsLocalRing O] {R C : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing C] [Algebra O C] [IsCO O C] (f : R →ₐ[O] C) (S : Set C) (hS : GenBy O S)
    (h1 : ∀ b ∈ S, b ∈ f.range) : Function.Surjective f := by
  apply co_surj O R C f
  intro x hx
  obtain ⟨a, ha, hxa⟩ := hS 2 x
  have hrange : Algebra.adjoin O S ≤ f.range := Algebra.adjoin_le (fun b hb => h1 b hb)
  obtain ⟨y, hy⟩ := hrange ha
  have hy' : f y = a := hy
  have hsq : maximalIdeal C ^ 2 ≤ maximalIdeal C := Ideal.pow_le_self (by norm_num)
  have haM : a ∈ maximalIdeal C := by
    have h2 : a = x - (x - a) := by ring
    rw [h2]
    exact sub_mem hx (hsq hxa)
  have hyM : y ∈ maximalIdeal R := by
    rw [← mem_iff f y, hy']
    exact haM
  have hx' : x = f y + (x - a) := by rw [hy']; ring
  rw [hx']
  exact add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem f hyM)) (Ideal.mem_sup_right hxa)

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  simp [GDet.lam, GDet.chi, GDet.comap, Finsupp.mapDomain_sub, MonoidAlgebra.mapDomain,
    Finsupp.mapDomain_single]

private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h := (CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)
  simpa using h.2 i

private theorem surjective_levelChangeBaseGroupHom {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) :
    Function.Surjective h.p₀ := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := h.surj x
  refine ⟨⟨y, ?_⟩, rfl⟩
  rw [MonoidHom.mem_ker, ← h.η y]
  exact hx

theorem UpperTheory.V.Th.Sp.betaSurj :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N), GenBy O (pairVals u) → Function.Surjective A.β := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A hgen
  obtain ⟨hD, hψ⟩ := A.β_pair
  refine surj_of_gen A.β _ hgen ?_
  rintro b (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩)
  · obtain ⟨g, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    refine ⟨A.p.D.lam i (MonoidAlgebra.single g 1), ?_⟩
    have h := lam_map A.p.D A.β.toRingHom i g
    rw [hD, lam_comap] at h
    exact h.symm
  · exact ⟨(A.p.ψ v i g : A.R), congrArg (fun χ => ((χ g : _ˣ) : B)) (hψ v i)⟩
end

section
open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.phi :
    ∀ (S M O X : Type) [CommRing S] [AddCommGroup M] [Module S M] [Module.Projective S M] [CommRing O] [AddCommGroup X] [Module O X] (th : S →+* O) (ell : S →+ X) (lam : M →+ O), (∀ a b, ell (a * b) = th a • ell b + th b • ell a) → (∀ (σ : S) m, lam (σ • m) = th σ * lam m) → ∃ Φ : M →+ X, ∀ (σ : S) m, Φ (σ • m) = th σ • Φ m + lam m • ell σ := by
  intro S M O X _ _ _ _ _ _ _ th ell lam hell hlam
  obtain ⟨s, hs⟩ := Module.Projective.out (R := S) (P := M)
  have key : ∀ m, lam m = (s m).sum (fun i a => th a * lam i) := by
    intro m
    conv_lhs => rw [← hs m]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [hlam]
  refine ⟨{ toFun := fun m => (s m).sum (fun i a => lam i • ell a),
            map_zero' := by simp,
            map_add' := ?_ }, ?_⟩
  · intro m n
    simp only [map_add]
    exact Finsupp.sum_add_index' (fun i => by simp) (fun i a b => by simp [smul_add])
  · intro σ m
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
    rw [Finsupp.sum_smul_index' (fun i => by simp), key m, Finsupp.sum, Finsupp.sum, Finsupp.sum,
      Finset.smul_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_eq_mul, hell, smul_add, smul_smul, smul_smul, smul_smul, mul_comm (lam i) (th σ),
      mul_comm (lam i) (th ((s m) i))]
end

section
open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.der :
    ∀ (O S T M X : Type) [CommRing O] [CommRing S] [CommRing T] [Algebra O S] [Algebra O T] [AddCommGroup M] [Module S M] [Module T M] [SMulCommClass S T M] [AddCommGroup X] [Module O X] (th : S →ₐ[O] O) (x : T →ₐ[O] O) (ell : S →ₗ[O] X) (lam : M →+ O) (Φ : M →+ X) (t : T) (v : M), (∀ (o : O) (m : M), algebraMap O S o • m = algebraMap O T o • m) → ell 1 = 0 → (∀ (σ : S) m, lam (σ • m) = th σ * lam m) → (∀ (σ : S) m, Φ (σ • m) = th σ • Φ m + lam m • ell σ) → (∀ a, x a = 0 → ∀ m : M, (t * a) • m ∈ (RingHom.ker th • ⊤ : Submodule S M)) → ∃ del : T →ₗ[O] X, (∀ a b, del (a * b) = x a • del b + x b • del a) ∧ (∀ (τ : T) (σ : S), (∀ m : M, τ • m = σ • m) → x τ = th σ → del τ = lam ((t * t) • v) • ell σ) ∧ ∀ a, x a = 0 → (∀ m : M, (t * a) • m = 0) → del a = 0 := by
  intro O S T M X _ _ _ _ _ _ _ _ _ _ _ th x ell lam Φ t v hO hell1 hlam hΦ hker
  set m0 : M := (t * t) • v with hm0
  have hell : ∀ o : O, ell (algebraMap O S o) = 0 := by
    intro o
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hell1, smul_zero]
  have hΦO : ∀ (o : O) (m : M), Φ (algebraMap O S o • m) = o • Φ m := by
    intro o m
    rw [hΦ, AlgHom.commutes, Algebra.algebraMap_self_apply, hell, smul_zero, add_zero]
  have hlamK : ∀ m ∈ (RingHom.ker th • ⊤ : Submodule S M), lam m = 0 := by
    intro m hm
    refine Submodule.smul_induction_on (p := fun m => lam m = 0) hm ?_ ?_
    · intro σ hσ n _
      rw [hlam, (RingHom.mem_ker).1 hσ, zero_mul]
    · intro y z hy hz
      rw [map_add, hy, hz, add_zero]
  have hΦK : ∀ a, x a = 0 → ∀ m ∈ (RingHom.ker th • ⊤ : Submodule S M), Φ ((t * a) • m) = 0 := by
    intro a ha m hm
    refine Submodule.smul_induction_on (p := fun m => Φ ((t * a) • m) = 0) hm ?_ ?_
    · intro σ hσ n _
      rw [← smul_comm σ (t * a) n, hΦ, (RingHom.mem_ker).1 hσ, zero_smul, zero_add,
        hlamK _ (hker a ha n), zero_smul]
    · intro y z hy hz
      rw [smul_add, map_add, hy, hz, add_zero]
  have hx0 : ∀ a, x (a - algebraMap O T (x a)) = 0 := by
    intro a
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  refine ⟨{ toFun := fun a => Φ ((a - algebraMap O T (x a)) • m0), map_add' := ?_, map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro a b
    rw [map_add x, map_add (algebraMap O T),
      show a + b - (algebraMap O T (x a) + algebraMap O T (x b)) = (a - algebraMap O T (x a)) + (b - algebraMap O T (x b)) by ring,
      add_smul, map_add]
  · intro o a
    have h : o • a - algebraMap O T (x (o • a)) = algebraMap O T o * (a - algebraMap O T (x a)) := by
      rw [map_smul x, smul_eq_mul, Algebra.smul_def, map_mul]
      ring
    show Φ ((o • a - algebraMap O T (x (o • a))) • m0) = o • Φ ((a - algebraMap O T (x a)) • m0)
    rw [h, mul_smul, ← hO, hΦO]
  · intro a b
    show Φ ((a * b - algebraMap O T (x (a * b))) • m0) = x a • Φ ((b - algebraMap O T (x b)) • m0) + x b • Φ ((a - algebraMap O T (x a)) • m0)
    have h : a * b - algebraMap O T (x (a * b)) = (a - algebraMap O T (x a)) * (b - algebraMap O T (x b)) + algebraMap O T (x a) * (b - algebraMap O T (x b)) + algebraMap O T (x b) * (a - algebraMap O T (x a)) := by
      rw [map_mul, map_mul]
      ring
    have hz : Φ (((a - algebraMap O T (x a)) * (b - algebraMap O T (x b))) • m0) = 0 := by
      rw [hm0, ← mul_smul,
        show (a - algebraMap O T (x a)) * (b - algebraMap O T (x b)) * (t * t) = (t * (a - algebraMap O T (x a))) * (t * (b - algebraMap O T (x b))) by ring,
        mul_smul]
      exact hΦK _ (hx0 a) _ (hker _ (hx0 b) v)
    rw [h, add_smul, add_smul, map_add, map_add, hz, zero_add, mul_smul (algebraMap O T (x a)), mul_smul (algebraMap O T (x b)), ← hO, ← hO, hΦO, hΦO]
  · intro τ σ hτσ hxτ
    show Φ ((τ - algebraMap O T (x τ)) • m0) = lam m0 • ell σ
    rw [sub_smul, hτσ, hxτ, ← hO, ← sub_smul, hΦ, map_sub th, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self,
      zero_smul, zero_add, map_sub ell, hell, sub_zero]
  · intro a ha hta
    show Φ ((a - algebraMap O T (x a)) • m0) = 0
    rw [ha, map_zero, sub_zero, hm0, ← mul_smul, show a * (t * t) = (t * a) * t by ring, mul_smul, hta, map_zero]
end

section
open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.dlam :
    ∀ (O σ : Type) [CommRing O] [DecidableEq σ] (th : MvPowerSeries σ O →ₐ[O] O) (k : σ), ∃ d : MvPowerSeries σ O →ₗ[O] O, (∀ a b, d (a * b) = th a • d b + th b • d a) ∧ ∀ k', d (MvPowerSeries.X k') = if k = k' then 1 else 0 := by
  intro O σ _ _ th k
  refine ⟨th.toLinearMap ∘ₗ (MvPowerSeries.pderiv O k).toLinearMap, ?_, ?_⟩
  · intro a b
    show th (MvPowerSeries.pderiv O k (a * b)) =
      th a • th (MvPowerSeries.pderiv O k b) + th b • th (MvPowerSeries.pderiv O k a)
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, smul_eq_mul,
      smul_eq_mul]
  · intro k'
    show th (MvPowerSeries.pderiv O k (MvPowerSeries.X k')) = if k = k' then 1 else 0
    by_cases h : k = k'
    · subst h
      rw [MvPowerSeries.pderiv_X_self, map_one, if_pos rfl]
    · rw [MvPowerSeries.pderiv_X_of_ne (Ne.symm h), map_zero, if_neg h]
end

section
open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.ell :
    ∀ (O Λ Γ X : Type) [CommRing O] [CommRing Λ] [Algebra O Λ] [CommGroup Γ] [AddCommGroup X] [Module O X] (th₀ : Λ →ₐ[O] O) (d : Λ →ₗ[O] X) (χ : Γ →* Multiplicative X), (∀ a b, d (a * b) = th₀ a • d b + th₀ b • d a) → ∃ (th : MonoidAlgebra Λ Γ →ₐ[O] O) (ell : MonoidAlgebra Λ Γ →ₗ[O] X), (∀ g a, th (MonoidAlgebra.single g a) = th₀ a) ∧ (∀ a b, ell (a * b) = th a • ell b + th b • ell a) ∧ ∀ g a, ell (MonoidAlgebra.single g a) = d a + th₀ a • Multiplicative.toAdd (χ g) :=
  _root_.UpperTheory.Reformulated.B.Qh12.ell
end

section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.chi :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] (q n m : ℕ) (a : Fin q → ℕ), (∀ j, m ≤ a j) → ∀ p : Fin q × Fin n, ∃ χ : Del l n a →* Multiplicative (Om O m), ∀ p', χ (Pi.mulSingle p' (Multiplicative.ofAdd 1)) = Multiplicative.ofAdd (if p = p' then 1 else 0) := by
  intro l _ O _ _ _ _ q n m a ha p
  have hl : (l : O) ∈ maximalIdeal O := by
    haveI : CharP (ResidueField O) l := IsCoef.char
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have h0 : (zmultiplesHom (Om O m) 1) ((l ^ a p.1 : ℕ) : ℤ) = 0 := by
    have : ((l : O) ^ a p.1) ∈ maximalIdeal O ^ m :=
      Ideal.pow_le_pow_right (ha _) (Ideal.pow_mem_pow hl _)
    have h2 := Ideal.Quotient.eq_zero_iff_mem.mpr this
    simpa using h2
  let f : ZMod (l ^ a p.1) →+ Om O m := ZMod.lift _ ⟨zmultiplesHom (Om O m) 1, h0⟩
  have f1 : f 1 = 1 := by
    have := ZMod.lift_coe (l ^ a p.1) ⟨zmultiplesHom (Om O m) 1, h0⟩ 1
    simpa [f] using this
  refine ⟨(AddMonoidHom.toMultiplicative f).comp
    (Pi.evalMonoidHom (fun p : Fin q × Fin n => Multiplicative (ZMod (l ^ a p.1))) p), fun p' => ?_⟩
  by_cases h : p = p'
  · subst h
    simp [f1]
  · simp [h, Pi.mulSingle_eq_of_ne h]
end

section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem core {O Λ R T M Γ X ι : Type} [CommRing O] [CommRing Λ] [CommRing R] [CommRing T] [Algebra O Λ] [Algebra O R]
    [Algebra Λ R] [IsScalarTower O Λ R] [Algebra R T] [Algebra O T] [IsScalarTower O R T] [AddCommGroup M] [Module R M]
    [Module Λ M] [IsScalarTower Λ R M] [CommGroup Γ] [AddCommGroup X] [Module O X]
    (act : T →ₐ[R] Module.End R M) (ρ : Representation Λ Γ M) (hP : Module.Projective (MonoidAlgebra Λ Γ) ρ.asModule)
    (gen : ι → Γ) (y : ι → T) (hρ : ∀ p m, ρ (gen p) m = act (1 + y p) m) (xT : T →ₐ[O] O) (hy : ∀ p, xT (y p) = 0)
    (hτ : ∀ g, ∃ τ, xT τ = 1 ∧ ∀ m, ρ g m = act τ m) (lam : M →+ O) (hlam : ∀ τ w, lam (act τ w) = xT τ * lam w)
    (t : T) (v : M) (I : Ideal R) (hI : I ≤ Ideal.span {s | ∃ a : Λ, s = algebraMap _ R a ∧ xT (algebraMap R T s) = 0})
    (ht : ∀ a, xT a = 0 → ∀ w, act (t * a) w ∈ (I • ⊤ : Submodule R M) ⊔ ⨆ p, LinearMap.range (act (y p)))
    (th₀ : Λ →ₐ[O] O) (h₀ : ∀ a, th₀ a = xT (algebraMap R T (algebraMap Λ R a))) (d : Λ →ₗ[O] X) (hd : IsDer th₀ d)
    (χ : Γ →* Multiplicative X) :
    ∃ del : T →ₗ[O] X, IsDer xT del ∧ (∀ a, del (algebraMap R T (algebraMap Λ R a)) = (xT t ^ 2 * lam v) • d a) ∧
      (∀ p, del (y p) = (xT t ^ 2 * lam v) • Multiplicative.toAdd (χ (gen p))) ∧ ∀ s, xT s = 0 → act (t * s) = 0 → del s = 0 := by
  classical
  obtain ⟨th, ell, hth, hell, hells⟩ := UpperTheory.V.Th.Sp.ell O Λ Γ X th₀ d χ hd
  have hact_alg : ∀ (r : R) (w : M), act (algebraMap R T r) w = r • w := by
    intro r w
    rw [AlgHom.commutes]
    rfl
  have hΛ : ∀ (a : Λ) (w : M), a • w = act (algebraMap R T (algebraMap Λ R a)) w := by
    intro a w
    rw [hact_alg, algebraMap_smul]
  have hcommρ : ∀ (τ : T) (g : Γ) (w : M), act τ (ρ g w) = ρ g (act τ w) := by
    intro τ g w
    obtain ⟨τ', -, h2⟩ := hτ g
    rw [h2, h2, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  have hcommΛ : ∀ (τ : T) (a : Λ) (w : M), act τ (a • w) = a • act τ w := by
    intro τ a w
    rw [hΛ, hΛ, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  have hd1 : d 1 = 0 := by
    have h11 : d (1 * 1) = th₀ 1 • d 1 + th₀ 1 • d 1 := hd 1 1
    simpa using h11
  have hell1 : ell 1 = 0 := by
    have h11 := hell 1 1
    simpa using h11
  letI : Module T ρ.asModule := Module.compHom M act.toRingHom
  have hsmulT : ∀ (τ : T) (x : ρ.asModule), τ • x = ρ.asModuleEquiv.symm (act τ (ρ.asModuleEquiv x)) :=
    fun _ _ => rfl
  have hS1 : ∀ (g : Γ) (a : Λ) (x : ρ.asModule),
      MonoidAlgebra.single g a • x = ρ.asModuleEquiv.symm (a • ρ g (ρ.asModuleEquiv x)) := by
    intro g a x
    rw [← LinearMap.smul_apply, ← Representation.asAlgebraHom_single, ← Representation.asModuleEquiv_map_smul,
      LinearEquiv.symm_apply_apply]
  haveI : SMulCommClass (MonoidAlgebra Λ Γ) T ρ.asModule := ⟨fun σ τ x => by
    induction σ using MonoidAlgebra.induction_linear with
    | zero => rw [zero_smul, zero_smul, smul_zero]
    | add f g hf hg => rw [add_smul, add_smul, smul_add, hf, hg]
    | single g a =>
      simp only [hS1, hsmulT, LinearEquiv.apply_symm_apply, hcommΛ, hcommρ]⟩
  haveI := hP
  let lam' : ρ.asModule →+ O := lam.comp ρ.asModuleEquiv.toLinearMap.toAddMonoidHom
  have hlam'e : ∀ x, lam' x = lam (ρ.asModuleEquiv x) := fun _ => rfl
  have hlam' : ∀ (σ : MonoidAlgebra Λ Γ) (x : ρ.asModule), lam' (σ • x) = th σ * lam' x := by
    intro σ x
    induction σ using MonoidAlgebra.induction_linear with
    | zero => rw [zero_smul, map_zero, map_zero, zero_mul]
    | add f g hf hg => rw [add_smul, map_add, hf, hg, map_add, add_mul]
    | single g a =>
      obtain ⟨τ, h1, h2⟩ := hτ g
      rw [hS1, hlam'e, hlam'e, LinearEquiv.apply_symm_apply, hΛ, hlam, h2, hlam, h1, one_mul, hth, h₀]
  obtain ⟨Φ, hΦ⟩ := UpperTheory.V.Th.Sp.phi (MonoidAlgebra Λ Γ) ρ.asModule O X th.toRingHom ell.toAddMonoidHom lam'
    (fun a b => hell a b) (fun σ x => hlam' σ x)
  have hKT : ∀ (τ : T) (x : ρ.asModule), x ∈ (RingHom.ker th • ⊤ : Submodule (MonoidAlgebra Λ Γ) ρ.asModule) →
      τ • x ∈ (RingHom.ker th • ⊤ : Submodule (MonoidAlgebra Λ Γ) ρ.asModule) := by
    intro τ x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro σ hσ n _
      rw [← smul_comm σ τ n]
      exact Submodule.smul_mem_smul hσ trivial
    · intro x y hx hy
      rw [smul_add]
      exact add_mem hx hy
  let N' : Submodule R M :=
    { carrier := {w | ρ.asModuleEquiv.symm w ∈ (RingHom.ker th • ⊤ : Submodule (MonoidAlgebra Λ Γ) ρ.asModule)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add] at *
        exact add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero]
        exact zero_mem _
      smul_mem' := by
        intro r w hw
        simp only [Set.mem_setOf_eq] at *
        have e : ρ.asModuleEquiv.symm (r • w) = (algebraMap R T r) • ρ.asModuleEquiv.symm w := by
          rw [hsmulT, LinearEquiv.apply_symm_apply, hact_alg]
        rw [e]
        exact hKT _ _ hw }
  have hmemN : ∀ w, w ∈ N' ↔
      ρ.asModuleEquiv.symm w ∈ (RingHom.ker th • ⊤ : Submodule (MonoidAlgebra Λ Γ) ρ.asModule) := fun _ => Iff.rfl
  have hy_eq : ∀ (p : ι) (w : M), ρ.asModuleEquiv.symm (act (y p) w) =
      (MonoidAlgebra.single (gen p) (1 : Λ) - 1) • ρ.asModuleEquiv.symm w := by
    intro p w
    have e : act (y p) w = ρ (gen p) w - w := by
      rw [hρ, map_add, map_one, LinearMap.add_apply, Module.End.one_apply, add_sub_cancel_left]
    rw [e, map_sub, sub_smul, one_smul, hS1, one_smul, LinearEquiv.apply_symm_apply]
  have hker_y : ∀ p : ι, MonoidAlgebra.single (gen p) (1 : Λ) - 1 ∈ RingHom.ker th := by
    intro p
    rw [RingHom.mem_ker, map_sub, map_one, hth, map_one, sub_self]
  have hN' : I • ⊤ ⊔ ⨆ p, LinearMap.range (act (y p)) ≤ N' := by
    refine sup_le ?_ (iSup_le fun p => ?_)
    · have key : ∀ r ∈ Ideal.span {s | ∃ a : Λ, s = algebraMap _ R a ∧ xT (algebraMap R T s) = 0},
          ∀ w : M, r • w ∈ N' := by
        intro r hr
        induction hr using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨a, rfl, ha⟩ := hx
          intro w
          rw [hmemN, algebraMap_smul]
          have e2 : ρ.asModuleEquiv.symm (a • w) = MonoidAlgebra.single (1 : Γ) a • ρ.asModuleEquiv.symm w := by
            rw [hS1, map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply]
          rw [e2]
          refine Submodule.smul_mem_smul ?_ Submodule.mem_top
          rw [RingHom.mem_ker, hth, h₀]
          exact ha
        | zero =>
          intro w
          rw [zero_smul]
          exact N'.zero_mem
        | add x y _ _ hx hy =>
          intro w
          rw [add_smul]
          exact N'.add_mem (hx w) (hy w)
        | smul c x _ hx =>
          intro w
          rw [smul_eq_mul, mul_smul]
          exact N'.smul_mem c (hx w)
      exact Submodule.smul_le.2 fun r hr w _ => key r (hI hr) w
    · rintro _ ⟨w, rfl⟩
      rw [hmemN, hy_eq]
      exact Submodule.smul_mem_smul (hker_y p) trivial
  have h5 : ∀ a : T, xT a = 0 → ∀ m : ρ.asModule,
      (t * a) • m ∈ (RingHom.ker th • ⊤ : Submodule (MonoidAlgebra Λ Γ) ρ.asModule) := by
    intro a ha m
    exact hN' (ht a ha (ρ.asModuleEquiv m))
  have hOS : ∀ (o : O) (m : ρ.asModule), algebraMap O (MonoidAlgebra Λ Γ) o • m = algebraMap O T o • m := by
    intro o m
    rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, hS1, map_one, Module.End.one_apply, hsmulT,
      IsScalarTower.algebraMap_apply O R T, hact_alg, IsScalarTower.algebraMap_apply O Λ R, algebraMap_smul R (algebraMap O Λ o)]
  obtain ⟨del, hdel1, hdel2, hdel3⟩ := UpperTheory.V.Th.Sp.der O (MonoidAlgebra Λ Γ) T ρ.asModule X th xT ell lam' Φ t
    (ρ.asModuleEquiv.symm v) hOS hell1 hlam' hΦ h5
  have hc : lam' ((t * t) • ρ.asModuleEquiv.symm v) = xT t ^ 2 * lam v := by
    rw [hlam'e, hsmulT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hlam, map_mul, pow_two]
  refine ⟨del, hdel1, ?_, ?_, ?_⟩
  · intro a
    rw [hdel2 (algebraMap R T (algebraMap Λ R a)) (MonoidAlgebra.single 1 a) ?_ ?_, hc, hells, map_one,
      toAdd_one, smul_zero, add_zero]
    · intro m
      rw [hsmulT, hS1, map_one, Module.End.one_apply, ← hΛ]
    · rw [hth, h₀]
  · intro p
    rw [hdel2 (y p) (MonoidAlgebra.single (gen p) (1 : Λ) - 1) ?_ ?_, hc, map_sub, hells, hell1, hd1, map_one,
      one_smul, zero_add, sub_zero]
    · intro m
      rw [hsmulT, hy_eq, LinearEquiv.symm_apply_apply]
    · rw [hy]
      exact ((RingHom.mem_ker).1 (hker_y p)).symm
  · intro s hs h0
    refine hdel3 s hs fun m => ?_
    rw [hsmulT, h0, LinearMap.zero_apply, map_zero]

private theorem gen_all {l q n : ℕ} (hl : l.Prime) (a : Fin q → ℕ) (S : Submonoid (Del l n a))
    (h : ∀ p, (Pi.mulSingle p (Multiplicative.ofAdd 1) : Del l n a) ∈ S) (g : Del l n a) : g ∈ S := by
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ a p.1) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  rw [← Finset.univ_prod_mulSingle g]
  refine Submonoid.prod_mem _ fun s _ => ?_
  have h1 : g s = Multiplicative.ofAdd (1 : ZMod (l ^ a s.1)) ^ (Multiplicative.toAdd (g s)).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [h1, Pi.mulSingle_pow]
  exact Submonoid.pow_mem _ (h s) _

theorem UpperTheory.V.Th.Sp.derOp :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N) (xT : PUY A.R q n →ₐ[O] O) (lam : A.M1 →+ O) (t : PUY A.R q n) (v : A.M1) (I : Ideal A.R) (m : ℕ), m ≤ N → (∀ j i, xT (yV A.R j i) = 0) → (∀ τ w, lam (A.act1 τ w) = xT τ * lam w) → I ≤ Ideal.span {s | ∃ a : abelian₂ O Empty D, s = algebraMap _ A.R a ∧ xT (MvPolynomial.C s) = 0} → (∀ a, xT a = 0 → ∀ w, A.act1 (t * a) w ∈ (I • ⊤ : Submodule A.R A.M1) ⊔ ⨆ p : Fin q × Fin n, LinearMap.range (A.act1 (yV A.R p.1 p.2))) → ∀ a : Fin D ⊕ Fin q × Fin n, ∃ del : PUY A.R q n →ₗ[O] Om O m, IsDer xT del ∧ (∀ k, del (MvPolynomial.C (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k)))) = if a = .inl k then algebraMap O _ (xT t ^ 2 * lam v) else 0) ∧ (∀ j i, del (yV A.R j i) = if a = .inr (j, i) then algebraMap O _ (xT t ^ 2 * lam v) else 0) ∧ ∀ s, xT s = 0 → A.act1 (t * s) = 0 → del s = 0 := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A xT lam t v I m hm hy hlam hI ht a
  have hτ : ∀ g : Del l n A.a, ∃ τ, xT τ = 1 ∧ ∀ w, A.ρ g w = A.act1 τ w := by
    intro g
    let S : Submonoid (Del l n A.a) :=
      { carrier := {g | ∃ τ, xT τ = 1 ∧ ∀ w, A.ρ g w = A.act1 τ w}
        mul_mem' := by
          rintro g1 g2 ⟨τ1, h1, e1⟩ ⟨τ2, h2, e2⟩
          refine ⟨τ1 * τ2, by rw [map_mul, h1, h2, one_mul], fun w => ?_⟩
          rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e2, e1]
        one_mem' := ⟨1, map_one _, fun w => by
          rw [map_one, map_one]
          rfl⟩ }
    have hg := gen_all (Fact.out : l.Prime) A.a S (fun p => ⟨1 + yV A.R p.1 p.2,
      by rw [map_add, map_one, hy, add_zero], A.ρ_gen p.1 p.2⟩) g
    exact hg
  let th₀ : abelian₂ O Empty D →ₐ[O] O :=
    (xT.comp (IsScalarTower.toAlgHom O A.R (PUY A.R q n))).comp (IsScalarTower.toAlgHom O (abelian₂ O Empty D) A.R)
  have h₀ : ∀ x, th₀ x = xT (algebraMap A.R (PUY A.R q n) (algebraMap (abelian₂ O Empty D) A.R x)) := fun _ => rfl
  obtain ⟨d, hd, hdX⟩ : ∃ d : abelian₂ O Empty D →ₗ[O] Om O m, IsDer th₀ d ∧
      ∀ k, d (MvPowerSeries.X (.inr k)) = if a = .inl k then 1 else 0 := by
    cases a with
    | inl k0 =>
      obtain ⟨d0, hd0, hX⟩ := UpperTheory.V.Th.Sp.dlam O (Empty ⊕ Fin D) th₀ (.inr k0)
      refine ⟨(Ideal.Quotient.mkₐ O (maximalIdeal O ^ m)).toLinearMap.comp d0, ?_, ?_⟩
      · intro x y
        simp only [LinearMap.comp_apply, hd0, map_add, map_smul]
      · intro k
        simp only [LinearMap.comp_apply, hX, Sum.inr.injEq, Sum.inl.injEq]
        split_ifs <;> simp
    | inr p0 =>
      refine ⟨0, ?_, ?_⟩
      · intro x y
        simp
      · intro k
        simp
  obtain ⟨χ, hχ⟩ : ∃ χ : Del l n A.a →* Multiplicative (Om O m), ∀ p : Fin q × Fin n,
      χ (Pi.mulSingle p (Multiplicative.ofAdd 1)) = Multiplicative.ofAdd (if a = .inr p then 1 else 0) := by
    cases a with
    | inl k0 =>
      refine ⟨1, fun p => ?_⟩
      simp
    | inr p0 =>
      obtain ⟨χ0, hχ0⟩ := UpperTheory.V.Th.Sp.chi l O q n m A.a (fun j => hm.trans (A.le_a j)) p0
      refine ⟨χ0, fun p => ?_⟩
      rw [hχ0]
      simp only [Sum.inr.injEq]
  obtain ⟨del, hdel, hΛv, hyv, hkill⟩ := core A.act1 A.ρ A.proj
    (fun p : Fin q × Fin n => (Pi.mulSingle p (Multiplicative.ofAdd 1) : Del l n A.a))
    (fun p => yV A.R p.1 p.2) (fun p w => A.ρ_gen p.1 p.2 w) xT (fun p => hy p.1 p.2) hτ lam hlam t v I hI ht
    th₀ h₀ d hd χ
  refine ⟨del, hdel, ?_, ?_, hkill⟩
  · intro k
    have hk := hΛv (MvPowerSeries.X (.inr k))
    rw [hdX] at hk
    refine hk.trans ?_
    split_ifs
    · exact (Algebra.algebraMap_eq_smul_one _).symm
    · exact smul_zero _
  · intro j i
    have hji := hyv (j, i)
    rw [hχ, toAdd_ofAdd] at hji
    refine hji.trans ?_
    split_ifs
    · exact (Algebra.algebraMap_eq_smul_one _).symm
    · exact smul_zero _
end

section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem fEl_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {q n : ℕ} (Nq : Fin q → ℕ) (u : Fin q → Fin n → R) :
    f (fEl Nq u) = fEl Nq fun j i => f (u j i) := by
  simp [fEl]

private theorem chi_rep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem g_dvd {O : Type} [CommRing O] {q n : ℕ} (Nq : Fin q → ℕ) (α : Fin q → Fin n → O) :
    (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) ∣ fEl Nq α :=
  Finset.prod_dvd_prod_of_dvd _ _ fun _ _ => Finset.prod_dvd_prod_of_dvd _ _ fun _ _ =>
    Finset.prod_dvd_prod_of_dvd _ _ fun _ _ => dvd_mul_right _ _

private theorem e_dvd {O : Type} [CommRing O] {q n : ℕ} (α : Fin q → Fin n → O) (j : Fin q) (i : Fin n) :
    (∏ k ∈ Finset.univ.erase i, (α j i - α j k)) ∣ ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k) :=
  (Finset.dvd_prod_of_mem (fun i => ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) (Finset.mem_univ i)).trans
    (Finset.dvd_prod_of_mem (fun j => ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) (Finset.mem_univ j))

private theorem num_dvd {O : Type} [CommRing O] (a g F e z c : O) (E : ℕ) (h1 : g ∣ F) (h2 : e ∣ F)
    (h : a ^ 2 * z * F ^ (3 * E + 6) ∣ c) : (a * g * F * F ^ E) ^ 2 * (F * z) * e ^ (E + 1) ∣ c := by
  refine Dvd.dvd.trans ?_ h
  obtain ⟨g', hg⟩ := h1
  obtain ⟨e', he⟩ := h2
  refine ⟨g' ^ 2 * e' ^ (E + 1), ?_⟩
  have : F ^ (3 * E + 6) = (g * g') ^ 2 * (F * F ^ E) ^ 2 * F * (e * e') ^ (E + 1) := by
    rw [← hg, ← he]; ring
  rw [this]; ring

theorem UpperTheory.V.Th.Sp.one :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N) (y : Pt G0.frame O n) (x : B →ₐ[O] O) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (E : ℕ) (α : Fin q → Fin n → O) (t₀ : B) (lam : b.M →+ O) (m₀ : b.M) (m : ℕ) (c : O), 1 ≤ n → GenBy O (pairVals u) → u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → (∀ a : B, x a = 0 → ∀ w : b.M, (t₀ * a) • w ∈ wtSub b x) → (∀ (a : B) w, lam (a • w) = x a * lam w) → (∀ j, h.p₀ (ta j) = 1) → (∀ j, (mat y.ρ (h.p₀ (ph j))).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α j k))) → OpRelX A Nq ph ta E → m ≤ N → x t₀ ^ 2 * lam m₀ * fEl Nq α ^ (3 * E + 6) ∣ c → ∀ a : Fin D ⊕ Fin q × Fin n, ∃ δ : A.R →ₗ[O] Om O m, IsDer (x.comp A.β) δ ∧ (∀ k, δ (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k))) = if a = .inl k then algebraMap O _ c else 0) ∧ ∀ j i, δ (A.p.D.tr (twoPowerModulus E (ph j) (ta j) (fun k => algebraMap O A.R (α j k)) i 0)) = if a = .inr (j, i) then algebraMap O _ c else 0 := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A y x Nq ph ta E α t₀ lam m₀ m c hn hgen hmap hEt hlam hta hα hA hN hc a
  have hs := Sp.betaSurj l L G0 G h n O r B u J D b q N A hgen
  have hβ := Sp.betaLam l L G0 G h n O r B u J D b q N A
  obtain ⟨t₁, rfl⟩ := hs t₀
  have hP : ∀ j, (u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)).map (x : B →+* O) =
      ∏ i, (Polynomial.X - Polynomial.C (α j i)) := fun j => by
    have h1 := ((UpperTheory.V.CA.d_gmap u.D).2.2.1 x.toRingHom (MonoidAlgebra.single (h.p₀ (ph j)) 1)).1
    rw [MonoidAlgebra.mapRingHom_single, map_one, hmap.1, chi_rep, hα j] at h1
    exact h1.symm
  obtain ⟨lw, v₀, hlw, hv₀⟩ := Sp.lamW O A.R B b.M A.Mw q n A.β x _ A.actw _ α lam m₀ hA.two hP hlam
  obtain ⟨htr, hker⟩ := Sp.trans A.R A.M1 A.Mw q n A.act1 A.actw A.tr A.tr_surj A.tr_ker A.tr_u
  obtain ⟨v, rfl⟩ := A.tr_surj v₀
  let xU : PU A.R q n →+* O := MvPolynomial.eval₂Hom ((x.comp A.β : A.R →ₐ[O] O) : A.R →+* O) fun p => α p.1 p.2
  let π : PUY A.R q n →ₐ[A.R] PU A.R q n := MvPolynomial.aeval (Sum.elim MvPolynomial.X 0)
  let xT : PUY A.R q n →ₐ[O] O :=
    { xU.comp (π : PUY A.R q n →+* PU A.R q n) with
      commutes' := fun o => by
        change xU (π (MvPolynomial.C (algebraMap O A.R o))) = o
        simp [xU, π] }
  have hxT : ∀ τ, xT τ = xU (π τ) := fun _ => rfl
  have hC : ∀ s, xT (MvPolynomial.C s) = x (A.β s) := fun s => by simp [hxT, xU, π]
  have hU : ∀ j k, xT (uV A.R j k) = α j k := fun j k => by simp [hxT, xU, π]
  have hY : ∀ j k, xT (yV A.R j k) = 0 := fun j k => by simp [hxT, xU, π]
  let I : Ideal A.R := (RingHom.ker (x.comp b.lam)).map (algebraMap (abelian₂ O Empty D) A.R)
  have hI : ∀ w, w ∈ wtSub b x → w ∈ (I.map A.β • ⊤ : Submodule B b.M) := fun w hw => by
    refine Submodule.smul_induction_on hw (fun s hs w _ => ?_) fun _ _ => add_mem
    rw [b.smul_lam, ← hβ]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hs)) trivial
  have hkill := Sp.kill O A.R B b.M A.Mw q n A.β x _ A.actw _ α I t₁ hs hA.two hP fun a ha w => hI _ (hEt a ha w)
  let t : PUY A.R q n := MvPolynomial.C t₁ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
    (uV A.R j i - MvPolynomial.C (algebraMap O A.R (α j k)))) * fEl Nq (uV A.R) * fEl Nq (uV A.R) ^ E
  have hF : xT (fEl Nq (uV A.R)) = fEl Nq α := by
    have := fEl_map (xT : PUY A.R q n →+* O) Nq (uV A.R)
    simpa [hU] using this
  have hxt : xT t = x (A.β t₁) * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) * fEl Nq α * fEl Nq α ^ E := by
    simp only [t, map_mul, map_pow, map_prod, map_sub, hC, hU, hF, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have hv : lw (A.tr v) = fEl Nq α * lam m₀ := by
    rw [hv₀]
    congr 1
    have := fEl_map xU Nq fun j i => MvPolynomial.X (j, i)
    simpa [xU] using this
  obtain ⟨del, hd, h1, h2, h3⟩ := Sp.derOp l L G0 G h n O r B u J D b q N A xT (lw.comp A.tr.toAddMonoidHom) t v I m hN hY
    (fun τ w => by
      change lw (A.tr (A.act1 τ w)) = xT τ * lw (A.tr w)
      rw [htr, hlw]; rfl)
    (Ideal.span_le.2 (by
      rintro _ ⟨s, hs, rfl⟩
      exact Ideal.subset_span ⟨s, rfl, by rw [hC, hβ]; exact hs⟩))
    (fun s hs w => hker I _ (by
      have hπ : π (fEl Nq (uV A.R)) = fEl Nq fun j i => MvPolynomial.X (j, i) := by
        have := fEl_map (π : PUY A.R q n →+* PU A.R q n) Nq (uV A.R)
        simpa [π] using this
      have e : π (t * s) = MvPolynomial.C t₁ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O A.R (α j k)))) * (fEl Nq fun j i => MvPolynomial.X (j, i)) *
          π (fEl Nq (uV A.R) ^ E * s) := by
        simp only [t, map_mul, map_prod, map_sub, hπ, mul_assoc]
        simp [π]
      rw [htr]
      change A.actw (π (t * s)) _ ∈ _
      rw [e]
      refine hkill _ ?_ _
      change xT _ = 0
      rw [map_mul, hs, mul_zero])) a
  have hv' : (lw.comp A.tr.toAddMonoidHom) v = fEl Nq α * lam m₀ := hv
  rw [hv'] at h1 h2
  have hq : ∀ j i, del (MvPolynomial.C (A.p.D.tr (twoPowerModulus E (ph j) (ta j) (fun k => algebraMap O A.R (α j k)) i 0))) =
      (∏ k ∈ Finset.univ.erase i, (α j i - α j k)) ^ (E + 1) • del (yV A.R j i) := fun j i => by
    obtain ⟨k1, k2⟩ := Sp.q2op l L G0 G h n O r B u J D b q N A y x (ph j) (ta j) (α j) E j i xT _ del hn hmap (hta j) (hα j)
      hC (hU j) (hY j i) hd
    have := h3 _ k1 (by
      simp only [t]
      rw [mul_assoc, map_mul, hA.rel2, mul_zero])
    rw [this] at k2
    exact sub_eq_zero.1 k2.symm
  let δ₀ : A.R →ₗ[O] Om O m := del ∘ₗ (IsScalarTower.toAlgHom O A.R (PUY A.R q n)).toLinearMap
  have hδ : ∀ s, δ₀ s = del (MvPolynomial.C s) := fun _ => rfl
  have hder : ∀ e : O, IsDer (x.comp A.β) (e • δ₀) := fun e s s' => by
    simp only [LinearMap.smul_apply, hδ, map_mul, hd _ _, hC, AlgHom.comp_apply, smul_add, smul_comm e]
  have hnum := fun j i => num_dvd _ _ _ _ _ c E (g_dvd Nq α) ((e_dvd α j i).trans (g_dvd Nq α)) hc
  have hn0 := num_dvd _ _ _ 1 _ c E (g_dvd Nq α) (one_dvd _) hc
  rw [← hxt] at hnum hn0
  rcases a with k | ⟨j, i⟩
  · obtain ⟨e, he⟩ := hn0
    refine ⟨e • δ₀, hder e, fun k' => ?_, fun j i => ?_⟩
    · rw [LinearMap.smul_apply, hδ, h1]
      split_ifs
      · rw [he, Algebra.smul_def, ← map_mul]; congr 1; ring
      · simp
    · rw [LinearMap.smul_apply, hδ, hq, h2]; simp
  · obtain ⟨e, he⟩ := hnum j i
    refine ⟨e • δ₀, hder e, fun k' => ?_, fun j' i' => ?_⟩
    · rw [LinearMap.smul_apply, hδ, h1]; simp
    · rw [LinearMap.smul_apply, hδ, hq, h2]
      split_ifs with hh
      · obtain ⟨rfl, rfl⟩ : j = j' ∧ i = i' := by simpa using hh
        rw [he, Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul]; congr 1; ring
      · simp
end
