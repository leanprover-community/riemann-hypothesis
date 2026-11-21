import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HarishChandraProjQuantumDetEqProd

section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_along {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (τ : E →+* ℂ) (z : ℂ) :
    Cm.mixEq E (GlobalTheory.CuspRep.atEmb τ z) = UpperTheory.ConvolutionTheory.along τ z := by
  refine Cm.mixed_ext fun w => ?_
  have h : (Cm.mixEq E (GlobalTheory.CuspRep.atEmb τ z)).2 w = GlobalTheory.CuspRep.atEmb τ z w.1 := Cm.mixRing_snd _ w
  rw [h, PositivityTheory.Rg.Cz.GK.atEmb_apply]
  simp only [UpperTheory.ConvolutionTheory.along]
  by_cases e : w.1 = InfinitePlace.mk τ
  · rw [if_pos e, if_pos e, e]
  · rw [if_neg e, if_neg e]

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_lie {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (τ : E →+* ℂ)
    (a b : Fin n) (z : ℂ) :
    Cm.ιC E n (GlobalTheory.CuspRep.toL (Matrix.single a b (GlobalTheory.CuspRep.atEmb τ z))) = (1 : ℂ) ⊗ₜ UpperTheory.ConvolutionTheory.elem τ a b z := by
  rw [Cm.ιC_apply, UpperTheory.ConvolutionTheory.elem]
  congr 2
  refine Subtype.ext ?_
  change Cm.matEq E n (Matrix.single a b (GlobalTheory.CuspRep.atEmb τ z)) = Matrix.single a b (UpperTheory.ConvolutionTheory.along τ z)
  refine Matrix.ext fun i j => ?_
  rw [Cm.matEq_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs
  · exact UpperTheory.ConvolutionTheory.Dp.jGen_along τ z
  · exact map_zero _

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_gen {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (τ : E →+* ℂ)
    (a b : Fin n) :
    (2⁻¹ : ℂ) ⊗ₜ UpperTheory.ConvolutionTheory.elem τ a b 1 - (2⁻¹ * Complex.I) ⊗ₜ UpperTheory.ConvolutionTheory.elem τ a b Complex.I = Cm.genC τ a b := by
  rw [Cm.genC, AlgRepEndIrreducible.eL, UpperTheory.ConvolutionTheory.Dp.jGen_lie, UpperTheory.ConvolutionTheory.Dp.jGen_lie, TensorProduct.smul_tmul', smul_sub,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  simp only [smul_eq_mul, mul_one, one_div]

private noncomputable def UpperTheory.ConvolutionTheory.Dp.jGen_lin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) :
    HarishChandra.gl n →ₗ[ℂ] A where
  toFun X := ∑ c : Fin n × Fin n, X c.1 c.2 • F c.1 c.2
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r X := by simp [Finset.smul_sum, mul_smul]

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_lin_E {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (c : Fin n × Fin n) : UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E c) = F c.1 c.2 := by
  change ∑ d : Fin n × Fin n, (HarishChandra.E c) d.1 d.2 • F d.1 d.2 = _
  rw [Finset.sum_eq_single c]
  · simp [HarishChandra.E]
  · intro d _ hd
    have : ¬ (c.1 = d.1 ∧ c.2 = d.2) := fun h => hd (Prod.ext h.1.symm h.2.symm)
    simp [HarishChandra.E, Matrix.single_apply, this]
  · simp

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_lin_lie {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) (X Y : HarishChandra.gl n) :
    UpperTheory.ConvolutionTheory.Dp.jGen_lin F ⁅X, Y⁆ = ⁅UpperTheory.ConvolutionTheory.Dp.jGen_lin F X, UpperTheory.ConvolutionTheory.Dp.jGen_lin F Y⁆ := by
  have hE : ∀ c d : Fin n × Fin n, UpperTheory.ConvolutionTheory.Dp.jGen_lin F ⁅HarishChandra.E c, HarishChandra.E d⁆ =
      ⁅UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E c), UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E d)⁆ := by
    intro c d
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, HarishChandra.E_mul_sub_mul,
      UpperTheory.ConvolutionTheory.Dp.jGen_lin_E, UpperTheory.ConvolutionTheory.Dp.jGen_lin_E, hF, map_sub]
    congr 1 <;> split_ifs <;> simp [UpperTheory.ConvolutionTheory.Dp.jGen_lin_E]
  rw [HarishChandra.eq_sum_E X, HarishChandra.eq_sum_E Y]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE]

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_ex {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) : ∃ f : HarishChandra.U n →ₐ[ℂ] A, ∀ a b, f (HarishChandra.e (a, b)) = F a b := by
  let L : HarishChandra.gl n →ₗ⁅ℂ⁆ A :=
    { UpperTheory.ConvolutionTheory.Dp.jGen_lin F with map_lie' := fun {X Y} => UpperTheory.ConvolutionTheory.Dp.jGen_lin_lie F hF X Y }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ L, fun a b => ?_⟩
  rw [HarishChandra.e, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact UpperTheory.ConvolutionTheory.Dp.jGen_lin_E F (a, b)

theorem UpperTheory.ConvolutionTheory.Dp.jGen :
    UpperTheory.ConvolutionTheory.Dp.JGen := by
  intro E _ _ _ n τ
  have key : ∀ j : HarishChandra.U n →ₐ[ℂ] UpperTheory.ConvolutionTheory.UC E n,
      UpperTheory.ConvolutionTheory.IsJ (n := n) τ j ↔ ∀ a b, j (HarishChandra.e (a, b)) = Cm.genC τ a b := fun j =>
    ⟨fun h a b => (h a b).trans (UpperTheory.ConvolutionTheory.Dp.jGen_gen τ a b),
      fun h a b => (h a b).trans (UpperTheory.ConvolutionTheory.Dp.jGen_gen τ a b).symm⟩
  obtain ⟨f, hf⟩ := UpperTheory.ConvolutionTheory.Dp.jGen_ex (Cm.genC (a := n) τ) (Cm.glRel_genC τ)
  exact ⟨⟨f, (key f).2 hf⟩, key⟩
end

section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

open GroundTheory.Automorphic.HarishChandra in
private theorem UpperTheory.ConvolutionTheory.Dp.capHC_mem (n : ℕ) (u : ℂ) :
    Formalism.REAL.qdet (fun i j : Fin n => e (i, j)) u ∈ Subalgebra.center ℂ (U n) := by
  have hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) := by
    intro i j k l
    exact e_mul_sub_mul (i, j) (k, l)
  refine mem_center_of_commute_e fun a => ?_
  exact (Formalism.REAL.qDetCentral (U n) n _ hgl u a.1 a.2).symm

theorem UpperTheory.ConvolutionTheory.Dp.capHC :
    UpperTheory.ConvolutionTheory.Dp.CapHC := by
  intro n u
  refine ⟨⟨_, capHC_mem n (u + ((n : ℂ) - 1) / 2)⟩, rfl, ?_⟩
  rw [HarishChandra.harishChandraHom_apply]
  dsimp only
  rw [UpperTheory.harishChandraProj_quantumDet_eq_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold GroundTheory.Automorphic.HarishChandra.translate
  rw [map_add, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
    add_comm (MvPolynomial.X k), ← add_assoc, ← map_add]
  congr 2
  simp only [HarishChandra.rhoVec, Pi.neg_apply]
  ring
end

section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem UpperTheory.ConvolutionTheory.Dp.capZc_mem_of_e {n : ℕ} (S : Subalgebra ℂ (HarishChandra.U n))
    (h : ∀ a b, HarishChandra.e (a, b) ∈ S) (x : HarishChandra.U n) : x ∈ S := by
  induction x using HarishChandra.U.induction with
  | halg r => exact S.algebraMap_mem r
  | hι X =>
    rw [HarishChandra.ι_eq_sum_e]
    exact S.sum_mem fun a _ => S.smul_mem (h a.1 a.2) _
  | hmul a b ha hb => exact S.mul_mem ha hb
  | hadd a b ha hb => exact S.add_mem ha hb

private theorem UpperTheory.ConvolutionTheory.Dp.capZc_prod (n : ℕ) (u : ℂ) :
    (∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k) : MvPolynomial (Fin n) ℂ) =
      u ^ n • (1 : MvPolynomial (Fin n) ℂ) +
        ∑ i : Fin n, u ^ (n - (i + 1)) • MvPolynomial.esymm (Fin n) ℂ (i + 1) := by
  have h := congrArg (Polynomial.eval (MvPolynomial.C u : MvPolynomial (Fin n) ℂ))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Fintype.card_fin] at h
  rw [h, Finset.sum_range_succ', add_comm, ← Fin.sum_univ_eq_sum_range
    (fun i => MvPolynomial.esymm (Fin n) ℂ (i + 1) * MvPolynomial.C u ^ (n - (i + 1))) n]
  congr 1
  · rw [MvPolynomial.esymm_zero, MvPolynomial.smul_eq_C_mul, map_pow, Nat.sub_zero, mul_comm]
  · exact Finset.sum_congr rfl fun i _ => by rw [MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]

private theorem UpperTheory.ConvolutionTheory.Dp.capZc_center {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}
    {z : Cm.UC E n} (h : ∀ τ i j, Cm.genC τ i j * z = z * Cm.genC τ i j) :
    z ∈ Subalgebra.center ℂ (Cm.UC E n) := by
  have : Algebra.adjoin ℂ {x : Cm.UC E n | ∃ τ i j, x = Cm.genC τ i j} ≤ Subalgebra.centralizer ℂ {z} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩ _ rfl
    exact (h τ i j).symm
  exact Subalgebra.mem_center_iff.2 fun x =>
    (this (Cm.adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top) z rfl).symm

theorem UpperTheory.ConvolutionTheory.Dp.capZc :
    UpperTheory.ConvolutionTheory.Dp.CapZc := by
  intro E _ _ _ n τ
  obtain ⟨⟨j, hj⟩, hiff⟩ := UpperTheory.ConvolutionTheory.Dp.jGen E n τ
  have hg := (hiff j).1 hj
  set w : Fin n → Subalgebra.center ℂ (HarishChandra.U n) := fun i =>
    (HarishChandra.harishChandraEquiv (n := n)).symm
      ⟨MvPolynomial.esymm (Fin n) ℂ (i + 1), MvPolynomial.esymm_isSymmetric (Fin n) ℂ (i + 1)⟩ with hw
  have hzc : ∀ i : Fin n, UpperTheory.ConvolutionTheory.zc τ i = j (w i) := fun i => by
    obtain ⟨j', hj', e⟩ := Classical.epsilon_spec
      (p := fun z => ∃ j, UpperTheory.ConvolutionTheory.IsJ τ j ∧ z = j (w i : HarishChandra.U n)) ⟨_, j, hj, rfl⟩
    refine e.trans ?_
    exact capZc_mem_of_e (AlgHom.equalizer j' j) (fun a b => ((hiff j').1 hj' a b).trans (hg a b).symm) _
  have hwH : ∀ i, HarishChandra.harishChandraHom (w i) = MvPolynomial.esymm (Fin n) ℂ (i + 1) := fun i => by
    rw [← HarishChandra.harishChandraEquiv_apply, hw, AlgEquiv.apply_symm_apply]
  refine ⟨fun i => ?_, fun u => ?_⟩
  · rw [hzc]
    refine capZc_center fun σ a b => ?_
    by_cases e : σ = τ
    · subst e
      rw [← hg]
      exact (map_mul j _ _).symm.trans
        ((congrArg j (Subalgebra.mem_center_iff.1 (w i).2 _)).trans (map_mul j _ _))
    · have := capZc_mem_of_e ((Subalgebra.centralizer ℂ {Cm.genC σ a b}).comap j) (fun c d => by
        rintro _ rfl
        rw [RingHom.coe_coe, hg]
        exact Cm.commute_genC e a b c d) (w i)
      exact this _ rfl
  · obtain ⟨z, hz, hH⟩ := UpperTheory.ConvolutionTheory.Dp.capHC n u
    have e : z = u ^ n • 1 + ∑ i : Fin n, u ^ (n - (i + 1)) • w i := by
      apply HarishChandra.harishChandraHom_injective
      rw [hH, capZc_prod]
      simp only [map_add, map_smul, map_one, map_sum, hwH]
    have e2 := congrArg (j.comp (Subalgebra.center ℂ (HarishChandra.U n)).val) e
    simp only [map_add, map_smul, map_one, map_sum] at e2
    simp only [hzc]
    refine Eq.trans ?_ e2
    change _ = j (z : HarishChandra.U n)
    rw [hz, Fb.map_qdet]
    simp only [hg]
    rfl
end
