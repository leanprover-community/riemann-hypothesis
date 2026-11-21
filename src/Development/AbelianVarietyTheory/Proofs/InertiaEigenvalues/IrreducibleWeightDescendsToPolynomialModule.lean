import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonzeroMatrixIntertwinerDescendsToSubfield
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightDominantIsoExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightSpanOfIndep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AlgWtDualRead

theorem isAlgWeight_of_hwAtF_dual : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (κ : Type) [Fintype κ] [DecidableEq κ] (b : Module.Basis κ K W) (ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (κ → ℂ)), (∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e) → ∀ (τ : L →+* K) (lam : Fin n → ℤ), NX.HWAtF c ρ.dual τ lam → Formalism.AUTREP.IsAlgWeight L n ρC := by
  intro L _ _ _ n K _ e c hc W _ _ _ ρ κ _ _ b ρC hρC τ lam hw
  obtain ⟨ι, _, _, b', P, hP, -⟩ := hw
  classical
  let bd := b.dualBasis
  let A : Matrix κ ι K := bd.toMatrix b'
  let B : Matrix ι κ K := b'.toMatrix bd
  let f : (L →+* K) × Fin n × Fin n → (L →+* K) × Fin n × Fin n := fun p => (p.1.comp c, p.2.2, p.2.1)
  let Q : κ → κ → MvPolynomial ((L →+* K) × Fin n × Fin n) K := fun i j =>
    ∑ l, ∑ k, MvPolynomial.C (A j k) * MvPolynomial.rename f (P k l) * MvPolynomial.C (B l i)
  have key : ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : Formalism.AUTREP.GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
      ∀ i j, LinearMap.toMatrix b b (ρ γ) i j =
        MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (Q i j) := by
    intro γ γ₀ hm i j
    have hinv := hP γ⁻¹ γ₀⁻¹ (GlobalTheory.WtDual.match_inv γ γ₀ hm)
    have hγ := GlobalTheory.WtDual.mem_rationalUnitaryGroup_of_matrix_match γ γ₀ hm
    have e1 : LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) = Matrix.transpose (LinearMap.toMatrix b b (ρ γ)) := by
      rw [Representation.dual_apply, inv_inv, LinearMap.toMatrix_transpose]
    have e2 : LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) = A * LinearMap.toMatrix b' b' (ρ.dual γ⁻¹) * B :=
      (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bd b' bd b' _).symm
    have e3 : LinearMap.toMatrix b b (ρ γ) i j = LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) j i := by
      rw [e1]; rfl
    rw [e3, e2]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    simp only [hinv]
    simp only [Q, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_rename]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    refine congrArg (fun g => MvPolynomial.eval g (P k l)) (funext fun p => ?_)
    simp only [Function.comp_apply, f, RingHom.comp_apply]
    rw [GlobalTheory.WtDual.inv_entry γ₀ hγ, hc]
    rfl
  refine ⟨inferInstance, κ, inferInstance, inferInstance, Pi.basisFun ℂ κ,
    fun i j => MvPolynomial.rename (fun p : (L →+* K) × Fin n × Fin n => (e.comp p.1, p.2)) (MvPolynomial.map e (Q i j)), ?_⟩
  intro γ γ₀ hm
  ext i j
  rw [LinearMap.toMatrix_eq_toMatrix', hρC γ, Matrix.map_apply, key γ γ₀ hm i j, MvPolynomial.eval_rename,
    MvPolynomial.eval_map]
  simp only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.hom_eval₂, RingHom.comp_id]
  rfl

end GlobalTheory.AlgWtDualRead
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgWeight_of_contragredient_highestWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (κ : Type) [Fintype κ] [DecidableEq κ] (b : Module.Basis κ K W) (ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (κ → ℂ)), (∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e) → ∀ (τ : L →+* K) (lam : Fin n → ℤ), NX.HWAtF c ρ.dual τ lam → Formalism.AUTREP.IsAlgWeight L n ρC := by
  atlas_forward_decl GlobalTheory.AlgWtDualRead.isAlgWeight_of_hwAtF_dual
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AlgSubrep

theorem toMatrix_sandwich {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (e : Module.Basis κ ℂ U) (π : V →ₗ[ℂ] U) (s : U →ₗ[ℂ] V)
    (f : V →ₗ[ℂ] V) :
    LinearMap.toMatrix e e (π ∘ₗ f ∘ₗ s) =
      LinearMap.toMatrix b e π * LinearMap.toMatrix b b f * LinearMap.toMatrix e b s := by
  rw [LinearMap.toMatrix_comp e b e, LinearMap.toMatrix_comp e b b, Matrix.mul_assoc]

theorem eval_sandwich {ι κ σ : Type} [Fintype ι] [Fintype κ] (A : Matrix κ ι ℂ) (B : Matrix ι κ ℂ)
    (P : ι → ι → MvPolynomial σ ℂ) (x : σ → ℂ) (M : Matrix ι ι ℂ)
    (hM : M = fun k l => MvPolynomial.eval x (P k l)) :
    A * M * B =
      fun i j => MvPolynomial.eval x (∑ k, ∑ l, MvPolynomial.C (A i k) * P k l * MvPolynomial.C (B l j)) := by
  funext i j
  simp only [Matrix.mul_apply, Finset.sum_mul]
  subst hM
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [Finset.sum_comm]

end GlobalTheory.AlgSubrep

namespace GlobalTheory.AlgSubrep

theorem isAlgWeight_subrep (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) V)
    (hρ : Formalism.AUTREP.IsAlgWeight L n ρ) (S : Subrepresentation ρ) :
    Formalism.AUTREP.IsAlgWeight L n S.toRepresentation := by
  classical
  obtain ⟨hfin, ι, _, _, b, P, hP⟩ := hρ
  haveI := hfin
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S.toSubmodule
  let π : V →ₗ[ℂ] S.toSubmodule := Submodule.linearProjOfIsCompl S.toSubmodule C hC
  let e := Module.Free.chooseBasis ℂ S.toSubmodule
  refine ⟨inferInstance, Module.Free.ChooseBasisIndex ℂ S.toSubmodule, inferInstance, inferInstance, e,
    fun i j => ∑ k, ∑ l, MvPolynomial.C (LinearMap.toMatrix b e π i k) * P k l *
      MvPolynomial.C (LinearMap.toMatrix e b S.toSubmodule.subtype l j), ?_⟩
  intro γ γ₀ hγ
  have hres : S.toRepresentation γ = π ∘ₗ ρ γ ∘ₗ S.toSubmodule.subtype := by
    ext x : 1
    have hm : ρ γ x ∈ S.toSubmodule := S.apply_mem_toSubmodule γ x.2
    have h1 := Submodule.linearProjOfIsCompl_apply_left hC ⟨ρ γ x, hm⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [show π (ρ γ ↑x) = _ from h1]
    apply Subtype.ext
    rfl
  have h4 := hP γ γ₀ hγ
  have h5 := toMatrix_sandwich b e π S.toSubmodule.subtype (ρ γ)
  exact (congrArg (LinearMap.toMatrix e e) hres).trans
    (h5.trans (eval_sandwich (LinearMap.toMatrix b e π) (LinearMap.toMatrix e b S.toSubmodule.subtype) P _ _ h4))
end GlobalTheory.AlgSubrep

namespace GlobalTheory.AlgSubrep

theorem exists_irreducible_algWt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) V), Formalism.AUTREP.IsAlgWeight L n ρ → ∃ (a : NG.AlgWt L n) (j : a.W →ₗ[ℂ] V), Function.Injective j ∧ ∀ γ x, j (a.ρ γ x) = ρ γ (j x) := by
  intro L _ _ _ n V _ _ _ ρ hρ
  haveI := hρ.1
  obtain ⟨S, hS⟩ := GlobalTheory.PiIsotypic.exists_irreducible_subrep ρ
  exact ⟨⟨S.toSubmodule, S.toRepresentation, isAlgWeight_subrep L n ρ hρ S, hS⟩,
    S.toSubmodule.subtype, S.toSubmodule.injective_subtype, fun γ x => rfl⟩

end GlobalTheory.AlgSubrep
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_algebraicWeight_subrep : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) V), Formalism.AUTREP.IsAlgWeight L n ρ → ∃ (a : NG.AlgWt L n) (j : a.W →ₗ[ℂ] V), Function.Injective j ∧ ∀ γ x, j (a.ρ γ x) = ρ γ (j x) := by
  atlas_forward_decl GlobalTheory.AlgSubrep.exists_irreducible_algWt
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel Formalism.L2.Col

section Irr

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]

theorem pair_inv (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (γ : ReciprocityTheory.Aut.GQ L n) (x y : VV ℂ lam) :
    pairBK lam (mtRep emb lam γ x) (tenRep emb lam γ y) = pairBK lam x y :=
  (pairBK_apply lam _ _).trans ((pairingBInvariantK_holds ℂ ι n lam (mtwEmb emb (mtwRat γ)) (x : VV ℂ lam).1
    (y : VV ℂ lam).1).trans (pairBK_apply lam x y).symm)

theorem tenIrr_conj (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (h : TenIrr emb lam) :
    TenIrr (mtwConj emb) lam := by
  unfold TenIrr
  rw [mtRep_eq_tenRep, mtwConj_conj]
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  have hd := GlobalTheory.WtDual.dual_isIrreducible (mtRep emb lam) h
  let Φ : VV ℂ lam →ₗ[ℂ] Module.Dual ℂ (VV ℂ lam) := (pairBK lam).flip
  have hΦ : ∀ x y, Φ y x = pairBK lam x y := fun x y => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact (pairingBNondegenerate_holds ℂ ι n lam).2 y fun x => by
      rw [← hΦ, hy]
      rfl
  have hdim : Module.finrank ℂ (VV ℂ lam) = Module.finrank ℂ (Module.Dual ℂ (VV ℂ lam)) :=
    (Subspace.dual_finrank_eq).symm
  let E := LinearMap.linearEquivOfInjective Φ hinj hdim
  have hE : ∀ y, E y = Φ y := fun y => rfl
  refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv (mtRep emb lam).dual (tenRep emb lam) E.symm
    (fun g f => ?_) hd
  apply E.injective
  rw [LinearEquiv.apply_symm_apply, hE]
  obtain ⟨y, rfl⟩ := E.surjective f
  rw [LinearEquiv.symm_apply_apply, hE]
  ext x
  rw [hΦ, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hΦ]
  have := pair_inv emb lam g ((mtRep emb lam g⁻¹) x) y
  rw [Representation.self_inv_apply] at this
  exact this

end Irr
end GlobalTheory.MtContraHw

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel Formalism.L2.Col

section Omega

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (e : K →+* ℂ) (lam : ι → DomWeight n)

def bC : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
  Module.Basis.mk (linearIndependent_mapVV e lam) (span_mapVV e lam).ge

theorem bC_apply (i : VVIdx lam) : bC e lam i = mapVV e lam (bVV K lam i) := by
  simp [bC]

variable {W : Type} [AddCommGroup W] [Module K W] (T : W ≃ₗ[K] VV K lam)

def omegaV : Module.Dual K W →ₛₗ[e] Module.Dual ℂ (VV ℂ lam) where
  toFun f := (bC e lam).constr ℂ fun i => e (f (T.symm (bVV K lam i)))
  map_add' f g := by
    rw [← map_add]
    congr 1
    funext i
    simp
  map_smul' c f := by
    rw [← map_smul]
    congr 1
    funext i
    simp

theorem omegaV_bC (f : Module.Dual K W) (i : VVIdx lam) :
    omegaV e lam T f (bC e lam i) = e (f (T.symm (bVV K lam i))) := by
  simp [omegaV, Module.Basis.constr_basis]

theorem omegaV_mapVV (f : Module.Dual K W) (x : VV K lam) :
    omegaV e lam T f (mapVV e lam x) = e (f (T.symm x)) := by
  conv_lhs => rw [← (bVV K lam).sum_repr x]
  conv_rhs => rw [← (bVV K lam).sum_repr x]
  simp only [map_sum, LinearMap.map_smulₛₗ, ← bC_apply, LinearMap.map_smul, omegaV_bC, smul_eq_mul, map_mul, RingHom.id_apply, LinearEquiv.map_smul, LinearMap.map_smul]

end Omega
end GlobalTheory.MtContraHw

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel Formalism.L2.Col

section Props

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (e : K →+* ℂ) (lam : ι → DomWeight n)
  {W : Type} [AddCommGroup W] [Module K W] (T : W ≃ₗ[K] VV K lam)

def coordK : Module.Dual K W →ₗ[K] VV K lam :=
  (bVV K lam).equivFun.symm.toLinearMap ∘ₗ LinearMap.pi fun i => Module.Dual.eval K W (T.symm (bVV K lam i))

def coordC : Module.Dual ℂ (VV ℂ lam) →ₗ[ℂ] VV ℂ lam :=
  (bC e lam).equivFun.symm.toLinearMap ∘ₗ LinearMap.pi fun i => Module.Dual.eval ℂ (VV ℂ lam) (bC e lam i)

theorem coordK_ker : LinearMap.ker (coordK lam T) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro f hf
  have h1 : ∀ i, f (T.symm (bVV K lam i)) = 0 := by
    intro i
    have h0 := congrArg (bVV K lam).equivFun hf
    simp only [coordK, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_zero] at h0
    simpa using congrFun h0 i
  have h2 : f ∘ₗ T.symm.toLinearMap = 0 := (bVV K lam).ext fun i => by simpa using h1 i
  ext w
  have := LinearMap.congr_fun h2 (T w)
  simpa using this

theorem coordC_omegaV (f : Module.Dual K W) : coordC e lam (omegaV e lam T f) = mapVV e lam (coordK lam T f) := by
  simp only [coordC, coordK, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
    LinearMap.pi_apply, Module.Dual.eval_apply, map_sum, LinearMap.map_smulₛₗ, omegaV_bC, bC_apply, omegaV_mapVV]

theorem omegaV_li (κ : Type) (v : κ → Module.Dual K W) (hv : LinearIndependent K v) :
    LinearIndependent ℂ fun x => omegaV e lam T (v x) := by
  refine LinearIndependent.of_comp (coordC e lam) ?_
  refine LinearIndependent.of_comp (VV ℂ lam).subtype ?_
  have h1 : LinearIndependent K fun x => ((coordK lam T (v x) : VV K lam) : Pol K ι n) :=
    (hv.map' (coordK lam T) (coordK_ker lam T)).map' (VV K lam).subtype (Submodule.ker_subtype _)
  convert Formalism.L2.Col.linearIndependent_map e _ h1 using 1
  funext x
  simp [coordC_omegaV, mapVV_coe]

theorem omegaV_coord (i : VVIdx lam) :
    omegaV e lam T ((bVV K lam).coord i ∘ₗ T.toLinearMap) = (bC e lam).coord i := by
  refine (bC e lam).ext fun j => ?_
  rw [omegaV_bC]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]

theorem omegaV_span : Submodule.span ℂ (Set.range (omegaV e lam T)) = ⊤ := by
  classical
  rw [eq_top_iff, ← (bC e lam).dualBasis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨_, by rw [omegaV_coord, Module.Basis.coe_dualBasis]⟩

end Props
end GlobalTheory.MtContraHw

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel Formalism.L2.Col

theorem omegaV_comm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type}
    [Field K] (e : K →+* ℂ) (emb : ι → L →+* K) (lam : ι → DomWeight n) {W : Type} [AddCommGroup W] [Module K W]
    (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam)
    (hT : ∀ γ x, T (ρ γ x) = rhoVr emb lam (mtwRat γ) (T x)) (γ : ReciprocityTheory.Aut.GQ L n) (f : Module.Dual K W) :
    omegaV e lam T (ρ.dual γ f) = (mtRep (fun t => e.comp (emb t)) lam).dual γ (omegaV e lam T f) := by
  refine (bC e lam).ext fun j => ?_
  have h1 : (mtRep (fun t => e.comp (emb t)) lam).dual γ (omegaV e lam T f) (bC e lam j) =
      omegaV e lam T f (mapVV e lam (rhoVr emb lam (mtwRat γ⁻¹) (bVV K lam j))) := by
    rw [GlobalTheory.ConjTwist.mapVV_rhoVr, bC_apply]
    rfl
  rw [h1, bC_apply, omegaV_mapVV, omegaV_mapVV]
  show e (f (ρ γ⁻¹ (T.symm (bVV K lam j)))) = _
  congr 2
  apply T.injective
  rw [hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.MtContraHw

open GlobalTheory.CoefModel Formalism.L2.Col in

theorem GlobalTheory.mtRatDual_hw : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', e.comp (emb t) ≠ ComplexEmbedding.conjugate (e.comp (emb t'))) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (lam : ι → DomWeight n), Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam), (∀ γ x, T (ρ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat γ) (T x)) → ∀ (t : ι) (lam0 : Fin n → ℤ), NX.HWAtF c ρ.dual (emb t) lam0 → lam0 = (lam t).w := by
  intro L _ _ _ n ι _ K _ e emb hinj hcm c hc lam hten W _ _ _ ρ T hT t lam0 hw
  have h' := GlobalTheory.MtContraHw.tenIrr_conj (fun t => e.comp (emb t)) lam hten
  have hwa := GlobalTheory.hwAt_of_hwAtF L n K e c hc (Module.Dual K W) ρ.dual
    (GlobalTheory.WtDual.dualWt (mtWt (fun t => e.comp (emb t)) lam hten)) (GlobalTheory.MtContraHw.omegaV e lam T)
    (GlobalTheory.MtContraHw.omegaV_li e lam T) (GlobalTheory.MtContraHw.omegaV_span e lam T)
    (GlobalTheory.MtContraHw.omegaV_comm e emb lam ρ T hT) (emb t) lam0 hw
  exact mtWt_hw_dual (fun t => e.comp (emb t)) hinj hcm lam hten h' t _ lam0 (GlobalTheory.WtDual.isDual_dualWt _) hwa
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredient_polynomialWeight_unique_highestWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', e.comp (emb t) ≠ ComplexEmbedding.conjugate (e.comp (emb t'))) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (lam : ι → DomWeight n), Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam), (∀ γ x, T (ρ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat γ) (T x)) → ∀ (t : ι) (lam0 : Fin n → ℤ), NX.HWAtF c ρ.dual (emb t) lam0 → lam0 = (lam t).w := by
  atlas_forward_decl GlobalTheory.mtRatDual_hw
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.WtDescent

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.CoefModel

theorem weight_descends : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', (fun t => e.comp (emb t)) t ≠ ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (fun t => e.comp (emb t)) t ∨ σ = ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t)) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W), ρ.IsIrreducible → ∀ lam0 : ι → Fin n → ℤ, (∀ t, NX.HWAtF c ρ.dual (emb t) (lam0 t)) → ∃ lam : ι → DomWeight n, (∀ t, (lam t).w = lam0 t) ∧ ∃ T : W ≃ₗ[K] VV K lam, ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  intro L _ _ _ n ι _ K _ e emb hinj hcm hcov c hc W _ _ _ ρ hρ lam0 hw
  classical
  obtain ⟨σ⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (S := L) (M := ℂ)).toRingHom⟩
  obtain ⟨t₀, -⟩ := hcov σ
  let N := Module.finrank K W
  let b : Module.Basis (Fin N) K W := Module.finBasis K W
  let A : ReciprocityTheory.Aut.GQ L n → Matrix (Fin N) (Fin N) K := fun γ => LinearMap.toMatrix b b (ρ γ)
  let ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (Fin N → ℂ) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin N) (Fin N) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin N → ℂ)) :
        Matrix (Fin N) (Fin N) ℂ →* Module.End ℂ (Fin N → ℂ)).comp
      (((e.mapMatrix : Matrix (Fin N) (Fin N) K →+* Matrix (Fin N) (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) K →* Matrix (Fin N) (Fin N) ℂ).comp
        (((LinearMap.toMatrixAlgEquiv b : Module.End K W ≃ₐ[K] Matrix (Fin N) (Fin N) K) :
          Module.End K W →* Matrix (Fin N) (Fin N) K).comp ρ))
  have hρC : ∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e := by
    intro γ
    show LinearMap.toMatrix' (Matrix.toLin' ((LinearMap.toMatrix b b (ρ γ)).map e)) = _
    rw [LinearMap.toMatrix'_toLin']
  have halg : Formalism.AUTREP.IsAlgWeight L n ρC :=
    GlobalTheory.T.isAlgWeight_of_contragredient_highestWeight L n K e c hc W ρ (Fin N) b ρC hρC (emb t₀) (lam0 t₀) (hw t₀)
  haveI : Nontrivial W := GlobalTheory.PiIsotypic.nontrivial_of_isIrreducible ρ hρ
  have hN : 0 < N := Module.finrank_pos
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨a, j, hj, hjρ⟩ := GlobalTheory.T.exists_irreducible_algebraicWeight_subrep L n (Fin N → ℂ) ρC halg
  obtain ⟨lam, Tc, hTc⟩ := GlobalTheory.T.algebraic_weight_dominant_iso_exists L n ι (fun t => e.comp (emb t)) hinj hcm hcov a
  have hmatch : ∀ γ : ReciprocityTheory.Aut.GQ L n, (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) :
      Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
      ((mtwRat γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
    intro γ
    exact (congrArg (fun g : GL (Fin n) (ReciprocityTheory.Aut.AL L) => (g : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)))
      (mtwInc_mtwRatFun γ)).symm
  let bK := bVV K lam
  let bC : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
    Module.Basis.mk (linearIndependent_mapVV e lam) (span_mapVV e lam).ge
  have hbC : ∀ i, bC i = mapVV e lam (bK i) := fun i => Module.Basis.mk_apply _ _ _
  have hrepr : ∀ x i, bC.repr (mapVV e lam x) i = e (bK.repr x i) := by
    intro x i
    have hx : mapVV e lam x = bC.equivFun.symm (fun i => e (bK.repr x i)) := by
      rw [Module.Basis.equivFun_symm_apply]
      conv_lhs => rw [← bK.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.map_smulₛₗ, hbC]
    rw [hx, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let B : ReciprocityTheory.Aut.GQ L n → Matrix (VVIdx lam) (VVIdx lam) K :=
    fun γ => LinearMap.toMatrix bK bK (rhoVr emb lam (mtwRat γ))
  have hB : ∀ γ, LinearMap.toMatrix bC bC (rhoVr (fun t => e.comp (emb t)) lam (mtwRat γ)) = (B γ).map e := by
    intro γ
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.map_apply]
    show _ = e (LinearMap.toMatrix bK bK (rhoVr emb lam (mtwRat γ)) i k)
    rw [LinearMap.toMatrix_apply, hbC, ← GlobalTheory.ConjTwist.mapVV_rhoVr, hrepr]
  let M : VV ℂ lam →ₗ[ℂ] (Fin N → ℂ) := j ∘ₗ Tc.symm.toLinearMap
  have hM : ∀ γ y, M (rhoVr (fun t => e.comp (emb t)) lam (mtwRat γ) y) = ρC γ (M y) := by
    intro γ y
    have h1 : Tc.symm (rhoVr (fun t => e.comp (emb t)) lam (mtwRat γ) y) = a.ρ γ (Tc.symm y) := by
      apply Tc.injective
      rw [hTc γ (mtwRat γ) (hmatch γ), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [M, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, hjρ]
  let X : Matrix (Fin N) (VVIdx lam) ℂ := LinearMap.toMatrix bC (Pi.basisFun ℂ (Fin N)) M
  have hX0 : X ≠ 0 := by
    intro h
    have hM0 : M = 0 := by
      have := congrArg (Matrix.toLin bC (Pi.basisFun ℂ (Fin N))) h
      simpa [X] using this
    haveI := GlobalTheory.PiIsotypic.nontrivial_of_isIrreducible a.ρ a.irr
    obtain ⟨x, hx⟩ := exists_ne (0 : a.W)
    apply hx
    apply hj
    have : M (Tc x) = j x := by simp [M]
    rw [← this, hM0, LinearMap.zero_apply, map_zero]
  have hXrel : ∀ γ, X * (B γ).map e = (A γ).map e * X := by
    intro γ
    rw [← hB, show (A γ).map e = LinearMap.toMatrix' (ρC γ) from (hρC γ).symm,
      ← LinearMap.toMatrix_eq_toMatrix', ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    congr 1
    exact LinearMap.ext fun y => hM γ y
  obtain ⟨XK, hXK0, hXK⟩ := GlobalTheory.T.nonzero_matrix_intertwiner_descends_to_subfield K e (ReciprocityTheory.Aut.GQ L n) (VVIdx lam) (Fin N) B A ⟨X, hX0, hXrel⟩
  let Φ : VV K lam →ₗ[K] W := Matrix.toLin bK b XK
  have hΦ : ∀ γ x, Φ (rhoVr emb lam (mtwRat γ) x) = ρ γ (Φ x) := by
    intro γ x
    have h : Φ ∘ₗ rhoVr emb lam (mtwRat γ) = ρ γ ∘ₗ Φ := by
      apply (LinearMap.toMatrix bK b).injective
      rw [LinearMap.toMatrix_comp bK bK b, LinearMap.toMatrix_comp bK b b, LinearMap.toMatrix_toLin]
      exact hXK γ
    exact LinearMap.congr_fun h x
  have hsurj : Function.Surjective Φ := by
    let S : Subrepresentation ρ := ⟨LinearMap.range Φ, by
      rintro γ _ ⟨x, rfl⟩
      exact ⟨_, hΦ γ x⟩⟩
    rcases hρ.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hXK0
      have hr : LinearMap.range Φ = ⊥ := congrArg Subrepresentation.toSubmodule h
      have hΦ0 : Φ = 0 := LinearMap.range_eq_bot.1 hr
      have := congrArg (LinearMap.toMatrix bK b) hΦ0
      simpa [Φ] using this
    · have hr : LinearMap.range Φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.range_eq_top.1 hr
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  haveI : FiniteDimensional K (VV K lam) := Module.Finite.of_basis bK
  have hdimC : Module.finrank ℂ a.W ≤ N := by
    have := LinearMap.finrank_le_finrank_of_injective hj
    simpa using this
  have hdimA : Module.finrank ℂ a.W = Fintype.card (VVIdx lam) := by
    rw [Tc.finrank_eq, Module.finrank_eq_card_basis bC]
  have hdimK : Module.finrank K (VV K lam) = Fintype.card (VVIdx lam) := Module.finrank_eq_card_basis bK
  have hle : N ≤ Module.finrank K (VV K lam) := by
    have := LinearMap.finrank_range_le Φ
    rwa [LinearMap.range_eq_top.2 hsurj, finrank_top] at this
  have heq : Module.finrank K (VV K lam) = Module.finrank K W := by
    show Module.finrank K (VV K lam) = N
    omega
  have hinjΦ : Function.Injective Φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).2 hsurj
  let Φb : VV K lam ≃ₗ[K] W := LinearEquiv.ofBijective Φ ⟨hinjΦ, hsurj⟩
  have h1 : ∀ y, Φb y = Φ y := fun y => rfl
  have hT : ∀ γ x, Φb.symm (ρ γ x) = rhoVr emb lam (mtwRat γ) (Φb.symm x) := by
    intro γ x
    apply Φb.injective
    rw [Φb.apply_symm_apply, h1, hΦ, ← h1, Φb.apply_symm_apply]
  have hten : Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam := by
    refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv a.ρ _ Tc (fun γ v => ?_) a.irr
    rw [hTc γ (mtwRat γ) (hmatch γ)]
    rfl
  refine ⟨lam, fun t => (GlobalTheory.T.contragredient_polynomialWeight_unique_highestWeight L n ι K e emb hinj hcm c hc lam hten W ρ Φb.symm hT t (lam0 t) (hw t)).symm,
    Φb.symm, fun γ γ₀ hm x => ?_⟩
  obtain rfl := mtwRat_eq_of_match γ γ₀ hm
  exact hT γ x

end GlobalTheory.WtDescent
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_weight_descends_to_polynomial_module : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', (fun t => e.comp (emb t)) t ≠ ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (fun t => e.comp (emb t)) t ∨ σ = ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t)) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W), ρ.IsIrreducible → ∀ lam0 : ι → Fin n → ℤ, (∀ t, NX.HWAtF c ρ.dual (emb t) (lam0 t)) → ∃ lam : ι → DomWeight n, (∀ t, (lam t).w = lam0 t) ∧ ∃ T : W ≃ₗ[K] VV K lam, ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  atlas_forward_decl GlobalTheory.WtDescent.weight_descends
end
