import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions

section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.DualJump

open GlobalTheory.DRFil GlobalTheory.DRDual

theorem multV_twisted_dual {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
    [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V')
    (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1) (j : ℤ) (hm : Function.Bijective m)
    (hg : ∀ g x y, m (ρ g x) (ρ' g y) = ((cycLL (P.PD K) ↥LL.1 g ^ j : (↥LL.1)ˣ) : ↥LL.1) * m x y)
    (h : IsDR (P.PD K) ρ) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) :
    multV (P.PD K) ρ' τ (-a - j) = multV (P.PD K) ρ τ a := by
  have := K.2
  have := LL.2
  have := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  have hs := filSpans T K LL ρ h
  let ρ₀ : Representation ↥LL.1 ↥(GK K) V' := twistRep (cycLL (P.PD K) ↥LL.1 ^ (-j)) ρ'
  have hρ₀ : ∀ g y, ρ₀ g y = ((cycLL (P.PD K) ↥LL.1 g ^ (-j) : (↥LL.1)ˣ) : ↥LL.1) • ρ' g y :=
    fun g y => rfl
  have hβ : ∀ g x y, m (ρ g x) (ρ₀ g y) = m x y := fun g x y => by
    rw [hρ₀, map_smul, hg, smul_eq_mul, zpow_neg, Units.inv_mul_cancel_left]
  have hβ' : Function.Bijective m.flip := (LinearEquiv.ofBijective m hm).flip.bijective
  have ht : (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K : P.R.BdR) = (P.PD K).ι (P.PD K).t := rfl
  obtain ⟨-, h2⟩ := twist_unit (P.PD K) ρ₀ ρ' (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K ^ (-j)) (-j)
    (fun g => (P.PD K).χ g ^ (-j)) (tdR_zpow_mem T K _)
    (by rw [← zpow_neg]; exact tdR_zpow_mem T K _) (act_zpow _ _ ht _)
    (fun g => by rw [← zpow_neg, ← zpow_neg]; exact act_zpow _ _ ht _ g)
    (fun g x => by
      rw [hρ₀, ← algebraMap_smul ↥LL.1]
      congr 1
      exact congrArg Units.val
        (map_zpow (Units.map (algebraMap ℚ_[l] ↥LL.1 : ℚ_[l] →* ↥LL.1)) ((P.PD K).χ g) (-j)))
  obtain ⟨n, d, k, had⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (isField_dR T) ρ hs τ
  obtain ⟨d', had'⟩ := had.dual ρ₀ m hβ hβ'
  rw [show -a - j = -j + -a by ring, h2, had.multV_eq, had'.multV_eq]
  simp only [neg_inj]

theorem dualJumpL : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], Nonempty (LocTied l (L l) (A l))) → DualJumpL L := by
  intro L AI hT l _ K LL A A' m hm h τ a
  obtain ⟨T⟩ := hT l
  obtain ⟨hg, h1, -, hd⟩ := hm
  have hi : Function.Injective m :=
    (injective_iff_map_eq_zero m).2 fun x hx => h1 x fun y => by rw [hx, LinearMap.zero_apply]
  have hb : Function.Bijective m :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hd.trans (Subspace.dual_finrank_eq (K := ↥LL.1) (V := A'.V)).symm)).1 hi⟩
  have key := multV_twisted_dual T K LL A.ρ A'.ρ m 1 hb (fun g x y => by rw [zpow_one]; exact hg g x y) h τ (-a - 1)
  rw [show -(-a - 1) - 1 = a by ring] at key
  rw [(GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (L l) (AI l) T K LL A'.V A'.ρ τ a).2.2,
    (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (L l) (AI l) T K LL A.V A.ρ τ (-a - 1)).2.2, key]

end GlobalTheory.DualJump
end
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem potDRL_of_tied : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], Nonempty (LocTied l (L l) (A l))) → PotDRL L := by
  intro L A hT l _ K K' LL h R hc
  obtain ⟨T⟩ := hT l
  exact (GlobalTheory.T.restrict_crystalline_deRham_finiteExt l (L l) (A l) T K K' LL h R.V R.ρ).2.2
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (L l) (A l) T K' LL R.V _ hc).1

end GlobalTheory.Pass
end

section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct GlobalTheory.Pass GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.FontCmp
open GlobalTheory.RegularRing

namespace GlobalTheory.PcrisTwist

section Eigen

variable {I LL : Type} [Group I] [Field LL]

open Classical in

theorem exists_separating (S : Finset (I →* LLˣ)) (a : I →* LLˣ) :
    ∃ e : I →₀ LL, ∀ b ∈ S, (e.sum fun g c => c * (b g : LL)) = if b = a then 1 else 0 := by
  have h1 : LinearIndependent LL (fun b : S => fun g : I => ((b.1 g : LLˣ) : LL)) := by
    refine (linearIndependent_monoidHom I LL).comp (fun b : S => (Units.coeHom LL).comp b.1) ?_
    intro b b' h
    exact Subtype.ext (MonoidHom.ext fun g => Units.ext (DFunLike.congr_fun h g))
  have h2 := span_flip_eq_top_iff_linearIndependent.2 h1
  obtain ⟨e, he⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
    (h2 ▸ Submodule.mem_top : (fun b : S => if b.1 = a then (1 : LL) else 0) ∈ _)
  refine ⟨e, fun b hb => ?_⟩
  have := congrFun he ⟨b, hb⟩
  simpa [Finsupp.sum, flip] using this

def eig {M : Type} [AddCommGroup M] [Module LL M] (T : I → M →ₗ[LL] M) (b : I →* LLˣ) : Submodule LL M :=
  ⨅ g : I, LinearMap.ker (T g - ((b g : LLˣ) : LL) • LinearMap.id)

theorem mem_eig {M : Type} [AddCommGroup M] [Module LL M] (T : I → M →ₗ[LL] M) (b : I →* LLˣ) (x : M) :
    x ∈ eig T b ↔ ∀ g, T g x = ((b g : LLˣ) : LL) • x := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem le_iSup_eig {M N J : Type} [AddCommGroup M] [Module LL M] [AddCommGroup N] [Module LL N]
    (S : Finset (I →* LLˣ)) (T : I → M →ₗ[LL] M) (D : Submodule LL M) (hD : ∀ g, ∀ x ∈ D, T g x ∈ D)
    (f : J → M →ₗ[LL] N) (T' : J → I → N →ₗ[LL] N) (hf : ∀ j g x, f j (T g x) = T' j g (f j x))
    (hS : ∀ j, ∀ x ∈ D, f j x ∈ ⨆ b ∈ S, eig (T' j) b) (hsep : ∀ x, (∀ j, f j x = 0) → x = 0) :
    D ≤ ⨆ b ∈ S, D ⊓ eig T b := by
  classical
  choose e he using exists_separating S
  let E : (I →* LLˣ) → M →ₗ[LL] M := fun a => (e a).sum fun g c => c • T g
  let E' : J → (I →* LLˣ) → N →ₗ[LL] N := fun j a => (e a).sum fun g c => c • T' j g
  have h1 : ∀ j a x, f j (E a x) = E' j a (f j x) := fun j a x => by
    simp [E, E', Finsupp.sum, hf]
  have h2 : ∀ j a, ∀ b ∈ S, ∀ y ∈ eig (T' j) b, E' j a y = if b = a then y else 0 := by
    intro j a b hb y hy
    have : E' j a y = ((e a).sum fun g c => c * (b g : LL)) • y := by
      simp [E', Finsupp.sum, (mem_eig _ _ _).1 hy, Finset.sum_smul, smul_smul]
    rw [this, he a b hb]
    split_ifs <;> simp
  have h3 : ∀ j, (⨆ b ∈ S, eig (T' j) b) ≤ LinearMap.ker (∑ a ∈ S, E' j a - LinearMap.id) := fun j =>
    iSup₂_le fun b hb y hy => by
      simp [h2 j _ b hb y hy, hb]
  have h4 : ∀ j a, (⨆ b ∈ S, eig (T' j) b) ≤ (eig (T' j) a).comap (E' j a) := fun j a =>
    iSup₂_le fun b hb y hy => by
      rw [Submodule.mem_comap, h2 j _ b hb y hy]
      split_ifs with h
      · exact h ▸ hy
      · exact Submodule.zero_mem _
  intro x hx
  have h5 : x = ∑ a ∈ S, E a x := by
    symm
    rw [← sub_eq_zero]
    refine hsep _ fun j => ?_
    simpa [h1] using h3 j (hS j x hx)
  rw [h5]
  refine Submodule.sum_mem _ fun a ha => Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha ⟨?_, ?_⟩)
  · simp only [E, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
    exact D.sum_mem fun g _ => D.smul_mem _ (hD g x hx)
  · refine (mem_eig _ _ _).2 fun g => ?_
    rw [← sub_eq_zero]
    refine hsep _ fun j => ?_
    rw [map_sub, map_smul, hf, h1, (mem_eig _ _ _).1 (h4 j a (hS j x hx)), sub_self]

end Eigen

section Pair

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]

variable (Qp B) in

def pairB (m : V →ₗ[LL] U →ₗ[LL] W) : V ⊗[Qp] B →ₗ[LL] U ⊗[Qp] B →ₗ[LL] W ⊗[Qp] B :=
  (TensorProduct.mk LL _ _).compr₂ (tensorB (TensorProduct.lift m) ∘ₗ prodB)

@[simp] theorem pairB_tmul (m : V →ₗ[LL] U →ₗ[LL] W) (v : V) (u : U) (b c : B) :
    pairB Qp B m (v ⊗ₜ b) (u ⊗ₜ c) = m v u ⊗ₜ (b * c) := by
  simp [pairB, prodB_tmul, tensorB]

theorem pairB_mB (m : V →ₗ[LL] U →ₗ[LL] W) (b : B) (x : V ⊗[Qp] B) (y : U ⊗[Qp] B) :
    pairB Qp B m x (mB LL b y) = mB LL b (pairB Qp B m x y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul v' c' => simp [mul_left_comm]

theorem act_pairB {ρ : Representation LL G V} {σ : Representation LL G U} {τ : Representation LL G W}
    {m : V →ₗ[LL] U →ₗ[LL] W} (hm : ∀ g v u, m (ρ g v) (σ g u) = τ g (m v u)) (g : G)
    (x : V ⊗[Qp] B) (y : U ⊗[Qp] B) :
    pairB Qp B m (actVB PD ρ g x) (actVB PD σ g y) = actVB PD τ g (pairB Qp B m x y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul v' c' => simp [actVB, hm]

theorem pairB_sep [FiniteDimensional LL U] {m : V →ₗ[LL] U →ₗ[LL] W} (hm : Function.Injective m)
    (x : V ⊗[Qp] B) (hx : ∀ y, pairB Qp B m x y = 0) : x = 0 := by
  obtain ⟨r, hr⟩ := m.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hm)
  let u := Module.finBasis LL U
  let s : Fin (finrank LL U) → W →ₗ[LL] V := fun i => r ∘ₗ LinearMap.smulRightₗ (u.coord i)
  have hs : ∀ v, ∑ i, s i (m v (u i)) = v := by
    intro v
    have h1 : ∑ i, LinearMap.smulRightₗ (u.coord i) (m v (u i)) = m v := by
      refine u.ext fun j => ?_
      simp [Finsupp.single_apply]
    simp only [s, LinearMap.comp_apply]
    rw [← map_sum, h1]
    exact LinearMap.congr_fun hr v
  have key : ∀ x : V ⊗[Qp] B, ∑ i, tensorB (s i) (pairB Qp B m x (u i ⊗ₜ 1)) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib, ha, hc]
    | tmul v c => simp [tensorB, ← TensorProduct.sum_tmul, hs]
  rw [← key x]
  simp [hx]

theorem actVB_mul (ρ : Representation LL G V) (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, ha, hc]
  | tmul v c => simp [actVB]

theorem isCrys_of_pair [IsDomain B] [FiniteDimensional Qp LL] [FiniteDimensional LL V] [FiniteDimensional LL U]
    [FiniteDimensional LL W] (hf : FracInv PD) (hu : LineUnit PD)
    {ρ : Representation LL G V} {σ : Representation LL G U} {τ : Representation LL G W}
    {m : V →ₗ[LL] U →ₗ[LL] W} (hm : ∀ g v u, m (ρ g v) (σ g u) = τ g (m v u)) (hi : Function.Injective m)
    (hσ : IsCrys PD σ) (hτ : IsCrys PD τ) : IsCrys PD ρ := by
  refine subCrys PD LL hf _ (σ.dual.tprod τ) V ρ ((dualTensorHomEquiv LL U W).symm.toLinearMap ∘ₗ m) ?_
    ((dualTensorHomEquiv LL U W).symm.injective.comp hi)
    (tensorCrys PD LL hf hu _ _ _ _ (dualCrys PD LL hf hu _ _ hσ) hτ)
  intro g v
  apply (dualTensorHomEquiv LL U W).injective
  have h1 := LinearMap.congr_fun (Representation.dualTensorHom_comm σ τ g)
    ((dualTensorHomEquiv LL U W).symm (m v))
  have h2 : ∀ z, dualTensorHom LL U W z = dualTensorHomEquiv LL U W z := fun z => by
    simp [dualTensorHomEquiv]
  simp only [LinearMap.comp_apply, h2, LinearEquiv.apply_symm_apply] at h1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Representation.tprod_apply, h1]
  ext u
  simp [Representation.linHom_apply, ← hm]

theorem tate_twist_multiplication_intertwines (g : G) (x : LL ⊗[Qp] B) :
    actVB PD (Representation.trivial LL G LL) g (mB LL PD.t x) =
      mB LL PD.t (actVB PD (WeaklyAdmissibleFiltrations.charRep (cycLL PD LL)) g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, ha, hc]
  | tmul v c =>
    simp [actVB, PD.t_act, WeaklyAdmissibleFiltrations.charRep, cycLL, ← Algebra.smul_def, smul_tmul]

include PD in
theorem mB_t_injective : Function.Injective (mB LL PD.t : V ⊗[Qp] B → V ⊗[Qp] B) := by
  obtain ⟨s, hs⟩ := PD.t_unit.exists_left_inv
  intro x y h
  rw [← mB_one (LL := LL) x, ← mB_one (LL := LL) y, ← hs, mB_mul, mB_mul, h]

theorem isCrys_cyc [IsDomain B] [FiniteDimensional Qp LL] (hf : FracInv PD) (hu : LineUnit PD) :
    IsCrys PD (WeaklyAdmissibleFiltrations.charRep (cycLL PD LL)) := by
  obtain ⟨s, hs⟩ := PD.t_unit.exists_right_inv
  rw [isCrys_iff_span PD hf hu]
  refine eq_top_of_tmul _ fun b v => ?_
  have h1 : b ⊗ₜ[Qp] v = (b * PD.t) • (s ⊗ₜ[Qp] v) := by
    rw [smul_tmul', smul_eq_mul, mul_assoc, hs, mul_one]
  rw [h1]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  change v ⊗ₜ[Qp] s ∈ Dcris PD _
  rw [mem_Dcris]
  intro g
  apply mB_t_injective PD (LL := LL)
  rw [← tate_twist_multiplication_intertwines, mB_tmul, hs]
  simp [actVB]

end Pair

section Pot

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]

theorem actVB_resH (ρ : Representation LL G V) (h : PC.H) (x : V ⊗[Qp] B) :
    actVB PC.PD' (PC.resH ρ) h x = actVB PC.PD ρ h x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, ha, hc]
  | tmul v c => simp [actVB, PC.actB_eq, PotCrysData.resH]

theorem mem_Dpcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ PC.Dpcris ρ ↔ ∀ h : PC.H, actVB PC.PD ρ h x = x := by
  simp only [PotCrysData.Dpcris, mem_Dcris, actVB_resH]

theorem act_mem_Dpcris (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B) (hx : x ∈ PC.Dpcris ρ) :
    actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  rw [mem_Dpcris] at hx ⊢
  intro h
  have h1 := hx ⟨g⁻¹ * h * g, PC.normal.conj_mem' _ h.2 g⟩
  conv_rhs => rw [← h1]
  rw [← actVB_mul, ← actVB_mul]
  congr 2
  group


variable [IsDomain B] [FiniteDimensional Qp LL]

theorem inertia_of_pair [FiniteDimensional LL V] [FiniteDimensional LL U] [FiniteDimensional LL W]
    (hf : FracInv PC.PD') (hu : LineUnit PC.PD')
    {ρ : Representation LL G V} {σ : Representation LL G U} {τ : Representation LL G W}
    {m : V →ₗ[LL] U →ₗ[LL] W} (hm : ∀ g v u, m (ρ g v) (σ g u) = τ g (m v u)) (hi : Function.Injective m)
    (hσ : PC.IsPotCrys σ) (hτ : PC.IsPotCrys τ) {S SU SW : Finset (PC.Iner →* LLˣ)}
    (hU : PC.InertiaThrough σ SU) (hW : PC.InertiaThrough τ SW)
    (hS : ∀ b, b ∈ S ↔ ∃ w ∈ SW, ∃ u ∈ SU, b = w * u⁻¹) :
    PC.IsPotCrys ρ ∧ PC.InertiaThrough ρ S := by
  refine ⟨isCrys_of_pair PC.PD' hf hu (m := m) (fun g v u => hm g v u) hi hσ hτ, ?_, ?_, ?_⟩
  · intro b hb g hg
    obtain ⟨w, hw, u, hu, rfl⟩ := (hS b).1 hb
    simp [hW.1 w hw g hg, hU.1 u hu g hg]
  · intro b hb
    obtain ⟨w, hw, u, hu, rfl⟩ := (hS b).1 hb
    refine Nat.Coprime.coprime_dvd_left (Commute.all w u⁻¹).orderOf_mul_dvd_mul_orderOf ?_
    rw [orderOf_inv]
    exact Nat.Coprime.mul_left (hW.2.1 w hw) (hU.2.1 u hu)
  refine le_antisymm ?_ (iSup₂_le fun _ _ => inf_le_left)
  refine le_iSup_eig (J := {p : (PC.Iner →* LLˣ) × (U ⊗[Qp] B) // p.1 ∈ SU ∧ p.2 ∈ PC.Eig σ PC.Iner p.1})
    S (fun g : PC.Iner => actVB PC.PD ρ g) _ (fun g x hx => act_mem_Dpcris PC ρ g x hx)
    (fun j => (pairB Qp B m).flip j.1.2)
    (fun j g => (((j.1.1 g)⁻¹ : LLˣ) : LL) • actVB PC.PD τ g) ?_ ?_ ?_
  · rintro ⟨⟨a, y⟩, ha, hy⟩ g x
    have h1 := act_pairB PC.PD hm g x y
    rw [(mem_eig _ _ _).1 hy.2 g, map_smul] at h1
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, ← h1, smul_smul, Units.inv_mul, one_smul]
  · rintro ⟨⟨a, y⟩, ha, hy⟩ x hx
    have h1 : pairB Qp B m x y ∈ PC.Dpcris τ := by
      rw [mem_Dpcris]
      intro h
      rw [← act_pairB PC.PD hm, (mem_Dpcris PC _ _).1 hx, (mem_Dpcris PC _ _).1 hy.1]
    rw [hW.2.2] at h1
    refine SetLike.le_def.1 (iSup₂_le fun w hw z hz => ?_) h1
    refine Submodule.mem_iSup_of_mem (w * a⁻¹) (Submodule.mem_iSup_of_mem ((hS _).2 ⟨w, hw, a, ha, rfl⟩) ?_)
    refine (mem_eig _ _ _).2 fun g => ?_
    have h2 : actVB PC.PD τ g z = _ := (mem_eig _ _ _).1 hz.2 g
    simp [h2, smul_smul, mul_comm]
  · intro x hx
    have h1 : PC.Dpcris σ ≤ LinearMap.ker (pairB Qp B m x) := by
      rw [hU.2.2]
      exact iSup₂_le fun a ha y hy => hx ⟨(a, y), ha, hy⟩
    refine pairB_sep hi x fun y => ?_
    induction y using cmp_ind PC.PD' (comparison_bijective PC.PD' hf hu _ hσ) with
    | h0 => simp
    | hadd y y' h h' => rw [map_add, h, h', add_zero]
    | hb b d => rw [pairB_mB, h1 d.2, map_zero]

theorem inertia_cyc (hf : FracInv PC.PD') (hu : LineUnit PC.PD') :
    PC.IsPotCrys (WeaklyAdmissibleFiltrations.charRep (cycLL PC.PD LL)) ∧ PC.InertiaThrough (WeaklyAdmissibleFiltrations.charRep (cycLL PC.PD LL)) {1} := by
  have e : PC.resH (WeaklyAdmissibleFiltrations.charRep (cycLL PC.PD LL)) = WeaklyAdmissibleFiltrations.charRep (cycLL PC.PD' LL) := by
    ext h
    simp [PotCrysData.resH, WeaklyAdmissibleFiltrations.charRep, cycLL, PC.χ_eq]
  refine ⟨?_, by simp, by simp, le_antisymm (fun x hx => ?_) (iSup₂_le fun _ _ => inf_le_left)⟩
  · unfold PotCrysData.IsPotCrys
    rw [e]
    exact isCrys_cyc PC.PD' hf hu
  refine Submodule.mem_iSup_of_mem 1 (Submodule.mem_iSup_of_mem (Finset.mem_singleton_self _) ⟨hx, ?_⟩)
  refine (mem_eig (fun g : PC.Iner => actVB PC.PD (WeaklyAdmissibleFiltrations.charRep (cycLL PC.PD LL)) g) 1 x).2 fun g => ?_
  have h1 : mB LL PC.PD.t x ∈ Dcris PC.PD' (Representation.trivial LL PC.H LL) := by
    rw [mem_Dcris]
    intro h
    rw [← PC.t_eq, tate_twist_multiplication_intertwines, ← e, (mem_Dcris _ _ _).1 hx]
  rw [unit_eq] at h1
  obtain ⟨y, hy⟩ := h1
  apply mB_t_injective PC.PD (LL := LL)
  rw [← tate_twist_multiplication_intertwines, MonoidHom.one_apply, Units.val_one, one_smul, ← hy]
  clear hy
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, ha, hc]
  | tmul v c => simp [actVB, g.2 c]

theorem inertia_twist [FiniteDimensional LL V] [FiniteDimensional LL W]
    (hf : FracInv PC.PD') (hu : LineUnit PC.PD') {ρ : Representation LL G V} {ρ' : Representation LL G W}
    {S S' : Finset (PC.Iner →* LLˣ)} (hA : PC.IsPotCrys ρ) (hI : PC.InertiaThrough ρ S)
    (χ : G →* LLˣ) (c : PC.Iner →* LLˣ) (ht : IsTwistRep χ⁻¹ ρ ρ') (hχ : PC.IsPotCrys (WeaklyAdmissibleFiltrations.charRep χ))
    (hc : PC.InertiaThrough (WeaklyAdmissibleFiltrations.charRep χ) {c}) (hs : ∀ b, b ∈ S' ↔ ∃ a ∈ S, b = a * c⁻¹) :
    PC.IsPotCrys ρ' ∧ PC.InertiaThrough ρ' S' := by
  obtain ⟨e, he⟩ := ht
  refine inertia_of_pair _ hf hu (m := (LinearMap.lsmul LL V).flip ∘ₗ e.symm.toLinearMap) ?_ ?_
    hχ hA hc hI fun b => by simpa using hs b
  · intro g v u
    obtain ⟨v, rfl⟩ := e.surjective v
    simp [he, WeaklyAdmissibleFiltrations.charRep, smul_smul, mul_comm, mul_left_comm]
  · intro v v' hv
    simpa using LinearMap.congr_fun hv 1

theorem inertia_dual [FiniteDimensional LL V] [FiniteDimensional LL W]
    (hf : FracInv PC.PD') (hu : LineUnit PC.PD') {ρ : Representation LL G V} {ρ' : Representation LL G W}
    {S S' : Finset (PC.Iner →* LLˣ)} (hA : PC.IsPotCrys ρ) (hI : PC.InertiaThrough ρ S)
    (P : V →ₗ[LL] W →ₗ[LL] LL) (hP : IsDual1 PC.PD ρ ρ' P) (hs : ∀ b, b ∈ S' ↔ ∃ a ∈ S, b = a⁻¹) :
    PC.IsPotCrys ρ' ∧ PC.InertiaThrough ρ' S' := by
  obtain ⟨h1, h2⟩ := inertia_cyc (LL := LL) _ hf hu
  refine inertia_of_pair _ hf hu (m := P.flip) (fun g v u => hP.1 g u v) ?_ hA h1 hI h2
    fun b => by simpa using hs b
  rw [injective_iff_map_eq_zero]
  exact fun y hy => hP.2.2.1 y fun x => LinearMap.congr_fun hy x

end Pot

theorem pcrisTensorL_of_tied : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)),
    (∀ (l : ℕ) [Fact l.Prime], Nonempty (LocTied l (L l) (A l))) → PcrisTensorL L := by
  intro L AI hT l _ K K' LL h hN hF hS A A' Sig Sig' hA hI
  obtain ⟨T⟩ := hT l
  obtain ⟨C, hfit⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l (L l) (AI l) T
  haveI := LL.2
  haveI := isDomain_of_tied T K
  have hf : FracInv (pc (L l) h hN hF hS).PD' := fun b b' hb hg =>
    fracInv hfit (GlobalTheory.MemLoc.TensorInj.tensorInj l C) K' b b' hb fun g => by
      obtain ⟨g, rfl⟩ := (GKinEquiv h).surjective g
      exact hg g
  have hu : LineUnit (pc (L l) h hN hF hS).PD' := fun b hb hg =>
    lineUnit hfit (GlobalTheory.MemLoc.core_regular l C) K' b hb fun g => by
      obtain ⟨g, rfl⟩ := (GKinEquiv h).surjective g
      exact hg g
  exact ⟨inertia_twist _ hf hu hA hI, inertia_dual _ hf hu hA hI⟩

end GlobalTheory.PcrisTwist
end
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.Closing

theorem closing_at_record : ∀ D : D7, DualJumpL D.loc ∧ PotDRL D.loc ∧ PcrisTensorL D.loc ∧
    PairedCharacterCondition.tieBr (D := D) ∧ InertEq D := by
  intro D
  have hT : ∀ (l : ℕ) [Fact (Nat.Prime l)], Nonempty (LocTied l (D.loc l) (D.locA l)) :=
    fun l _ => ⟨D.locT l⟩
  refine ⟨GlobalTheory.DualJump.dualJumpL D.loc D.locA hT, GlobalTheory.Pass.potDRL_of_tied D.loc D.locA hT,
    GlobalTheory.PcrisTwist.pcrisTensorL_of_tied D.loc D.locA hT, ?_, GlobalTheory.BridgeInertia.inertEq D⟩
  intro i w hw
  exact GlobalTheory.bridge_degW D.nbr i w hw

end GlobalTheory.Closing
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

noncomputable section

namespace GlobalTheory.EigenProjector

theorem HG_of_mem_Zgood (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (hπ : π ∈ D.nd.Zgood i) :
    HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩

end GlobalTheory.EigenProjector
end
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

noncomputable section

namespace GlobalTheory.Pass

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem cutBound_of_steps : StepsNoCut → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CT : ℕ), SumRepresentations.adm5 D → ElementDenominator.adm12 D → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → GaloisFamilyConditions (D := D) → admG5 (D := D) → admG6 (D := D) → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → LocalGlobalCompatibilityAlt (D := D) → FontaineAtPlacesOverL (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → CongruenceAtTypePrimes (D := D) CT fun i k ρ eta => ∀ π ∈ D.nd.Zgood i, ∀ Xs : Set (D.nd.X i), π ∈ Xs → TypeLocus P i k Xs → LocalCongruenceBound CT eta i ρ π (vccCut i Xs π) := by
  rintro ⟨_hCI, _hCen, hDeg, hType, hPotD, hPotDu, hJD, hJDu, hLift, hSub, hCont, hLocD, hLocDu, hHf, hRes, hGlob⟩
  intro D P HW F CT h5 h12 hIne hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hTB hBK hBC hLGC hFont htie0 hChi
  obtain ⟨hDJ, hPDR, hPT, hBr, hIE⟩ := GlobalTheory.Closing.closing_at_record D
  intro i k k' _hkk' hlk r ρ hr hdec eta s S sg U hs _hlog hCT _hsg hHost hSQ hsFin hSha π hπ Xs hπXs hTL
  have hπZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  have hHG : HG D.nd D.naut i := GlobalTheory.EigenProjector.HG_of_mem_Zgood D i π hπ
  have hdecπ := hdec π hπZ
  have hTLGC : TypeLGC P := hType D P hDZ htie0 hBC hLGC h5
  have hPH : PairedCharacterCondition.tiePH (D := D) := D.loc_tie
  have hl2 : D.nd.l i ≠ 2 := hlk ▸ Formalism.L2.Pj.g_ne_two D k
  have hloc : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), HfChar i w hw ∧
      LocBoundP i w hw r Xs (WpO D.nd i ρ π) (2 * D.R.r * eMax D CT eta) ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, LocBoundP i w hw r Xs (chiRatO D.nd i c) (2 * 1 * eMax D CT eta) := by
    intro w hw
    have hdeg1 := (hDeg D hBr i k hlk).2 w hw
    have hPot : PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) (D.R.nV + 1) :=
      hPotD D P hTLGC hFont htie0 hBr hPH hChi hIE h12 hPT hIne i k hlk r ρ hr π hπZ hdecπ Xs hπXs hTL w hw
    have hCT' : CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.nd.l i := hlk ▸ hCT
    have hH : eta + D.R.t + 1 < s + S := by omega
    have hsub := hSub D i r ρ hr π hdecπ Xs hπXs
    have key : ∀ (kk : ℕ) (M : GE D.nd →* Matrix (Fin kk) (Fin kk) (D.nd.O i)), SubTw i r Xs M →
        LocBoundP i w hw r Xs M (2 * kk * eMax D CT eta) := by
      intro kk M hM
      cases hsw : sg w
      · have hPotDu' := hPotDu D hPT i r hr Xs w hw _ hPot
        have hJ := hJDu D hDJ hPDR i r hr eta s S sg U hs hHost Xs w hw _ hsw hPot
        have hL := hLift D CT hT hFont i w hw hdeg1 (↥Xs) (fun x => rDuO D.nd i r x)
          (fun x => (hCont D i r hr x).2) eta (s + S) hH hCT' hPotDu' hJ
        exact hLocDu D hLOC hBK hFont hPDR i r hr Xs w hw hdeg1 _ _ hPot hL kk M hM
      · have hJ := hJD D i r eta s S sg U hs hHost Xs w hw hsw
        have hL := hLift D CT hT hFont i w hw hdeg1 (↥Xs) (fun x => rTwO D.nd i r x)
          (fun x => (hCont D i r hr x).1) eta (s + S) hH hCT' hPot hJ
        exact hLocD D hLOC hBK hFont hPDR i r hr Xs w hw hdeg1 _ _ hPot hL kk M hM
    exact ⟨hHf D P HW F hTB hIE i k hlk hl2 w hw hdeg1, key _ _ hsub.1, fun c hc => key _ _ (hsub.2 c hc)⟩
  have hG1 : TruncatedSeriesCountingIdentities.admG1 (D := D) i r := by
    intro g kk
    obtain ⟨f, hf⟩ := (hG14 i r hr).1 g kk
    have e : (fun x : D.nd.X i => ((rO D.nd i r x g).charpolyRev).coeff kk) = (f : D.nd.X i → D.nd.O i) :=
      funext fun x => (hf x).symm
    rw [e]
    exact f.2
  have hG4 : TruncatedSeriesCountingIdentities.admG4 (D := D) i r := by
    intro x v hl hS hQ g hg
    exact (hG14 i r hr).2.2.2 x v hl hS hQ (D.nd.plOm.1 v) (D.nd.plOm.2 v) g hg
  obtain ⟨S0, hS0, -⟩ := ((hN5g i k hlk hHG r ρ hr).2 π hπZ hdecπ).1 hπZ
  have hG := hGlob D i r ρ π Xs (2 * D.R.r * eMax D CT eta) (2 * 1 * eMax D CT eta) hr hG1
    (hRes D hRbar hG14 i r ρ hr π hπ hdecπ) hG4 (galois_condition_five_of D i r hG5 hHG hr)
    (GlobalTheory.TameDesign.main D i).2 (galois_condition_six_of D i r hG6 hHG hr) hdecπ (coefficient_compatibility_of D i (hBr i)) hSQ
    ⟨S0, hS0⟩ hπZ hπXs hloc (hsFin π hπ) hSha
  have hcard : (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f := (hDeg D hBr i k hlk).1
  have hnat : (placesOver D.host.E (D.nd.l i)).ncard * (2 * D.R.r * eMax D CT eta + D.R.t * (2 * 1 * eMax D CT eta)) =
      D.R.f * (2 * ((2 * D.R.r + D.R.t * 2) * (CT * ((D.R.nV + 1) * ((D.R.nV + 1) ^ 2 / 4) +
        (eta + D.R.t + 1) * ((D.R.nV + 1) + (D.R.nV + 1) ^ 2 / 4))))) := by
    rw [hcard]; unfold eMax; ring
  rw [hnat] at hG
  have hrn : D.R.r ≤ D.R.nV := by unfold Ranks.nV; omega
  have hr2 : 2 ≤ D.R.r := hRbar.1
  refine ⟨D.R.nV + 1, (D.R.nV + 1) ^ 2 / 4, by omega, le_refl _, ?_, Nat.mul_div_le _ _, ?_⟩
  · have h9 : 9 ≤ (D.R.nV + 1) ^ 2 := by nlinarith
    omega
  · have hG' := (Rat.cast_le (K := ℝ)).2 hG
    push_cast at hG' ⊢
    linarith

end GlobalTheory.Pass

end
end
