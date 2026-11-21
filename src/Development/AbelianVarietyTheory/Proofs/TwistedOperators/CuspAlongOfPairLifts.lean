import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitaryS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaRuleExchangePairMembers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompatStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorFrameChangeSameCartan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNegatedSpaceDiscreteSeriesModelTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijectionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerAdjointIsRealThetaIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanishStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsAddBlockArrow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsRemoveBlockArrow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsColumnArrows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParameStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.ConjModelTr

def Tw (X : Type) : Type := X

instance (X : Type) [AddCommGroup X] : AddCommGroup (Tw X) := inferInstanceAs (AddCommGroup X)
instance (X : Type) [AddCommGroup X] [Module ℂ X] : Module ℂ (Tw X) := Module.compHom X (starRingEnd ℂ)

section Gen

variable {ι : Type} [Fintype ι] {X₁ X : ι → Type} [∀ i, AddCommGroup (X₁ i)] [∀ i, Module ℂ (X₁ i)]
  [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]

theorem comp_update [DecidableEq ι] (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) (v : ∀ i, X₁ i) (i : ι) (x : X₁ i) :
    (fun j => c j (Function.update v i x j)) = Function.update (fun j => c j (v j)) i (c i x) :=
  funext fun j => Function.apply_update (fun j => (c j : X₁ j → X j)) v i x j

def cmul (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) : MultilinearMap ℂ X₁ (Tw (⨂[ℂ] i, X i)) where
  toFun v := (PiTensorProduct.tprod ℂ (fun i => c i (v i)) : ⨂[ℂ] i, X i)
  map_update_add' v i x y := by
    classical
    show PiTensorProduct.tprod ℂ (fun j => c j (Function.update v i (x + y) j)) =
      PiTensorProduct.tprod ℂ (fun j => c j (Function.update v i x j)) +
        PiTensorProduct.tprod ℂ (fun j => c j (Function.update v i y j))
    rw [comp_update, comp_update, comp_update, map_add, MultilinearMap.map_update_add]
  map_update_smul' v i a x := by
    classical
    show PiTensorProduct.tprod ℂ (fun j => c j (Function.update v i (a • x) j)) =
      (starRingEnd ℂ a) • PiTensorProduct.tprod ℂ (fun j => c j (Function.update v i x j))
    rw [comp_update, comp_update, map_smulₛₗ, MultilinearMap.map_update_smul]

def kapF (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) : (⨂[ℂ] i, X₁ i) →+ ⨂[ℂ] i, X i where
  toFun x := (PiTensorProduct.lift (cmul c) x : Tw (⨂[ℂ] i, X i))
  map_zero' := map_zero (PiTensorProduct.lift (cmul c))
  map_add' x y := map_add (PiTensorProduct.lift (cmul c)) x y

theorem kapF_tprod (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) (v : ∀ i, X₁ i) :
    kapF c (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (fun i => c i (v i)) := by
  show (PiTensorProduct.lift (cmul c) (PiTensorProduct.tprod ℂ v) : Tw (⨂[ℂ] i, X i)) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

theorem kapF_smul (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) (r : ℂ) (x : ⨂[ℂ] i, X₁ i) :
    kapF c (r • x) = starRingEnd ℂ r • kapF c x := by
  show (PiTensorProduct.lift (cmul c) (r • x) : Tw (⨂[ℂ] i, X i)) = _
  rw [map_smul]
  rfl

theorem kapF_symm (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) (x : ⨂[ℂ] i, X₁ i) :
    kapF (fun i => (c i).symm) (kapF c x) = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => rw [kapF_smul, kapF_smul, kapF_tprod, kapF_tprod]; simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def kap (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) : (⨂[ℂ] i, X₁ i) ≃+ ⨂[ℂ] i, X i where
  toFun := kapF c
  invFun := kapF fun i => (c i).symm
  left_inv := kapF_symm c
  right_inv y := by
    have := kapF_symm (fun i => (c i).symm) y
    simpa using this
  map_add' := map_add (kapF c)

theorem kap_tprod (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) (v : ∀ i, X₁ i) :
    kap c (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (fun i => c i (v i)) := kapF_tprod c v

theorem kap_smul (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) (r : ℂ) (x : ⨂[ℂ] i, X₁ i) :
    kap c (r • x) = starRingEnd ℂ r • kap c x := kapF_smul c r x

end Gen

section Model

open GlobalTheory.ConjDS

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def cM (M : DSModel V S) (τ : D.what₂.Tau) : (conjModel M).H τ ≃ₗᵢ⋆[ℂ] M.H τ := GlobalTheory.ConjDS.cj (M.H τ)

theorem rep_conjModel (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (w : (conjModel M).H τ) : cM M τ ((conjModel M).rep τ g w) = M.rep τ g (cM M τ w) := by
  have e : rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
      ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹) = M.fr τ * g * (M.fr τ)⁻¹ := by
    rw [inv_submatrix_equiv]
    have : (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * (M.fr τ)⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
        rv (M.fr τ * g * (M.fr τ)⁻¹) := by
      ext i j
      simp [rv, Matrix.mul_apply]
    rw [this, rv_rv]
  show M.σ τ (rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
      ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹)) (cM M τ w) = M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (cM M τ w)
  rw [e]

theorem sm_iff (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau) (w : (conjModel M).H τ) :
    w ∈ (conjModel M).sm τ ↔ cM M τ w ∈ M.sm τ :=
  (GlobalTheory.ConjMult.conj_mult θ M (conjModel M) (cM M) (fun τ g _ w => rep_conjModel M τ g w)).1 τ w

def csm (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau) : (conjModel M).sm τ ≃ₗ⋆[ℂ] M.sm τ where
  toFun w := ⟨cM M τ (w : (conjModel M).H τ), (sm_iff θ M τ w).1 w.2⟩
  invFun w := ⟨(cM M τ).symm (w : M.H τ), (sm_iff θ M τ _).2 (by simpa using w.2)⟩
  map_add' x y := Subtype.ext (map_add (cM M τ) _ _)
  map_smul' a x := Subtype.ext (map_smulₛₗ (cM M τ) _ _)
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)

theorem csm_val (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau) (w : (conjModel M).sm τ) :
    ((csm θ M τ w : M.sm τ) : M.H τ) = cM M τ (w : (conjModel M).H τ) := rfl

def chs (M : DSModel V S) (τ : D.what₂.Tau) : (conjModel M).H τ ≃ₗ⋆[ℂ] M.H τ := (cM M τ).toLinearEquiv

theorem incl_kap (θ : InfFam D) (M : DSModel V S) (x : SmT (conjModel M)) :
    inclT M (kap (csm θ M) x) = kap (chs M) (inclT (conjModel M) x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [kap_smul, map_smul, map_smul, kap_smul, kap_tprod, inclT, inclT, PiTensorProduct.map_tprod,
      PiTensorProduct.map_tprod, kap_tprod]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem act_kap (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (z : ⨂[ℂ] ρ, (conjModel M).H ρ) :
    kap (chs M) (actT (conjModel M) τ g z) = actT M τ g (kap (chs M) z) := by
  classical
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, kap_smul, kap_smul, map_smul, actT, actT, PiTensorProduct.map_tprod, kap_tprod, kap_tprod,
      PiTensorProduct.map_tprod]
    congr 2
    funext ρ
    by_cases h : ρ = τ
    · subst h
      simp only [Function.update_self]
      exact rep_conjModel M ρ g (f ρ)
    · simp only [Function.update_of_ne h]
      rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem ell_kap (M : DSModel V S) (w₁ : ∀ τ, (conjModel M).H τ) (z : ⨂[ℂ] ρ, (conjModel M).H ρ) :
    ellT (conjModel M) w₁ z = starRingEnd ℂ (ellT M (fun τ => cM M τ (w₁ τ)) (kap (chs M) z)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, kap_smul, map_smul, kap_tprod, ellT, ellT, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
    simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, smul_eq_mul,
      map_mul, map_prod, Complex.conj_conj]
    congr 1
    refine Finset.prod_congr rfl fun ρ _ => ?_
    change ⟪(cM M ρ (f ρ) : M.H ρ), cM M ρ (w₁ ρ)⟫_ℂ = starRingEnd ℂ ⟪(cM M ρ (w₁ ρ) : M.H ρ), cM M ρ (f ρ)⟫_ℂ
    exact (inner_conj_symm (𝕜 := ℂ) _ _).symm
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end Model

section Main

open GlobalTheory.ConjDS

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem cart_conjModel (M : DSModel V S) (τ : D.what₂.Tau) : cart (conjModel M) τ = cart M τ := by
  unfold cart
  show ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹ * Formalism.REAL.Jm (fun a => M.ε τ a.rev) *
      (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) = (M.fr τ)⁻¹ * Formalism.REAL.Jm (M.ε τ) * M.fr τ
  rw [inv_submatrix_equiv, ← rv_Jm (ε := fun a => M.ε τ a.rev) (ε' := M.ε τ) (fun a => by simp), rv,
    submatrix_mul_equiv, submatrix_mul_equiv]
  simp

theorem act_iff (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (x y : SmT (conjModel M)) :
    inclT (conjModel M) y = actT (conjModel M) τ g (inclT (conjModel M) x) ↔
      inclT M (kap (csm θ M) y) = actT M τ g (inclT M (kap (csm θ M) x)) := by
  rw [incl_kap, incl_kap, ← act_kap]
  exact (kap (chs M)).injective.eq_iff.symm

theorem ell_inv (M : DSModel V S) (w : ∀ τ, M.H τ) (z : ⨂[ℂ] ρ, (conjModel M).H ρ) :
    ellT M w (kap (chs M) z) = starRingEnd ℂ (ellT (conjModel M) (fun τ => (cM M τ).symm (w τ)) z) := by
  rw [ell_kap, Complex.conj_conj]
  congr 2

theorem der_iff (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau) (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (x y : SmT (conjModel M)) : DerT (conjModel M) τ Y x y ↔ DerT M τ Y (kap (csm θ M) x) (kap (csm θ M) y) := by
  unfold DerT
  constructor
  · intro h w
    have e1 : (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • Y)) (inclT M (kap (csm θ M) x)))) =
        fun t : ℝ => star (ellT (conjModel M) (fun τ => (cM M τ).symm (w τ))
          (actT (conjModel M) τ (NormedSpace.exp (t • Y)) (inclT (conjModel M) x))) := by
      funext t
      rw [incl_kap, ← act_kap, ell_inv]
      rfl
    have e2 : ellT M w (inclT M (kap (csm θ M) y)) =
        star (ellT (conjModel M) (fun τ => (cM M τ).symm (w τ)) (inclT (conjModel M) y)) := by
      rw [incl_kap, ell_inv]
      rfl
    rw [e1, e2]
    exact (h _).star
  · intro h w₁
    have e1 : (fun t : ℝ => ellT (conjModel M) w₁ (actT (conjModel M) τ (NormedSpace.exp (t • Y)) (inclT (conjModel M) x))) =
        fun t : ℝ => star (ellT M (fun τ => cM M τ (w₁ τ))
          (actT M τ (NormedSpace.exp (t • Y)) (inclT M (kap (csm θ M) x)))) := by
      funext t
      rw [ell_kap, act_kap, ← incl_kap]
      rfl
    have e2 : ellT (conjModel M) w₁ (inclT (conjModel M) y) =
        star (ellT M (fun τ => cM M τ (w₁ τ)) (inclT M (kap (csm θ M) y))) := by
      rw [ell_kap, ← incl_kap]
      rfl
    rw [e1, e2]
    exact (h _).star

theorem ell_field (θ : InfFam D) (M : DSModel V S) (w₁ : ∀ τ, (conjModel M).H τ) :
    ∃ w : ∀ τ, M.H τ, ∀ x, ellT (conjModel M) w₁ (inclT (conjModel M) x) =
      starRingEnd ℂ (ellT M w (inclT M (kap (csm θ M) x))) :=
  ⟨fun τ => cM M τ (w₁ τ), fun x => by rw [ell_kap, incl_kap]⟩

theorem mult_fw (θ : InfFam D) (M : DSModel V S) : ∀ F ∈ MultT θ M ∅ 1, ∃ F₁ ∈ MultT θ (conjModel M) ∅ 1,
    ∀ x g, F₁ x g = starRingEnd ℂ (F (kap (csm θ M) x) g) := by
  intro F hF
  have hT := (mem_multT θ M ∅ 1 F).1 hF
  obtain ⟨T', hT', hv⟩ :=
    (GlobalTheory.ConjMult.conj_mult θ M (conjModel M) (cM M) (fun τ g _ w => rep_conjModel M τ g w)).2 ∅ 1 _ hT
  have e1 : (fun k => star ((1 : GA D V → ℂ) k)) = 1 := by funext k; simp
  rw [e1] at hT'
  refine ⟨PiTensorProduct.lift T', (mem_multT θ _ ∅ 1 _).2 (by simpa using hT'), fun x g => ?_⟩
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, kap_smul, map_smul, PiTensorProduct.lift.tprod, kap_tprod]
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]
    rw [hv f (fun i => csm θ M i (f i)) (fun τ => rfl) g]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    simp only [Pi.add_apply, LinearMap.add_apply, map_add, hx, hy]

theorem mult_bw (θ : InfFam D) (M : DSModel V S) : ∀ F₁ ∈ MultT θ (conjModel M) ∅ 1, ∃ F ∈ MultT θ M ∅ 1,
    ∀ x g, F₁ x g = starRingEnd ℂ (F (kap (csm θ M) x) g) := by
  intro F₁ hF
  have hT := (mem_multT θ (conjModel M) ∅ 1 F₁).1 hF
  have hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w,
      (cM M τ).symm (M.rep τ g w) = (conjModel M).rep τ g ((cM M τ).symm w) := by
    intro τ g _ w
    apply (cM M τ).injective
    rw [LinearIsometryEquiv.apply_symm_apply, rep_conjModel, LinearIsometryEquiv.apply_symm_apply]
  obtain ⟨T', hT', hv⟩ :=
    (GlobalTheory.ConjMult.conj_mult θ (conjModel M) M (fun τ => (cM M τ).symm) hc).2 ∅ 1 _ hT
  have e1 : (fun k => star ((1 : GA D V → ℂ) k)) = 1 := by funext k; simp
  rw [e1] at hT'
  refine ⟨PiTensorProduct.lift T', (mem_multT θ _ ∅ 1 _).2 (by simpa using hT'), fun x g => ?_⟩
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, kap_smul, map_smul, kap_tprod, PiTensorProduct.lift.tprod]
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]
    rw [hv (fun i => csm θ M i (f i)) f (fun τ => by simp [csm_val]) g]
    simp [PiTensorProduct.lift_symm]
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    simp only [Pi.add_apply, LinearMap.add_apply, map_add, hx, hy]

theorem modelTr_conjModel (θ : InfFam D) (M : DSModel V S) :
    ModelTr (starRingEnd ℂ) false θ (V := V) (conjModel M) M (kap (csm θ M)) where
  smul c x := kap_smul _ c x
  cart τ := cart_conjModel M τ
  act τ g _ x y := act_iff θ M τ g x y
  der τ Y _ x y := der_iff θ M τ Y x y
  ell w₁ := ell_field θ M w₁
  vec v₁ := ⟨fun τ => csm θ M τ (v₁ τ), kap_tprod _ _, fun τ => rfl⟩
  mult := mult_fw θ M
  mult' := mult_bw θ M

end Main

theorem exists_conjModelTr : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : DSModel V S), ∃ (M₁ : DSModel (sgn false V) fun τ => dualPar (S τ)) (κ : SmT M₁ ≃+ SmT M),
      ModelTr (starRingEnd ℂ) false θ M₁ M κ := by
  intro D θ _ V S M
  exact ⟨GlobalTheory.ConjDS.conjModel M, kap (csm θ M), modelTr_conjModel θ M⟩

end GlobalTheory.ConjModelTr

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_series_model_conjugate_transfer : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ (M₁ : DSModel (sgn false V) fun τ => dualPar (S τ)) (κ : SmT M₁ ≃+ SmT M), ModelTr (starRingEnd ℂ) false θ M₁ M κ := by
  atlas_forward_decl GlobalTheory.ConjModelTr.exists_conjModelTr
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_frameChange_same_cartan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (V W : HSp D) (A A' : Fr V) (B B' : Fr W), (∀ τ, A'.cart τ = A.cart τ) → (∀ τ, B'.cart τ = B.cart τ) → ∃ j : PolF D W.rank V.rank ≃ₗ[ℂ] PolF D W.rank V.rank, ∀ f, IsThetaFunO ψ V W f → ∀ P, ptF ψ θ A' B' f (j P) = ptF ψ θ A B f P := by
  first | exact @GlobalTheory.FrameChange.ptF_frame_change | exact GlobalTheory.FrameChange.ptF_frame_change | (intros; apply GlobalTheory.FrameChange.ptF_frame_change <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_negatedSpace_discreteSeriesModelTransport : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ (M₁ : DSModel (sgn true V) fun τ => GlobalTheory.SignedHC.flip (S τ)) (κ : SmT M₁ ≃+ SmT M), ModelTr (RingHom.id ℂ) true θ M₁ M κ := by
  first | exact @GlobalTheory.negModel_tr | exact GlobalTheory.negModel_tr | (intros; apply GlobalTheory.negModel_tr <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaIntertwiner_adjoint_isRealThetaIntertwiner : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (Z P : Type) [AddCommGroup P] [Module ℂ P] (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (Z → ℂ)) (ω' : GA D W × GA D V →* Module.End ℂ (Z → ℂ)) (pt : P → Z → ℂ) (It : P →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M') (Tp : P → SmT M' →ₗ[ℂ] SmT M), (∀ g h, ω' (h, g) = ω (g, h)) → GlobalTheory.Grid.IsIntw θ M' M ω' pt It → (∀ (p : P) (v : M.Vec) (w : M'.Vec), ellT M' (fun τ => w τ) (inclT M' (It p (PiTensorProduct.tprod ℂ v))) = starRingEnd ℂ (ellT M (fun τ => v τ) (inclT M (Tp p (PiTensorProduct.tprod ℂ w))))) → IsIntwF θ M M' ω pt Tp := by
  first | exact @GlobalTheory.Adopt.realThetaIntertwiner_adjoint_isRealThetaIntertwiner | exact GlobalTheory.Adopt.realThetaIntertwiner_adjoint_isRealThetaIntertwiner | (intros; apply GlobalTheory.Adopt.realThetaIntertwiner_adjoint_isRealThetaIntertwiner <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredientThetaParams_addBlockArrow : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i j : ℕ) (τ : D.what₂.Tau), i < D.R.m → j ≤ D.R.m → PairPar (GlobalTheory.SignedHC.flip (parV D (i + 1) j τ)) (parV D i j τ) (att (cen D τ (D.R.m - i)) (rkV D (i + 1) j)) (att (cen D τ (D.R.m - i)) (rkV D i j)) := by
  first | exact @GlobalTheory.GridParD.pairPar_X | exact GlobalTheory.GridParD.pairPar_X | (intros; apply GlobalTheory.GridParD.pairPar_X <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredientThetaParams_removeBlockArrow : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i j : ℕ) (τ : D.what₂.Tau), i ≤ D.R.m → ∀ hj : j < D.R.m, PairPar (parV D i j τ) (parV D i (j + 1) τ) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j)) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1))) := by
  first | exact @GlobalTheory.RemoveBlock.removeBlock_pairPar | exact GlobalTheory.RemoveBlock.removeBlock_pairPar | (intros; apply GlobalTheory.RemoveBlock.removeBlock_pairPar <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredientThetaParams_columnArrows : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i : ℕ) (τ : D.what₂.Tau), i < D.R.m → PairPar (dualPar (GlobalTheory.SignedHC.flip (parP D (i + 1) τ))) (dualPar (parP D i τ)) (cen D τ (D.R.m - i)) (cen D τ (D.R.m - i)) ∧ PairPar (dualPar (parP D i τ)) (dualPar (GlobalTheory.SignedHC.flip (parP D (i + 1) τ))) (cen D τ (D.R.m - i)) (cen D τ (D.R.m - i)) := by
  first | exact @GlobalTheory.ParPairArrows.parPi_pairPar | exact GlobalTheory.ParPairArrows.parPi_pairPar | (intros; apply GlobalTheory.ParPairArrows.parPi_pairPar <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.TopPair

open GlobalTheory.SignedHC Finset

variable (D : D7) (τ : D.what₂.Tau)

local notation "Γ" => grid D τ

theorem grid_e {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).e l : ℤ) : ℚ) = (D.hc τ).e ⟨l - 1, by omega⟩ := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact GridData.extend_cast 1 (D.hc τ).e_int ⟨l, by omega⟩

theorem grid_b {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).b l : ℤ) : ℚ) = (D.hc τ).b ⟨l - 1, by omega⟩ := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact GridData.extend_cast 1 (D.hc τ).b_int ⟨l, by omega⟩

theorem grid_v {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : (((Γ).v i : ℤ) : ℚ) = (D.hc τ).v ⟨i - 2, by omega⟩ := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
  exact GridData.extend_cast 2 (D.hc τ).v_int ⟨i, by omega⟩

theorem grid_be {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).e l : ℚ) - (Γ).b l := by
  rw [grid_e D τ h1 h2, grid_b D τ h1 h2]
  exact (D.hc τ).gap_be _

theorem grid_eb {l : ℕ} (h1 : 1 ≤ l) (h2 : l + 1 ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).b (l + 1) : ℚ) - (Γ).e l := by
  rw [grid_e D τ h1 (by omega), grid_b D τ (by omega) h2]
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact (D.hc τ).gap_eb ⟨l, by omega⟩ (by simpa using (by omega : l + 1 < D.R.m))

theorem grid_e_lt {l l' : ℕ} (h1 : 1 ≤ l) (h : l < l') (h2 : l' ≤ D.R.m) : (D.R.t : ℚ) + 3 + (Γ).e l ≤ (Γ).e l' := by
  induction l', h using Nat.le_induction with
  | base =>
    linarith [grid_be D τ (l := l + 1) (by omega) h2, grid_eb D τ h1 h2]
  | succ n hn ih =>
    have := ih (by omega)
    have e1 := grid_be D τ (l := n + 1) (by omega) h2
    have e2 := grid_eb D τ (l := n) (by omega) h2
    have : (0 : ℚ) ≤ D.R.t := by positivity
    linarith

theorem grid_cloud {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : -((Γ).b 1 : ℚ) + 1 ≤ (Γ).v i := by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have base : -((Γ).b 1 : ℚ) < (Γ).v D.R.k := by
    rw [grid_v D τ hk le_rfl, grid_b D τ le_rfl hm]
    have e1 := (D.hc τ).u_last_gt (by omega) (by omega)
    have e2 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
    have e3 : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
    simp only [e3] at e2
    exact e1.trans e2
  have base' : -((Γ).b 1) < (Γ).v D.R.k := by exact_mod_cast base
  have step : (Γ).v D.R.k ≤ (Γ).v i := by
    rcases h2.eq_or_lt with rfl | h
    · exact le_rfl
    · exact ((Γ).v_anti i D.R.k h1 h le_rfl).le
  have : -((Γ).b 1) + 1 ≤ (Γ).v i := by omega
  exact_mod_cast this

theorem grid_a_le {i j : ℕ} (h : i ≤ j) : (Γ).a j ≤ (Γ).a i := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · have : (0 : ℚ) ≤ (Γ).ga := by positivity
    linarith [GlobalTheory.ChiGrid.a_add_le (G := Γ) h]

theorem grid_blockMPlus_bd {l : ℕ} {x : ℚ} (h : x ∈ (Γ).blockMPlus l) :
    -((Γ).e l : ℚ) - (D.R.t : ℚ) / 2 ≤ x ∧ x ≤ -((Γ).e l : ℚ) + (D.R.t : ℚ) / 2 := by
  have := abs_le.1 (abs_sub_le_of_mem_block h)
  have e : (((Γ).t + 1 : ℕ) : ℚ) = D.R.t + 1 := by push_cast; rfl
  rw [e] at this
  constructor <;> linarith [this.1, this.2]

theorem grid_s_lt_gap : (Γ).s < (Γ).ga := by
  have := (isLeast_gap D).1.2.1
  show sLen D < gap D
  omega

theorem grid_length_odd : Odd (Γ).s := GlobalTheory.ChiGrid.odd_sLen D

theorem grid_weightX_above {j : ℕ} (hj : j + 1 ≤ D.R.m) {x y : ℚ} (hx : x ∈ (Γ).weightX j)
    (hy : y ∈ (Γ).blockMPlus (j + 1)) : y < x := by
  have hm : 1 ≤ D.R.m := by omega
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have hg : (0 : ℚ) ≤ (Γ).ga := by positivity
  obtain ⟨y1, y2⟩ := grid_blockMPlus_bd D τ hy
  have hbe := grid_be D τ (l := 1) le_rfl hm
  have he1 : ((Γ).e 1 : ℚ) ≤ (Γ).e (j + 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact le_rfl
    · linarith [grid_e_lt D τ (l := 1) (l' := j + 1) le_rfl (by omega) hj]
  have hlow : y < -((Γ).b 1 : ℚ) := by linarith
  have hc2 := grid_cloud D τ (i := 2) le_rfl hk
  have ham : (Γ).a (Γ).m = (Γ).v 2 + (Γ).ga + 1 / 2 := (Γ).a_m
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, h⟩
  · obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h
    linarith [grid_a_le D τ hi]
  · obtain ⟨i, h1, h2, rfl⟩ := GridData.mem_cloudHalf.1 h
    have := grid_cloud D τ h1 h2
    simp only [GridData.vHalf]
    linarith
  · have := (GlobalTheory.ChiGrid.blockC'_between (grid_nearMid D τ) (grid_length_odd D τ).pos (grid_s_lt_gap D τ) h1 h2 h).1
    linarith [grid_a_le D τ h2]
  · have := grid_e_lt D τ h1 (by omega : l < j + 1) hj
    have := (grid_blockMPlus_bd D τ h).1
    linarith

theorem grid_inCoset_weightX {j : ℕ} : InCoset (1 / 2) ((Γ).weightX j) := by
  induction j with
  | zero => exact GlobalTheory.ChiGrid.inCoset_weightX_zero (grid_length_odd D τ)
  | succ j ih =>
    rw [(Γ).weightX_succ]
    intro x hx
    rcases mem_union.1 hx with h | h
    · exact ih x h
    · obtain ⟨a, -, rfl⟩ := mem_block.1 h
      obtain ⟨u, hu⟩ := D.R.t_odd
      have e : ((Γ).t : ℚ) = 2 * u + 1 := by
        have : ((Γ).t : ℚ) = D.R.t := rfl
        rw [this, hu]; push_cast; ring
      refine ⟨-(Γ).e (j + 1) + u - a, ?_⟩
      push_cast
      rw [e]
      ring

theorem grid_card_weightX_le (j : ℕ) : ((Γ).weightX j).card ≤ D.R.k + D.R.m * sLen D + j * (D.R.t + 1) := by
  have c1 : (Γ).tops.card ≤ D.R.m + 1 := by
    unfold GridData.tops
    exact card_image_le.trans (by simp; rfl)
  have c2 : (Γ).cloudHalf.card ≤ D.R.k - 1 := by
    unfold GridData.cloudHalf
    refine card_image_le.trans ?_
    rw [Nat.card_Icc]
    show D.R.k + 1 - 2 ≤ D.R.k - 1
    omega
  have c3 : ((Icc 1 (Γ).m).biUnion (Γ).blockC').card ≤ D.R.m * (sLen D - 1) := by
    refine card_biUnion_le.trans ?_
    simp only [GridData.blockC', card_block, sum_const, Nat.card_Icc, smul_eq_mul]
    show (D.R.m + 1 - 1) * (sLen D - 1) ≤ _
    simp
  have c4 : ((Icc 1 j).biUnion (Γ).blockMPlus).card ≤ j * (D.R.t + 1) := by
    refine card_biUnion_le.trans ?_
    simp only [GridData.blockMPlus, card_block, sum_const, Nat.card_Icc, smul_eq_mul]
    show (j + 1 - 1) * (D.R.t + 1) ≤ _
    simp
  have hs : 1 ≤ sLen D := (grid_length_odd D τ).pos
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have e : D.R.m * sLen D = D.R.m * (sLen D - 1) + D.R.m := by
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hs)]
  rw [GridData.weightX, GridData.entries_lam]
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)) _).trans ?_
  omega

theorem pairPar_top : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (j : ℕ) (τ : D.what₂.Tau) (hj : j < D.R.m),
    PairPar (dualPar (parXp D (j + 1) τ)) (dualPar (parXp D j τ)) (-(D.hc τ).e ⟨j, hj⟩) (-(D.hc τ).e ⟨j, hj⟩) := by
  intro D hS j τ hj
  set G := grid D τ with hG
  have hj' : j + 1 ≤ D.R.m := hj
  have hce : (D.hc τ).e ⟨j, hj⟩ = ((G.e (j + 1) : ℤ) : ℚ) := by
    have := grid_e D τ (l := j + 1) (by omega) hj'
    simp only [Nat.add_sub_cancel] at this
    exact this.symm
  set c : ℚ := -(D.hc τ).e ⟨j, hj⟩ with hc
  have hblock : G.blockMPlus (j + 1) = TPar.block c (D.R.t + 1) := by
    rw [hc, hce]; rfl

  have habove : ∀ x ∈ G.weightX j, c + (D.R.t : ℚ) / 2 + 1 ≤ x := by
    intro x hx
    have htop : c + (D.R.t : ℚ) / 2 ∈ TPar.block c (D.R.t + 1) :=
      mem_block.2 ⟨0, by omega, by push_cast; ring⟩
    have hlt := grid_weightX_above D τ hj' hx (hblock ▸ htop)
    obtain ⟨z, hz⟩ := grid_inCoset_weightX D τ (j := j) x hx
    obtain ⟨u, hu⟩ := D.R.t_odd
    have ht : (D.R.t : ℚ) = 2 * u + 1 := by rw [hu]; push_cast; ring
    obtain ⟨w, hw⟩ : ∃ w : ℤ, c = w := ⟨-(G.e (j + 1)), by rw [hc, hce]; push_cast; ring⟩
    rw [hz, hw, ht] at hlt ⊢
    have : (w : ℚ) + u < z := by linarith
    have h2 : w + u < z := by exact_mod_cast this
    have h3 : ((w + u + 1 : ℤ) : ℚ) ≤ z := by exact_mod_cast Int.add_one_le_iff.2 h2
    push_cast at h3
    linarith
  have hX : parXp D j τ = G.parX j := rfl
  have hX' : parXp D (j + 1) τ = G.parX (j + 1) := rfl
  have hpart : partner (D.R.t + 1) true c c (G.parX j) = G.parX (j + 1) := by
    unfold partner
    have h1 : ((G.parX j).image fun x : ℚ × Bool => (x.1 - c + c, if x.1 < c then !x.2 else x.2)) = G.parX j := by
      rw [← image_id (s := G.parX j)]
      rw [image_image]
      refine image_congr fun x hx => ?_
      have hx1 : x.1 ∈ G.weightX j := (mem_plus.1 hx).1
      have := habove _ hx1
      have ht : (0 : ℚ) ≤ D.R.t := by positivity
      have hn : ¬ x.1 < c := by linarith
      simp [hn]
    rw [h1, GridData.parX, GridData.parX, GridData.weightX_succ, plus_union, hblock]
    rfl
  have hT : (((D.R.t + 1 : ℕ) : ℚ) + 1) / 2 = (D.R.t : ℚ) / 2 + 1 := by push_cast; ring
  have hne : (G.parX j).Nonempty := by
    refine ⟨(G.a 0, true), mem_plus.2 ⟨GridData.mem_weightX.2 (Or.inl (GridData.mem_tops.2 ⟨0, by omega, rfl⟩)), rfl⟩⟩
  have hcos : InCoset (c + (((D.R.t + 1 : ℕ) : ℚ) + 1) / 2) (entries (G.parX j)) := by
    rw [GridData.parX, entries_plus, hT]
    intro x hx
    obtain ⟨z, hz⟩ := grid_inCoset_weightX D τ (j := j) x hx
    obtain ⟨u, hu⟩ := D.R.t_odd
    have ht : (D.R.t : ℚ) = 2 * u + 1 := by rw [hu]; push_cast; ring
    obtain ⟨w, hw⟩ : ∃ w : ℤ, c = w := ⟨-(G.e (j + 1)), by rw [hc, hce]; push_cast; ring⟩
    refine ⟨z - w - u - 1, ?_⟩
    rw [hz, hw, ht]; push_cast; ring
  have hfar : FarFrom c ((((D.R.t + 1 : ℕ) : ℚ) + 1) / 2) (G.parX j) := by
    rw [hT]
    intro x hx
    rw [GridData.parX, entries_plus] at hx
    have := habove x hx
    have h0 : (0 : ℚ) ≤ D.R.t := by positivity
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hcard : (G.parX j).card + (D.R.t + 1) ≤ bigN D := by
    rw [GridData.parX, ← (isRegular_plus _).card_entries, entries_plus]
    have := grid_card_weightX_le D τ j
    have e : bigN D = D.R.k + D.R.m * (D.R.t + sLen D + 1) := rfl
    have : (j + 1) * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_right _ hj'
    rw [e]
    nlinarith
  have hN : 1800 < bigN D := by
    have h1 := hS.1
    have e : bigN D = D.R.k + D.R.m * (D.R.t + sLen D + 1) := rfl
    have : D.R.m ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold Ranks.r at h1
    omega
  have hgap : ∀ E : Finset ℚ, GapOver (plus E) (2 * (bigN D : ℚ) ^ 3) := by
    intro E x hx y hy hxy
    exact absurd ((mem_plus.1 hx).2.trans (mem_plus.1 hy).2.symm) hxy
  have key := GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter (D.R.t + 1) true c c (G.parX j) (bigN D) (by omega) hne (isRegular_plus _) hcos hfar hcard hN
    (hgap _) (by rw [hpart]; exact hgap _)
  rw [hpart] at key
  exact ⟨D.R.t + 1, parXp D (j + 1) τ, parXp D j τ, rfl, rfl, Or.inr key⟩

end GlobalTheory.TopPair
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredientThetaParams_lastRowArrows : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (j : ℕ) (τ : D.what₂.Tau) (hj : j < D.R.m), PairPar (dualPar (parXp D (j + 1) τ)) (dualPar (parXp D j τ)) (-(D.hc τ).e ⟨j, hj⟩) (-(D.hc τ).e ⟨j, hj⟩) := by
  atlas_forward_decl GlobalTheory.TopPair.pairPar_top
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift

theorem rulePar_of_pairPar {X : ProvA} (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X)
    {S S' : SPar} {aS aT : ℚ} (h : PairPar S S' aS aT) : RulePar X S S' aS aT := by
  have far : ∀ {t : ℕ} {al be ga de : List ℚ}, GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) (signed (al ++ be) (ga ++ de) aT) →
      ¬ ∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2 := by
    rintro t al be ga de hF ⟨a, ha⟩
    have hm : (((t : ℚ) + 1) / 2, a.isLeft) ∈ GlobalTheory.SignedHC.ofIx (lamA al be ga de) :=
      Finset.mem_image.2 ⟨a, Finset.mem_univ _, by rw [ha]⟩
    rw [lamA, GlobalTheory.SignedHC.mem_ofIx_ofBlocks (by simp) (by simp)] at hm
    have : ∃ s, (((t : ℚ) + 1) / 2 + aT, s) ∈ signed (al ++ be) (ga ++ de) aT := by
      rcases hm with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨true, Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩
      · exact ⟨false, Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩
    have := hF _ (GlobalTheory.SignedHC.mem_entries.2 this)
    rw [add_sub_cancel_right, abs_of_nonneg (by positivity)] at this
    linarith
  have hb : ∀ t, (block t).length = t := fun t => by simp [block]
  obtain ⟨t, P, P', e, e', ⟨⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩, hF⟩ | ⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩⟩ := h
  all_goals
    have ht := hd.1.1
    have hn := hd.1.2.1
    obtain ⟨-, p1, p2, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hd.1
    obtain ⟨-, p3, -⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hd.1
  · exact ⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp [hb]; omega, by simp,
      ⟨by omega, by omega, p1, p2, (h3.1 t al be ga de hd).2.1, (h3.1 t al be ga de hd).2.2,
        h5.1 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩
  · exact ⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp, by simp [hb]; omega,
      ⟨by omega, by omega, p1, p3, (h3.2 t al be ga de hd).2.1, (h3.2 t al be ga de hd).2.2,
        h5.2 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩
  · have sw := GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamA' t al be ga de)
    exact ⟨_, _, _, _, _, _, _, _, by simp [hb]; omega, by simp, by simp, by simp,
      ⟨by omega, by omega, p2, p1, sw.1 (h3.1 t al be ga de hd).1, sw.2.1 (h3.1 t al be ga de hd).2.2,
        sw.2.2 (h4.1 t al be ga de hd)⟩, e, e'⟩
  · have sw := GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamM' t al be ga de)
    exact ⟨_, _, _, _, _, _, _, _, by simp, by simp [hb]; omega, by simp, by simp,
      ⟨by omega, by omega, p3, p1, sw.1 (h3.2 t al be ga de hd).1, sw.2.1 (h3.2 t al be ga de hd).2.2,
        sw.2.2 (h4.2 t al be ga de hd)⟩, e, e'⟩

def IdOrConj (σ : ℂ →+* ℂ) : Prop := σ = RingHom.id ℂ ∨ σ = starRingEnd ℂ

theorem IdOrConj.invol {σ : ℂ →+* ℂ} (h : IdOrConj σ) (z : ℂ) : σ (σ z) = z := by
  rcases h with rfl | rfl <;> simp

theorem IdOrConj.norm {σ : ℂ →+* ℂ} (h : IdOrConj σ) (z : ℂ) : ‖σ z‖ = ‖z‖ := by
  rcases h with rfl | rfl <;> simp

theorem IdOrConj.deriv {σ : ℂ →+* ℂ} (h : IdOrConj σ) {f : ℝ → ℂ} {a : ℂ} (hf : HasDerivAt (fun t => σ (f t)) (σ a) 0) :
    HasDerivAt f a 0 := by
  rcases h with rfl | rfl
  · exact hf
  · simpa using hf.star

theorem IdOrConj.integral {σ : ℂ →+* ℂ} (h : IdOrConj σ) {G : Type} [MeasurableSpace G] (μ : Measure G) (f : G → ℂ) :
    (Integrable (fun g => σ (f g)) μ → Integrable f μ) ∧ ∫ g, σ (f g) ∂μ = σ (∫ g, f g ∂μ) := by
  rcases h with rfl | rfl
  · exact ⟨id, rfl⟩
  · exact ⟨fun hf => Complex.conjCLE.integrable_comp_iff.1 hf, integral_conj⟩

variable {D : D7} {θ : InfFam D}

section Transport

variable {A B : HSp D} {SA SB SA₁ SB₁ : D.what₂.Tau → SPar} {MA : DSModel A SA} {MB : DSModel B SB} {εA εB : Bool}
  {MA₁ : DSModel (sgn εA A) SA₁} {MB₁ : DSModel (sgn εB B) SB₁} {σ : ℂ →+* ℂ} {κA : SmT MA₁ ≃+ SmT MA}
  {κB : SmT MB₁ ≃+ SmT MB}

theorem LiftsM.transport (hθ : IsInfFam θ) (hσ : IdOrConj σ) (hA : ModelTr σ εA θ MA₁ MA κA) (hB : ModelTr σ εB θ MB₁ MB κB)
    {P P₁ : Type} (j : P → P₁) {K : P → GA D B → GA D A → ℂ} {K₁ : P₁ → GA D (sgn εB B) → GA D (sgn εA A) → ℂ}
    {It : P → SmT MA → SmT MB} {It₁ : P₁ → SmT MA₁ → SmT MB₁}
    (hK : ∀ p h g, K₁ (j p) h g = σ (K p (ofSgn εB B h) (ofSgn εA A g))) (hI : ∀ p v, κB (It₁ (j p) v) = It p (κA v))
    {ν : Measure (GA D A)} {𝓕 : Set (GA D A)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 ν)
    (H : ∀ ν₁ 𝓕₁, ν₁.IsHaarMeasure → IsFundamentalDomain (GQ (sgn εA A)) 𝓕₁ ν₁ → LiftsM θ MA₁ MB₁ ν₁ 𝓕₁ K₁ It₁) :
    LiftsM θ MA MB ν 𝓕 K It := by
  intro F hF
  obtain ⟨ν₁, a, b, c⟩ := (GlobalTheory.T.signedUnitaryGroup_compat D θ hθ εA A).meas ν 𝓕 hν h𝓕
  obtain ⟨F₁, hF₁, e₁⟩ := hA.mult F hF
  obtain ⟨F₂, hF₂, e₂⟩ := H ν₁ _ a b F₁ hF₁
  obtain ⟨F', hF', e'⟩ := hB.mult' F₂ hF₂
  refine ⟨F', hF', fun p v h => ?_⟩
  obtain ⟨v, rfl⟩ := κA.surjective v
  obtain ⟨h, rfl⟩ := (ofSgn εB B).surjective h
  obtain ⟨i1, i2⟩ := e₂ (j p) v h
  simp only [hK, e₁, ← map_mul] at i1 i2
  obtain ⟨c1, c2⟩ := c fun g => σ (K p (ofSgn εB B h) g * F (κA v) g)
  obtain ⟨d1, d2⟩ := hσ.integral (ν.restrict 𝓕) fun g => K p (ofSgn εB B h) g * F (κA v) g
  refine ⟨d1 (c1.1 i1), σ.injective ?_⟩
  rw [← d2, ← c2, i2, e', hI]

theorem IsIntwF.transport (hθ : IsInfFam θ) (hσ : IdOrConj σ) (hA : ModelTr σ εA θ MA₁ MA κA)
    (hB : ModelTr σ εB θ MB₁ MB κB) {Z P : Type} {ω : GA D B × GA D A →* Module.End ℂ (Z → ℂ)} {pt : P → Z → ℂ}
    {It : P → SmT MA →ₗ[ℂ] SmT MB} (H : IsIntwF θ MB MA ω pt It) {ρ : ℂ →+* ℂ} (hρ : IdOrConj ρ)
    {α : WO (sgn εB B) (sgn εA A) → Z} (hα : Function.Surjective α) {ω₁ : WRep (sgn εB B) (sgn εA A)}
    (hω : ∀ h g f, ω₁ (h, g) (fun y => ρ (f (α y))) = fun y => ρ (ω (ofSgn εB B h, ofSgn εA A g) f (α y)))
    {j : P → PolF D (sgn εA A).rank (sgn εB B).rank} (hj : Function.Surjective j)
    {pt₁ : PolF D (sgn εA A).rank (sgn εB B).rank → WO (sgn εB B) (sgn εA A) → ℂ}
    (hpt : ∀ p, pt₁ (j p) = fun y => ρ (pt p (α y)))
    {It₁ : PolF D (sgn εA A).rank (sgn εB B).rank →ₗ[ℂ] SmT MA₁ →ₗ[ℂ] SmT MB₁}
    (hI : ∀ p v, κB (It₁ (j p) v) = It p (κA v)) : IsItW θ MB₁ MA₁ ω₁ pt₁ It₁ := by
  have lA := GlobalTheory.T.signedUnitaryGroup_compat D θ hθ εA A
  have lB := GlobalTheory.T.signedUnitaryGroup_compat D θ hθ εB B
  have inj : ∀ {f f' : Z → ℂ}, ((fun y => ρ (f (α y))) = fun y => ρ (f' (α y))) → f = f' := fun {f f'} h => by
    funext z
    obtain ⟨y, rfl⟩ := hα z
    exact ρ.injective (congrFun h y)
  refine ⟨fun h0 => ?_, fun φ w => ?_, fun τ g hg φ φ' h v => ?_, fun τ Y hY φ φ' h v => ?_,
    fun τ g hg φ φ' v v' h h' => ?_, fun τ Y hY φ φ' v v' h h' => ?_⟩
  · obtain ⟨φ, hφ⟩ := H.ne
    refine hφ (LinearMap.ext fun v => ?_)
    obtain ⟨v, rfl⟩ := κA.surjective v
    rw [← hI, h0]
    simp
  · obtain ⟨φ, rfl⟩ := hj φ
    obtain ⟨w', hw⟩ := hB.ell w
    obtain ⟨c, hc⟩ := H.bdd φ w'
    refine ⟨c, fun v => ?_⟩
    obtain ⟨v', e1, e2⟩ := hA.vec v
    rw [hw, hσ.norm, hI, e1]
    simpa only [e2] using hc v'
  · obtain ⟨φ, rfl⟩ := hj φ
    obtain ⟨φ', rfl⟩ := hj φ'
    rw [lB.grp] at hg
    rw [hpt, hpt, hω, lB.atTau, map_one] at h
    rw [hB.act τ g hg, hI, hI]
    exact H.eqK τ g hg φ φ' (inj h) _
  · obtain ⟨φ, rfl⟩ := hj φ
    obtain ⟨φ', rfl⟩ := hj φ'
    rw [lB.lie] at hY
    rw [hB.der τ Y hY, hI, hI]
    refine H.eqg τ Y hY φ φ' (fun z => ?_) _
    obtain ⟨y, rfl⟩ := hα z
    have := h y
    simp only [hpt, hω, oneP, lB.atTau, map_one] at this
    exact hρ.deriv this
  · obtain ⟨φ, rfl⟩ := hj φ
    obtain ⟨φ', rfl⟩ := hj φ'
    rw [lA.grp] at hg
    rw [hpt, hpt, hω, lA.atTau, map_one] at h
    apply κB.injective
    rw [hI, hI]
    exact H.invK τ g hg φ φ' _ _ (inj h) ((hA.act τ g hg _ _).1 h')
  · obtain ⟨φ, rfl⟩ := hj φ
    obtain ⟨φ', rfl⟩ := hj φ'
    rw [lA.lie] at hY
    apply κB.injective
    rw [map_add, map_zero, hI, hI]
    refine H.invg τ Y hY φ φ' _ _ (fun z => ?_) ((hA.der τ Y hY _ _).1 h')
    obtain ⟨y, rfl⟩ := hα z
    have := h y
    simp only [hpt, hω, oneP, lA.atTau, map_one] at this
    exact hρ.deriv this

theorem exists_bilin (hσ : IdOrConj σ) (hA : ModelTr σ εA θ MA₁ MA κA) (hB : ModelTr σ εB θ MB₁ MB κB)
    {P₁ : Type} [AddCommGroup P₁] [Module ℂ P₁] (It : P₁ → SmT MA →ₗ[ℂ] SmT MB) (h1 : ∀ p q, It (p + q) = It p + It q)
    (h2 : ∀ (c : ℂ) p, It (c • p) = σ c • It p) :
    ∃ It₁ : P₁ →ₗ[ℂ] SmT MA₁ →ₗ[ℂ] SmT MB₁, ∀ p v, κB (It₁ p v) = It p (κA v) := by
  have hs : ∀ (c : ℂ) x, κB.symm (σ c • x) = c • κB.symm x := fun c x =>
    κB.injective (by rw [hB.smul, κB.apply_symm_apply, κB.apply_symm_apply])
  exact ⟨LinearMap.mk₂ ℂ (fun p v => κB.symm (It p (κA v))) (fun p q v => by simp [h1])
    (fun c p v => by simp only [h2, LinearMap.smul_apply, hs]) (fun p v w => by simp)
    (fun c p v => by simp only [hA.smul, map_smul, hs]), fun p v => κB.apply_symm_apply _⟩

end Transport

theorem ModelTr.refl {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) :
    ModelTr (RingHom.id ℂ) false θ (V := V) (S₁ := S) M M (AddEquiv.refl _) :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl, fun w => ⟨w, fun _ => rfl⟩,
    fun v => ⟨v, rfl, fun _ => rfl⟩, fun F h => ⟨F, h, fun _ _ => rfl⟩, fun F h => ⟨F, h, fun _ _ => rfl⟩⟩

theorem exists_conj_neg (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) :
    ∃ (M₁ : DSModel (sgn true V) fun τ => dualPar (GlobalTheory.SignedHC.flip (S τ))) (κ : SmT M₁ ≃+ SmT M),
      ModelTr (starRingEnd ℂ) true θ M₁ M κ := by
  obtain ⟨N, κ, h⟩ := GlobalTheory.T.exists_negatedSpace_discreteSeriesModelTransport D θ hθ V S M
  obtain ⟨M₁, κ', h'⟩ := GlobalTheory.T.discrete_series_model_conjugate_transfer D θ hθ (sgn true V) _ N
  have l := GlobalTheory.T.signedUnitaryGroup_compat D θ hθ true V
  refine ⟨M₁, κ'.trans κ, fun c x => ?_, fun τ => (h'.cart τ).trans (h.cart τ), fun τ g hg x y => ?_, fun τ Y hY x y => ?_,
    fun w => ?_, fun v => ?_, fun F hF => ?_, fun F hF => ?_⟩
  · exact (congrArg κ (h'.smul c x)).trans (h.smul _ _)
  · exact (h'.act τ g (by rwa [l.grp]) x y).trans (h.act τ g hg _ _)
  · exact (h'.der τ Y (by rwa [l.lie]) x y).trans (h.der τ Y hY _ _)
  · obtain ⟨w', e'⟩ := h'.ell w
    obtain ⟨w'', e⟩ := h.ell w'
    exact ⟨w'', fun x => (e' x).trans (congrArg _ (e _))⟩
  · obtain ⟨v', e1, e2⟩ := h'.vec v
    obtain ⟨v'', e3, e4⟩ := h.vec v'
    exact ⟨v'', (congrArg κ e1).trans e3, fun τ => (e4 τ).trans (e2 τ)⟩
  · obtain ⟨F', a, b⟩ := h.mult F hF
    obtain ⟨F'', c, d⟩ := h'.mult F' a
    exact ⟨F'', c, fun x g => (d x g).trans (congrArg _ (b _ _))⟩
  · obtain ⟨F', a, b⟩ := h'.mult' F hF
    obtain ⟨F'', c, d⟩ := h.mult' F' a
    exact ⟨F'', c, fun x g => (b x g).trans (congrArg _ (d _ _))⟩

theorem lifts_of_tr {X : ProvA} (hP : PairLifts D X) (hθ : IsInfFam θ) {A B : HSp D} {SA SB SA₁ SB₁ : D.what₂.Tau → SPar}
    {MA : DSModel A SA} {MB : DSModel B SB} {εA εB : Bool} {MA₁ : DSModel (sgn εA A) SA₁} {MB₁ : DSModel (sgn εB B) SB₁}
    {σ : ℂ →+* ℂ} {κA : SmT MA₁ ≃+ SmT MA} {κB : SmT MB₁ ≃+ SmT MB} (hσ : IdOrConj σ) (hA : ModelTr σ εA θ MA₁ MA κA)
    (hB : ModelTr σ εB θ MB₁ MB κB) {aS aT : D.what₂.Tau → ℚ} (hR : ∀ τ, RulePar X (SB₁ τ) (SA₁ τ) (aS τ) (aT τ))
    {ψ : AddChar (AF D.host.F) ℂ} {ω₁ : WRep (sgn εB B) (sgn εA A)} (hW : IsWeilExp ψ _ _ aS aT ω₁)
    {Z P : Type} {ω : GA D B × GA D A →* Module.End ℂ (Z → ℂ)} {pt : (Z → ℂ) → P → Z → ℂ} {vac : (Z → ℂ) → Prop}
    {ρ : ℂ →+* ℂ} (hρ : IdOrConj ρ) {α : WO (sgn εB B) (sgn εA A) → Z} (hα : Function.Surjective α)
    (hω : ∀ h g f, ω₁ (h, g) (fun y => ρ (f (α y))) = fun y => ρ (ω (ofSgn εB B h, ofSgn εA A g) f (α y)))
    (j : P ≃ PolF D (sgn εA A).rank (sgn εB B).rank)
    (hpt : ∀ f, vac f → IsVacF ψ θ (Fr.ofModel MB₁) (Fr.ofModel MA₁) (fun y => ρ (f (α y))) ∧
      ∀ p, ptOf ψ θ MB₁ MA₁ (fun y => ρ (f (α y))) (j p) = fun y => ρ (pt f p (α y)))
    {f₀ : Z → ℂ} (hf₀ : vac f₀) (h0 : f₀ ≠ 0) {It : P → SmT MA →ₗ[ℂ] SmT MB} (H : IsIntwF θ MB MA ω (pt f₀) It)
    (h1 : ∀ p q, It (j.symm (p + q)) = It (j.symm p) + It (j.symm q))
    (h2 : ∀ (c : ℂ) p, It (j.symm (c • p)) = σ c • It (j.symm p)) {f : Z → ℂ} (hf : vac f)
    {K : P → GA D B → GA D A → ℂ} (hK : ∀ p h g, ρ (ω (h, g) (pt f p) (α 0)) = σ (K p h g))
    {ν : Measure (GA D A)} {𝓕 : Set (GA D A)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 ν) :
    LiftsM θ MA MB ν 𝓕 K fun p v => It p v := by
  obtain ⟨It₁, hI⟩ := exists_bilin hσ hA hB (fun p => It (j.symm p)) h1 h2
  have hI' : ∀ p v, κB (It₁ (j p) v) = It p (κA v) := fun p v => by rw [hI, j.symm_apply_apply]
  have hv : IsVacVec ψ θ MB₁ MA₁ fun y => ρ (f₀ (α y)) := ⟨(hpt f₀ hf₀).1.1, fun h => h0 (funext fun z => by
    obtain ⟨y, rfl⟩ := hα z
    exact ρ.injective ((congrFun h y).trans (map_zero ρ).symm)), (hpt f₀ hf₀).1.2⟩
  refine LiftsM.transport hθ hσ hA hB j (fun p h g => ?_) hI' hν h𝓕 fun ν₁ 𝓕₁ a b =>
    hP _ _ aS aT hR _ _ MB₁ MA₁ θ ψ hθ ω₁ hW _ It₁ hv
      (H.transport hθ hσ hA hB hρ hα hω j.surjective (hpt f₀ hf₀).2 hI') ν₁ 𝓕₁ a b _ (hpt f hf).1
  rw [(hpt f hf).2, thetaKO, hω]
  exact hK _ _ _

variable {ψ : AddChar (AF D.host.F) ℂ} {ε : Bool} {S T : Node D}

theorem fock_eq (f : WO S.V T.V → ℂ) (p : GlobalTheory.Grid.Pol S T) :
    ptF ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) f p = fock ψ θ ε S T f p := by
  have : (frSgn ε (Fr.ofModel S.M)).cart = cartS ε S := funext fun τ => cart_frSgn ε _ τ
  unfold ptF fock
  rw [this]
  rfl

theorem isVacF_congr {V W : HSp D} {A A' : Fr V} {B B' : Fr W} (hA : ∀ τ, A'.cart τ = A.cart τ)
    (hB : ∀ τ, B'.cart τ = B.cart τ) {f : WO V W → ℂ} (h : IsVacF ψ θ A B f) : IsVacF ψ θ A' B' f :=
  ⟨h.1, fun τ => by rw [hA, hB]; exact h.2 τ⟩

theorem isVacF_of_finVec {f : WO S.V T.V → ℂ} (h : IsFinVec ψ θ ε S T f) :
    IsVacF ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) f :=
  ⟨h.1, fun τ => by rw [cart_frSgn]; exact h.2 τ⟩

theorem vac_ne {f : WO S.V T.V → ℂ} (h : IsVac ψ θ ε S T f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, h⟩ := h.2.norm
  have := h p hp
  simp [nrm2] at this

theorem lifts_toSource {X : ProvA} (hP : PairLifts D X) (hθ : IsInfFam θ) {σ : ℂ →+* ℂ} (hσ : IdOrConj σ)
    {S₁ T₁ : D.what₂.Tau → SPar} {MS : DSModel (sgn ε S.V) S₁} {MT : DSModel (sgn false T.V) T₁}
    {κS : SmT MS ≃+ SmT S.M} {κT : SmT MT ≃+ SmT T.M} (hS : ModelTr σ ε θ MS S.M κS) (hT : ModelTr σ false θ MT T.M κT)
    {aS aT : D.what₂.Tau → ℚ} (hR : ∀ τ, RulePar X (S₁ τ) (T₁ τ) (aS τ) (aT τ)) {χS χT : (AE D)ˣ →* Circle}
    {ω : WRep S.V T.V} (hW : IsWeil ψ ε S.V T.V χS χT ω) (he : ∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ))
    {f₀ : WO S.V T.V → ℂ} (hf₀ : IsVac ψ θ ε S T f₀) {It : GlobalTheory.Grid.Pol S T → SmT T.M →ₗ[ℂ] SmT S.M}
    (H : IsIntwF θ S.M T.M ω (fock ψ θ ε S T f₀) It) (h1 : ∀ p q, It (p + q) = It p + It q)
    (h2 : ∀ (c : ℂ) p, It (c • p) = σ c • It p) {f : WO S.V T.V → ℂ} (hf : IsFinVec ψ θ ε S T f) {m : T.MeasDat}
    (hm : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ T.V) m.fd m.ν) :
    LiftsM θ T.M S.M m.ν m.fd (fun p h g => σ (thetaKO ω h g (fock ψ θ ε S T f p))) fun p v => It p v := by
  have cS : ∀ τ, (Fr.ofModel MS).cart τ = (frSgn ε (Fr.ofModel S.M)).cart τ := fun τ =>
    (hS.cart τ).trans (cart_frSgn ε (Fr.ofModel S.M) τ).symm
  have cT : ∀ τ, (Fr.ofModel MT).cart τ = (Fr.ofModel T.M).cart τ := hT.cart
  obtain ⟨j, hj⟩ := GlobalTheory.T.fockVector_frameChange_same_cartan D ψ θ hW.std hθ (sgn ε S.V) T.V _ _ _ _ cS cT
  exact lifts_of_tr hP hθ hσ hT hS hR (ω₁ := ω.toSgn ε) ⟨χS, χT, hW, he⟩ (pt := fun f p => fock ψ θ ε S T f p)
    (vac := IsFinVec ψ θ ε S T) (Or.inl rfl) (α := fun y => y) Function.surjective_id (fun _ _ _ => rfl) j.toEquiv
    (fun f hf => ⟨isVacF_congr cS cT (isVacF_of_finVec hf), fun p => (hj f hf.1 p).trans (fock_eq f p)⟩)
    (IsVac.isFinVec ψ θ ε S T hf₀) (vac_ne hf₀) H (fun p q => by simp [h1]) (fun c p => by simp [h2]) hf
    (fun p h g => (hσ.invol _).symm) hm.1 hm.2

theorem lifts_toTarget {X : ProvA} (hP : PairLifts D X) (hθ : IsInfFam θ)
    {S₁ T₁ : D.what₂.Tau → SPar} {MS : DSModel (sgn ε S.V) S₁} {MT : DSModel (sgn false T.V) T₁}
    {κS : SmT MS ≃+ SmT S.M} {κT : SmT MT ≃+ SmT T.M} (hS : ModelTr (starRingEnd ℂ) ε θ MS S.M κS)
    (hT : ModelTr (starRingEnd ℂ) false θ MT T.M κT)
    {aS aT : D.what₂.Tau → ℚ} (hR : ∀ τ, RulePar X (T₁ τ) (S₁ τ) (aT τ) (aS τ)) {χS χT : (AE D)ˣ →* Circle}
    {a : ArrT S T} (ha : a.Is ψ θ ε χS χT) (he : ∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ))
    {f : WO S.V T.V → ℂ} (hf : IsFinVec ψ θ ε S T f) {m : S.MeasDat}
    (hm : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ S.V) m.fd m.ν) :
    LiftsM θ S.M T.M m.ν m.fd (fun p h g => thetaKO a.ω g h (fock ψ θ ε S T f p)) fun p v => a.It p v := by
  have cS : ∀ τ, (Fr.ofModel MS).cart τ = (frSgn ε (Fr.ofModel S.M)).cart τ := fun τ =>
    (hS.cart τ).trans (cart_frSgn ε (Fr.ofModel S.M) τ).symm
  have cT : ∀ τ, (Fr.ofModel MT).cart τ = (Fr.ofModel T.M).cart τ := hT.cart
  have hs := ha.weil.std
  have L := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hs (sgn ε S.V) T.V
  obtain ⟨ω', hW', hω'⟩ := GlobalTheory.T.exists_conj_weilDatum_exchangedPair D ψ _ _ _ _ _ ha.weil
  obtain ⟨j₀, hj₀, hj₀'⟩ := GlobalTheory.T.fockVectors_conjAdjointPullback_bijection D ψ θ hs hθ (sgn ε S.V) T.V (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M)
  obtain ⟨j, hj⟩ := GlobalTheory.T.fockVector_frameChange_same_cartan D ψ θ hs hθ T.V (sgn ε S.V) _ _ _ _ cT cS
  have z : adjO (sgn ε S.V) T.V 0 = 0 := by
    have := L.add 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  have hs₀ : ∀ (c : ℂ) x, j₀.symm (c • x) = starRingEnd ℂ c • j₀.symm x := fun c x =>
    j₀.injective (by rw [hj₀, j₀.apply_symm_apply, j₀.apply_symm_apply, Complex.conj_conj])
  have H := ha.intw
  refine lifts_of_tr hP hθ (Or.inr rfl) hS hT hR (ω₁ := ω') ⟨χT, χS, hW', fun τ => (he τ).symm⟩ (ω := a.ω.swap)
    (pt := fun f p => fock ψ θ ε S T f p) (vac := IsFinVec ψ θ ε S T) (Or.inr rfl) (α := adjO (sgn ε S.V) T.V)
    (fun x => ⟨_, L.invol x⟩) (fun h g f => hω' g h f) (j₀.toEquiv.trans j.toEquiv)
    (fun f hf => ⟨isVacF_congr cT cS (hj₀' f (isVacF_of_finVec hf)).1, fun p => ?_⟩)
    (IsVac.isFinVec ψ θ ε S T ha.vac) (vac_ne ha.vac) (It := fun p => a.It p)
    ⟨by_contra fun h => H.ne (LinearMap.ext fun p => by_contra fun h' => h ⟨p, h'⟩), H.bdd, H.eqK, H.eqg, H.invK, H.invg⟩
    (fun p q => by simp) (fun c p => by simp [hs₀]) hf (fun p h g => by rw [z]; rfl) hm.1 hm.2
  exact (hj _ (hj₀' f (isVacF_of_finVec hf)).1.1 _).trans (((hj₀' f (isVacF_of_finVec hf)).2 p).trans
    (congrArg _ (fock_eq f p)))

theorem hasInfExp_att {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {c : ℚ} (h : HasInfExp D χ τ c)
    (hη : HasInfExp D η τ (1 / 2)) (n : ℕ) : HasInfExp D (Lift.attChr χ η n) τ (att c n) := by
  unfold Lift.attChr att
  split_ifs
  · rw [sub_eq_add_neg]
    exact StepVac.hasInfExp_mul h (StepVac.hasInfExp_inv hη)
  · exact h

theorem haar_of_is {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

theorem haar_cast {N N' : Node D} (h : N = N') {m : N.MeasDat}
    (hm : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν) :
    (m.cast h).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N'.V) (m.cast h).fd (m.cast h).ν := by
  subst h; exact hm

section Grid

open GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts Formalism.L2.DIV Formalism.L2.Indef

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R}

theorem par_vert (hG : G.Is) {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (G.V i j).S = parV D i j := by
  cases i with
  | succ i => exact (hG.spaces.vert i j hi hj).par
  | zero =>
    rw [parV_zero D hj]
    show (row0 R j).S = _
    rcases hj.lt_or_eq with h | rfl
    · rw [← nodeY_eq_chainVertexAtRowZero_of_lt R h]
      show parB (Ptw D) (min j D.R.m) = _
      rw [min_eq_left hj]
    · rw [← nodeX_eq_chainVertexAtRowZero_top R]

theorem par_Xp (hG : G.Is) {j : ℕ} (hj : j ≤ D.R.m) : (G.Xp j).S = parXp D j := by
  cases j with
  | succ j => exact (hG.spaces.X j hj).par
  | zero => exact (hG.spaces.P _ le_rfl).par.trans (parP_m D)

theorem haar_vert (hR : RowBase R) (hG : G.Is) (t : T) {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) :
    (G.meas t i j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.V i j).V) (G.meas t i j).fd (G.meas t i j).ν := by
  cases j with
  | zero => rw [G.meas_zero]; exact haar_of_is (hG.meas.col i hi)
  | succ j =>
    cases i with
    | succ i => exact haar_of_is (hG.meas.vert i j hi hj)
    | zero =>
      show (meas0 R t j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (row0 R (j + 1)).V) (meas0 R t j).fd (meas0 R t j).ν
      unfold meas0
      split_ifs with h
      · refine haar_cast _ ?_
        by_cases h' : j + 1 + 1 < D.R.m
        · exact ⟨(hR.measY t _ h').1.1, (hR.measY t _ h').2⟩
        · have e : j + 1 = D.R.m - 1 := by omega
          have := hR.measY' t
          rw [← e] at this
          exact ⟨this.1.1, this.2⟩
      · exact haar_cast _ ⟨(hR.measX t).1.1, (hR.measX t).2⟩

theorem haar_Xp (hG : G.Is) {j : ℕ} (hj : j ≤ D.R.m) :
    (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
  cases j with
  | zero => exact haar_of_is (hG.meas.P _ le_rfl)
  | succ j => exact haar_of_is (hG.meas.X j hj)

theorem exp_eta (hR : RowBase R) (τ : D.what₂.Tau) : HasInfExp D R.eta τ (1 / 2) :=
  GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hR.lev.eta
    (StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, R.toLevCh.C.isEta.inf⟩) τ

theorem exp_mu (hR : RowBase R) (t : T) {j : ℕ} (hj : j < D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (R.toLevCh.mu t (j + 1)) τ (-(D.hc τ).e ⟨j, hj⟩) := by
  obtain ⟨n, hn, ho⟩ := hR.lev.xi_fin t
  have := StepVac.hasInfExp_mul (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hR.lev.mu0 ⟨j, hj⟩)
    (StepVac.hasInfQ_tau (R.toLevCh.C.isMu0 ⟨j, hj⟩).inf) τ) (StepVac.hasInfExp_of_order hR.inf (hR.lev.xi t) hn ho τ)
  rwa [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this

theorem exp_chi (hG : G.Is) {i : ℕ} (hi : i < D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (G.chi (D.R.m - i)) τ (cen D τ (D.R.m - i)) :=
  GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hG.chars.tie _ (by omega) (by omega))
    (hG.chars.aux _ (by omega) (by omega)).inf τ

theorem isIntwF_of_isItW {V W : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel W S'} {ω : WRep V W}
    {pt : PolF D W.rank V.rank → WO V W → ℂ} {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M}
    (H : IsItW θ M M' ω pt It) : IsIntwF θ M M' ω pt fun p => It p :=
  ⟨by_contra fun h => H.ne (LinearMap.ext fun p => by_contra fun h' => h ⟨p, h'⟩), H.bdd, H.eqK, H.eqg, H.invK, H.invg⟩

theorem cuspAlong_of_pairLifts {X : ProvA} (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X)
    (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X) (hP : PairLifts D X) (hS : Sizes D) (hR : RowBase R) (hG : G.Is) : CuspAlong G := by
  have hθ := hR.inf
  have rp := fun {S S' aS aT} => rulePar_of_pairPar (S := S) (S' := S') (aS := aS) (aT := aT) h3 h4 h5
  refine ⟨fun t i j hi hj f hf => ?_, fun t i j hi hj f hf => ?_, fun i hi f hf => ?_, fun i hi f hf => ?_,
    fun t j hj f hf => ?_⟩
  · obtain ⟨M₁, κ, h⟩ := GlobalTheory.T.exists_negatedSpace_discreteSeriesModelTransport D _ hθ _ _ (G.V (i + 1) j).M
    have a := hG.arrows.X i j hi hj
    exact lifts_toSource hP hθ (Or.inl rfl) h (ModelTr.refl _)
      (fun τ => rp (by rw [par_vert hG hi hj, par_vert hG hi.le hj]; exact GlobalTheory.T.contragredientThetaParams_addBlockArrow D hS i j τ hi hj)) a.weil
      (fun τ => ⟨hasInfExp_att (exp_chi hG hi τ) (exp_eta hR τ) _, hasInfExp_att (exp_chi hG hi τ) (exp_eta hR τ) _⟩)
      a.vac (isIntwF_of_isItW a.intw) (map_add _) (map_smul _) hf (haar_vert hR hG t hi.le hj)
  · have a := hG.arrows.th t i j hi hj
    exact lifts_toSource hP hθ (Or.inl rfl) (ModelTr.refl _) (ModelTr.refl _)
      (fun τ => rp (by rw [par_vert hG hi hj.le, par_vert hG hi hj]; exact GlobalTheory.T.contragredientThetaParams_removeBlockArrow D hS i j τ hi hj)) a.weil
      (fun τ => ⟨hasInfExp_att (exp_mu hR t hj τ) (exp_eta hR τ) _, hasInfExp_att (exp_mu hR t hj τ) (exp_eta hR τ) _⟩)
      a.vac (isIntwF_of_isItW a.intw) (map_add _) (map_smul _) hf (haar_vert hR hG t hi hj)
  · obtain ⟨M₁, κ, h⟩ := exists_conj_neg hθ (G.P (i + 1)).M
    obtain ⟨M₂, κ', h'⟩ := GlobalTheory.T.discrete_series_model_conjugate_transfer D _ hθ _ _ (G.P i).M
    have a := hG.arrows.dn i hi
    exact lifts_toSource hP hθ (Or.inr rfl) h h'
      (fun τ => rp (by rw [(hG.spaces.P _ hi).par, (hG.spaces.P _ hi.le).par]; exact (GlobalTheory.T.contragredientThetaParams_columnArrows D hS i τ hi).1)) a.weil
      (fun τ => ⟨exp_chi hG hi τ, exp_chi hG hi τ⟩) a.vac
      (GlobalTheory.T.realThetaIntertwiner_adjoint_isRealThetaIntertwiner D _ _ _ _ _ _ _ _ _ _ _ _ _ (fun p => G.ItU i p) (fun _ _ => rfl) a.intw (hG.arrows.up i hi))
      (map_add _) (map_smulₛₗ _) hf (haar_of_is (hG.meas.P i hi.le))
  · obtain ⟨M₁, κ, h⟩ := exists_conj_neg hθ (G.P (i + 1)).M
    obtain ⟨M₂, κ', h'⟩ := GlobalTheory.T.discrete_series_model_conjugate_transfer D _ hθ _ _ (G.P i).M
    exact lifts_toTarget hP hθ h h'
      (fun τ => rp (by rw [(hG.spaces.P _ hi).par, (hG.spaces.P _ hi.le).par]; exact (GlobalTheory.T.contragredientThetaParams_columnArrows D hS i τ hi).2))
      (hG.arrows.dn i hi) (fun τ => ⟨exp_chi hG hi τ, exp_chi hG hi τ⟩) hf (haar_of_is (hG.meas.P _ hi))
  · obtain ⟨M₁, κ, h⟩ := GlobalTheory.T.discrete_series_model_conjugate_transfer D _ hθ _ _ (G.Xp j).M
    obtain ⟨M₂, κ', h'⟩ := GlobalTheory.T.discrete_series_model_conjugate_transfer D _ hθ _ _ (G.Xp (j + 1)).M
    exact lifts_toTarget hP hθ h h'
      (fun τ => rp (by rw [par_Xp hG hj, par_Xp hG hj.le]; exact GlobalTheory.T.contragredientThetaParams_lastRowArrows D hS j τ hj))
      (hG.arrows.col t j hj) (fun τ => ⟨exp_mu hR t hj τ, exp_mu hR t hj τ⟩) hf (haar_Xp hG hj.le)

end Grid

theorem liftsCuspidal (X : ProvA) (hX : GlobalTheory.Chain.RealIt.ChosenSeries X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X)
    (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X) (hH : GlobalTheory.Published.HarishChandraModules)
    (hC : GlobalTheory.Published.CuspRapidDecay) (hB : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D)
    (hV : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D) (hL : ∀ D, LieFockAll D) (hK : ∀ D, CompactFockAll D) (hD : ∀ D, FockDense D)
    (hP : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D) (hT : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D)
    (hE : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := by
  intro D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG
  have I : Inputs D X := ⟨hX, hH, hC, hB D, hV D, hL D, hK D, hD D, hP D, hT D, hE D⟩
  exact cuspAlong_of_pairLifts h3 h4 h5
    (GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X I (GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish D X I (GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock D X I (GlobalTheory.T.lowerTowerLifts_vanish_on_fock D X I)))) hS hR hG

end GlobalTheory.PairLift

end
end
