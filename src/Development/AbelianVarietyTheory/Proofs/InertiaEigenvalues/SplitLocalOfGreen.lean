import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsConstituentOfRepIsoLeft
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricBlockTypeVectorCuspidalSupportTameChara
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSplitExactTwistCountProduct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalTwistOfBlockTypeVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterOfPolynomialOfCuspidalLabel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceHarishChandraInducedEqProductCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionLabelOfLabelMapLabel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterParahoricInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleHarishChandraOfStdTraceNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterLabelRootOfHarishChandraConstituent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTameCharacterStatement

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

theorem conv_sum {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (T : G → W →ₗ[ℂ] W) (f : G → W)
    (hT : ∀ g h, T g (f h) = f (g * h)) (a b : MonoidAlgebra ℂ G) :
    (a.coeff.sum fun g c => c • T g (b.coeff.sum fun h d => d • f h)) = (a * b).coeff.sum fun k c => c • f k := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    rw [add_mul, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.sum_add_index', Finsupp.sum_add_index', ha, ha']
      <;> intros <;> simp [add_smul]
  | single g c =>
    rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      rw [mul_add, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.sum_add_index', Finsupp.sum_add_index',
        map_add, smul_add, hb, hb'] <;> intros <;> simp [add_smul]
    | single h d =>
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
        Finsupp.sum_single_index, Finsupp.sum_single_index, map_smul, hT, smul_smul] <;> simp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {r t : ℕ}

def ee (r t : ℕ) : Fin r ⊕ Fin t ≃ Fin (r + t) := stdSum (rfl : r + t = r + t)

theorem ee_inl (i : Fin r) : ee r t (Sum.inl i) = Fin.castAdd t i := by ext; simp [ee]

theorem ee_inr (j : Fin t) : ee r t (Sum.inr j) = Fin.natAdd r j := by ext; simp [ee]

variable (F) in

def dg (r t : ℕ) : GL (Fin r) F →* GL (Fin (r + t)) F := (emb₂ F (ee r t)).comp (MonoidHom.inl _ _)

variable (F) in

def bl (r t : ℕ) : GL (Fin (r + t)) F →* GL (Fin r ⊕ Fin t) F := reix F (ee r t).symm

theorem bl_apply (g : GL (Fin (r + t)) F) (a b : Fin r ⊕ Fin t) : (bl F r t g).val a b = g.val (ee r t a) (ee r t b) := by
  rw [bl, val_reix, Equiv.symm_symm]

theorem eq_of_bl {g g' : GL (Fin (r + t)) F} (H : (bl F r t g).val = (bl F r t g').val) : g = g' := by
  apply Units.ext
  ext a b
  obtain ⟨a, rfl⟩ := (ee r t).surjective a
  obtain ⟨b, rfl⟩ := (ee r t).surjective b
  have := congrFun (congrFun H a) b
  rwa [bl_apply, bl_apply] at this

theorem dg_bl (A : GL (Fin r) F) : (bl F r t (dg F r t A)).val = fromBlocks A.val 0 0 1 := by
  ext a b
  rw [bl_apply]
  have := val_emb₂ F (ee r t) (A, 1)
  simp only [dg, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply]
  rw [this, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

theorem bl_21 (g : GL (Fin (r + t)) F) (i : Fin t) (j : Fin r) :
    (bl F r t g).val.toBlocks₂₁ i j = g.val (Fin.natAdd r i) (Fin.castAdd t j) := by
  simp only [toBlocks₂₁, of_apply, bl_apply, ee_inr, ee_inl]

theorem bl_11 (g : GL (Fin (r + t)) F) (i j : Fin r) :
    (bl F r t g).val.toBlocks₁₁ i j = g.val (Fin.castAdd t i) (Fin.castAdd t j) := by
  simp only [toBlocks₁₁, of_apply, bl_apply, ee_inl]

theorem bl_22 (g : GL (Fin (r + t)) F) :
    (bl F r t g).val.toBlocks₂₂ = g.val.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
  ext i j
  simp only [toBlocks₂₂, of_apply, bl_apply, ee_inr, submatrix_apply]

theorem intM_dg {A : GL (Fin r) F} (hA : IntM A.val) : IntM (dg F r t A).val := by
  intro a b
  obtain ⟨a, rfl⟩ := (ee r t).surjective a
  obtain ⟨b, rfl⟩ := (ee r t).surjective b
  have := congrFun (congrFun (dg_bl (t := t) A) a) b
  rw [bl_apply] at this
  rw [this]
  exact intM_fromBlocks.2 ⟨hA, intM_zero, intM_zero, intM_one⟩ a b

theorem dg_mem_KO {A : GL (Fin r) F} (hA : A ∈ KO F (Fin r)) : dg F r t A ∈ KO F (Fin (r + t)) :=
  GlobalTheory.StepData.mem_KO.2 ⟨intM_dg (GlobalTheory.StepData.mem_KO.1 hA).1,
    by rw [← map_inv]; exact intM_dg (GlobalTheory.StepData.mem_KO.1 hA).2⟩

end GlobalTheory.BlockIdem

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {r t : ℕ}
  {χ : Fˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin (r + t)) F) W}

theorem isBlockVec_add {v w : W} (hv : IsBlockVec χ π v) (hw : IsBlockVec χ π w) : IsBlockVec χ π (v + w) :=
  fun h hh h1 h2 u hu => by rw [map_add, hv h hh h1 h2 u hu, hw h hh h1 h2 u hu, smul_add]

theorem isBlockVec_smul (c : ℂ) {v : W} (hv : IsBlockVec χ π v) : IsBlockVec χ π (c • v) :=
  fun h hh h1 h2 u hu => by rw [map_smul, hv h hh h1 h2 u hu, smul_comm]

theorem isBlockVec_zero : IsBlockVec χ π (0 : W) := fun _ _ _ _ _ _ => by simp

theorem dg_fix {v : W} (hv : IsBlockVec χ π v) {κ : GL (Fin r) F} (hκ : κ ∈ KOne F (Fin r)) :
    π (dg F r t κ) v = v := by
  have key := hv _ (dg_mem_KO (GlobalTheory.StepData.KOne_le_KO hκ))
    (fun i j => by rw [← bl_21, dg_bl, toBlocks_fromBlocks₂₁]; simp)
    (fun i j => by
      rw [← bl_11, dg_bl, toBlocks_fromBlocks₁₁]
      have := (GlobalTheory.StepData.mem_KOne.1 hκ) i j
      rwa [Matrix.sub_apply, Matrix.one_apply] at this)
    1 (by rw [← bl_22, dg_bl, toBlocks_fromBlocks₂₂, det_one, Units.val_one])
  rw [key, map_one, Units.val_one, one_smul]

theorem dg_isBlockVec {v : W} (hv : IsBlockVec χ π v) {κ : GL (Fin r) F} (hκ : κ ∈ KO F (Fin r)) :
    IsBlockVec χ π (π (dg F r t κ) v) := by
  intro h hh h1 h2 u hu
  have hd := dg_mem_KO (t := t) hκ
  have hK : (dg F r t κ)⁻¹ * h * dg F r t κ ∈ KO F (Fin (r + t)) := mul_mem (mul_mem (inv_mem hd) hh) hd
  obtain ⟨A, B, C, D, hE⟩ : ∃ A B C D, (bl F r t h).val = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  have hΦ : (bl F r t ((dg F r t κ)⁻¹ * h * dg F r t κ)).val =
      fromBlocks ((κ⁻¹).val * A * κ.val) ((κ⁻¹).val * B) (C * κ.val) D := by
    rw [← map_inv (dg F r t) κ, map_mul, map_mul, Units.val_mul, Units.val_mul, dg_bl, dg_bl, hE,
      fromBlocks_multiply, fromBlocks_multiply]
    simp [Matrix.mul_assoc]
  have hC : MaxM C := fun i j => by
    rw [show C i j = h.val (Fin.natAdd r i) (Fin.castAdd t j) by rw [← bl_21, hE, toBlocks_fromBlocks₂₁]]
    exact h1 i j
  have hA : MaxM (A - 1) := fun i j => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    rw [show A i j = h.val (Fin.castAdd t i) (Fin.castAdd t j) by rw [← bl_11, hE, toBlocks_fromBlocks₁₁]]
    exact h2 i j
  have key := hv _ hK
    (fun i j => by rw [← bl_21, hΦ, toBlocks_fromBlocks₂₁]; exact hC.mul_intM (intM_of_mem_KO hκ) i j)
    (fun i j => by
      rw [← bl_11, hΦ, toBlocks_fromBlocks₁₁]
      have e : (κ⁻¹).val * A * κ.val - 1 = (κ⁻¹).val * (A - 1) * κ.val := by
        rw [mul_sub, sub_mul, mul_one, Units.inv_mul]
      have := ((((GlobalTheory.StepData.mem_KO.1 hκ).2).mul_maxM hA).mul_intM (intM_of_mem_KO hκ)) i j
      rw [← e, Matrix.sub_apply, Matrix.one_apply] at this
      exact this)
    u (by
      rw [← bl_22, hΦ, toBlocks_fromBlocks₂₂]
      rw [← bl_22, hE, toBlocks_fromBlocks₂₂] at hu
      exact hu)
  have hh' : h * dg F r t κ = dg F r t κ * ((dg F r t κ)⁻¹ * h * dg F r t κ) := by group
  calc π h (π (dg F r t κ) v) = π (dg F r t κ) (π ((dg F r t κ)⁻¹ * h * dg F r t κ) v) := by
        rw [← Module.End.mul_apply, ← map_mul, hh', map_mul, Module.End.mul_apply]
    _ = (χ u : ℂ) • π (dg F r t κ) v := by rw [key, map_smul]

theorem exists_of_isLiftN {p : ℕ} {g : GL (Fin r) (ZMod p)} {h : GL (Fin (r + t)) F} (H : IsLiftN g h) :
    ∃ A : GL (Fin r) F, dg F r t A = h ∧ IsLift g A := by
  set M : Matrix (Fin r) (Fin r) F := fun i j => h.val (Fin.castAdd t i) (Fin.castAdd t j) with hM
  have hΦ : (bl F r t h).val = fromBlocks M 0 0 1 := by
    ext (a | a) (b | b)
    · rw [bl_apply, ee_inl, ee_inl, fromBlocks_apply₁₁]
    · have := H (Fin.castAdd t a) (Fin.natAdd r b)
      rw [dif_neg (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      have hne : Fin.castAdd t a ≠ Fin.natAdd r b := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      simp [bl_apply, ee_inl, ee_inr, this, hne]
    · have := H (Fin.natAdd r a) (Fin.castAdd t b)
      rw [dif_neg (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      have hne : Fin.natAdd r a ≠ Fin.castAdd t b := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      simp [bl_apply, ee_inl, ee_inr, this, hne]
    · have := H (Fin.natAdd r a) (Fin.natAdd r b)
      rw [dif_neg (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      simp [bl_apply, ee_inr, this, Matrix.one_apply]
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (bl F r t h).val.det := (Matrix.isUnit_iff_isUnit_det _).1 (bl F r t h).isUnit
    rwa [hΦ, Matrix.det_fromBlocks_zero₂₁, det_one, mul_one] at h1
  refine ⟨Matrix.nonsingInvUnit M hdet, eq_of_bl ?_, fun a b => ?_⟩
  · rw [dg_bl, hΦ]; rfl
  · have := H (Fin.castAdd t a) (Fin.castAdd t b)
    rw [dif_pos (show ((Fin.castAdd t a : Fin (r + t)) : ℕ) < r ∧ ((Fin.castAdd t b : Fin (r + t)) : ℕ) < r
      from ⟨a.isLt, b.isLt⟩)] at this
    exact this

end GlobalTheory.BlockIdem

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

theorem exists_fixed_blockVec : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (x : W), resCard F = p → z * z = z → IsBlockVec χ π x → NotKilled π z x → ∃ y : W, y ≠ 0 ∧ IsBlockVec χ π y ∧ ∃ ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F, (∀ g, IsLift g (ℓ g)) ∧ (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y := by
  intro F _ _ _ _ p _ r t χ W _ _ π z x hp hz hx hnk
  obtain ⟨ℓ', hℓ', hne⟩ := hnk
  have hA : ∀ g, ∃ A : GL (Fin r) F, dg F r t A = ℓ' g ∧ IsLift g A := fun g => exists_of_isLiftN (hℓ' g)
  choose ℓ hℓ1 hℓ2 using hA
  have hx1 : ∀ h ∈ KOne F (Fin r), (π.comp (dg F r t)) h x = x := fun h hh => dg_fix hx hh
  have hT : ∀ g h, π (dg F r t (ℓ g)) (π (dg F r t (ℓ h)) x) = π (dg F r t (ℓ (g * h))) x := by
    intro g h
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul]
    exact IsLift.apply_eq hp (π := π.comp (dg F r t)) hx1 ((hℓ2 g).mul hp (hℓ2 h)) (hℓ2 (g * h))
  refine ⟨z.coeff.sum fun g c => c • π (dg F r t (ℓ g)) x, ?_, ?_, ℓ, hℓ2, ?_⟩
  · simpa only [hℓ1] using hne
  · rw [Finsupp.sum]
    exact Finset.sum_induction _ _ (fun a b => isBlockVec_add) isBlockVec_zero
      (fun g _ => isBlockVec_smul _ (dg_isBlockVec hx ((hℓ2 g).mem_KO hp)))
  · have := conv_sum (fun g => π (dg F r t (ℓ g))) (fun h => π (dg F r t (ℓ h)) x) hT z z
    rw [hz] at this
    exact this

end GlobalTheory.BlockIdem
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_parahoricBlockVector_of_idempotent : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (x : W), resCard F = p → z * z = z → IsBlockVec χ π x → NotKilled π z x → ∃ y : W, y ≠ 0 ∧ IsBlockVec χ π y ∧ ∃ ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F, (∀ g, IsLift g (ℓ g)) ∧ (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y := by
  atlas_forward_decl GlobalTheory.BlockIdem.exists_fixed_blockVec
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

open GlobalTheory.SmGL.DepthZero ValuativeRel Matrix

theorem factor_eq_det_of_isSubquotient_jac : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n β : Type) [Fintype n] [DecidableEq n] [Fintype β] [LinearOrder β] (c : β → ℕ) (f : (Σ j, Fin (c j)) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n F) V) (ψ : Fˣ →* ℂˣ) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), Nonempty (σ.Equiv (detRep n ψ)) → IsSubquotient (piTensor fun j => (s j).ρ) (jac f σ) → ∀ j, ∀ g ∈ KO F (Fin (c j)), ∀ v, (s j).ρ g v = (ψ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  intro F _ _ _ _ n β _ _ _ _ c f V _ _ σ ψ s ⟨E⟩ hsub j g hg v
  classical

  have hσ : ∀ (h : GL n F) (x : V), σ h x = (ψ (GeneralLinearGroup.det h) : ℂ) • x := by
    intro h x
    apply E.toLinearEquiv.injective
    have h1 := E.toIntertwiningMap.isIntertwining σ (detRep n ψ) h x
    have h2 : E.toLinearEquiv (σ h x) = E.toIntertwiningMap (σ h x) := rfl
    have h3 : E.toLinearEquiv x = E.toIntertwiningMap x := rfl
    rw [h2, h1, map_smul, h3]
    simp [detRep]

  have hval : ∀ {d : Type} [Fintype d] [DecidableEq d] {h : GL d F}, h ∈ KO F d →
      valuation F (GeneralLinearGroup.det h : F) = 1 := by
    intro d _ _ h hh
    obtain ⟨h, rfl⟩ := hh
    have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[F] F) h) : Fˣ) : F) =
        algebraMap 𝒪[F] F (GeneralLinearGroup.det h : 𝒪[F]ˣ) :=
      ((algebraMap 𝒪[F] F).map_det _).symm
    rw [h1]
    exact (Valuation.integer.integers (valuation F)).one_of_isUnit (Units.isUnit _)
  set l : Levi F (fun j => Fin (c j)) := Pi.mulSingle j g with hl
  have hlK : ∀ b, l b ∈ KO F (Fin (c b)) := by
    intro b
    by_cases hb : b = j
    · subst hb; simp [l, hg]
    · simp [l, Pi.mulSingle_eq_of_ne hb, one_mem]
  have hdet : GeneralLinearGroup.det (leviEmb F f l) = GeneralLinearGroup.det g := by
    rw [det_leviEmb, Finset.prod_eq_single j]
    · simp [l]
    · intro b _ hb; simp [l, Pi.mulSingle_eq_of_ne hb]
    · simp
  have hδ : deltaHalf F (fun j => Fin (c j)) l = 1 := by
    rw [deltaHalf_apply]
    exact Finset.prod_eq_one fun b _ => isUnram_absPow F _ _ (hval (hlK b))

  have hjac : ∀ x, jac f σ l x = (ψ (GeneralLinearGroup.det g) : ℂ) • x := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [jac_mk, hδ, inv_one, Units.val_one, one_smul, hσ, hdet, Submodule.Quotient.mk_smul]

  have hT := Model.scalar_of_isSubquotient hsub hjac

  have hnt : ∀ b, Nontrivial (s b).V := fun b => Model.nontrivial_of_isIrreducible (s b).irr
  have hφ : ∀ b, ∃ x : (s b).V, ∃ φ : (s b).V →ₗ[ℂ] ℂ, φ x ≠ 0 := by
    intro b
    obtain ⟨x, hx⟩ := exists_ne (0 : (s b).V)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (s b).V, φ x ≠ 0 := by
      by_contra! h
      exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ x).1 h)
    exact ⟨x, φ, hφ⟩
  choose x φ hxφ using hφ
  let y : ∀ b, (s b).V := Function.update x j v
  have hc : (∏ b ∈ Finset.univ.erase j, φ b (y b)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun b hb => ?_
    rw [show y b = x b from Function.update_of_ne (Finset.ne_of_mem_erase hb) _ _]
    exact hxφ b
  have hyj : y j = v := Function.update_self _ _ _
  have key := contract_piTensor (fun b => (s b).ρ) φ j g (PiTensorProduct.tprod ℂ y)
  rw [hT, map_smul, contract_tprod, hyj, map_smul] at key
  rw [smul_comm] at key
  exact (smul_right_injective _ hc key).symm

end GlobalTheory.LevelType
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetSubquotient_detCharacter_factors_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n β : Type) [Fintype n] [DecidableEq n] [Fintype β] [LinearOrder β] (c : β → ℕ) (f : (Σ j, Fin (c j)) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n F) V) (ψ : Fˣ →* ℂˣ) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), Nonempty (σ.Equiv (detRep n ψ)) → IsSubquotient (piTensor fun j => (s j).ρ) (jac f σ) → ∀ j, ∀ g ∈ KO F (Fin (c j)), ∀ v, (s j).ρ g v = (ψ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  atlas_forward_decl GlobalTheory.LevelType.factor_eq_det_of_isSubquotient_jac
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EmptySecondBlock

section Reindex

variable {R : Type} [CommRing R] {t : ℕ} {c : Bool → ℕ}

def falseEquiv (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c true = 0) : Fin (c false) ≃ Fin t :=
  Equiv.ofBijective (fun i => f ⟨false, i⟩) ⟨fun i j h => by
    have := f.injective h
    simpa using this, fun x => by
    obtain ⟨⟨b, i⟩, rfl⟩ := f.surjective x
    cases b with
    | false => exact ⟨i, rfl⟩
    | true => exact absurd i.2 (by omega)⟩

@[simp] theorem falseEquiv_apply (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c true = 0) (i : Fin (c false)) :
    falseEquiv f hc i = f ⟨false, i⟩ := rfl

theorem leviEmb_mulSingle (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c true = 0) (h : GL (Fin t) R) :
    leviEmb R f (Pi.mulSingle (M := fun j => GL (Fin (c j)) R) false (reix R (falseEquiv f hc).symm h)) = h := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective y
  cases a with
  | true => exact absurd i.2 (by omega)
  | false =>
    cases b with
    | true => exact absurd j.2 (by omega)
    | false =>
      rw [leviEmb_apply_same]
      simp [val_reix]

end Reindex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {c : Bool → ℕ}

theorem deltaHalf_eq_one (hc : c true = 0) (g : Levi k (fun j => Fin (c j))) :
    deltaHalf k (fun j => Fin (c j)) g = 1 := by
  haveI : IsEmpty (Fin (c true)) := by rw [hc]; infer_instance
  rw [deltaHalf_apply, Fintype.prod_bool]
  have h1 : modExp (fun j => Fin (c j)) false = 0 := by
    simp only [modExp, Finset.sum_filter, Fintype.sum_bool]
    simp [hc]
  have h2 : Matrix.GeneralLinearGroup.det (g true) = 1 := by
    ext; simp [Matrix.det_isEmpty]
  have h0 : absPow k 0 = 1 := by
    ext x; simp [val_absPow]
  rw [h1, h2]
  simp [h0]

end GlobalTheory.EmptySecondBlock

end

namespace GlobalTheory.EmptySecondBlock

open GlobalTheory.SmGL.DepthZero

theorem isSubquotient_comp' {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsSubquotient σ π) (ψ : G' →* G) :
    IsSubquotient (σ.comp ψ : Representation ℂ G' W) (π.comp ψ : Representation ℂ G' V) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ψ g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (ψ g)⟩, hf⟩

theorem isSubquotient_of_empty_second_block : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) F) V) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (jac f π) → ∃ φ : Fin r ≃ Fin (c false), IsSubquotient ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) π := by
  intro F _ _ _ _ r c f V _ _ π s hc hsub
  refine ⟨(falseEquiv f hc).symm, ?_⟩
  let ι : GL (Fin r) F →* Levi F (fun j => Fin (c j)) :=
    (MonoidHom.mulSingle (fun j => GL (Fin (c j)) F) false).comp (reix F (falseEquiv f hc).symm)
  have hι : ∀ h, leviEmb F f (ι h) = h := fun h => leviEmb_mulSingle f hc h

  let q : π.IntertwiningMap ((jac f π).comp ι) :=
    ⟨(twKer π (unipRad F f) 1).mkQ, fun h => by
      ext w
      show Submodule.Quotient.mk (π h w) = jac f π (ι h) (Submodule.Quotient.mk w)
      rw [jac_mk, deltaHalf_eq_one hc, inv_one, Units.val_one, one_smul, hι]⟩
  have h3 : IsSubquotient ((jac f π).comp ι) π :=
    IsSubquotient.of_surjective q (Submodule.mkQ_surjective _)
  have h2 := isSubquotient_comp' hsub ι

  haveI := nontrivial_of_irreducible (s true).irr
  obtain ⟨w0, hw0⟩ := exists_ne (0 : (s true).V)
  obtain ⟨ψ0, hψ0⟩ : ∃ ψ0 : Module.Dual ℂ (s true).V, ψ0 w0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff ℂ w0).1 h)
  let ψ : ∀ j, (s j).V →ₗ[ℂ] ℂ := fun j => Bool.rec (motive := fun j => (s j).V →ₗ[ℂ] ℂ) 0 ((ψ0 w0)⁻¹ • ψ0) j
  let K : Representation.IntertwiningMap ((piTensor fun j => (s j).ρ).comp ι : Representation ℂ (GL (Fin r) F) _)
      ((s false).ρ.comp (reix F (falseEquiv f hc).symm) : Representation ℂ (GL (Fin r) F) _) :=
    ⟨contract ψ false, fun h => by
      refine LinearMap.ext fun t => ?_
      exact contract_piTensor (fun j => (s j).ρ) ψ false (reix F (falseEquiv f hc).symm h) t⟩
  have hK : Function.Surjective K := fun y => by
    let x : ∀ j, (s j).V := fun j => Bool.rec (motive := fun j => (s j).V) y w0 j
    refine ⟨PiTensorProduct.tprod ℂ x, ?_⟩
    show contract ψ false (PiTensorProduct.tprod ℂ x) = y
    rw [contract_tprod]
    have : Finset.univ.erase false = {true} := by decide
    rw [this, Finset.prod_singleton]
    show ((ψ0 w0)⁻¹ • ψ0) w0 • y = y
    rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hψ0, one_smul]
  exact (IsSubquotient.of_surjective K hK).trans (h2.trans h3)

end GlobalTheory.EmptySecondBlock
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetSubquotient_firstFactor_of_emptySecondBlock : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) F) V) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (jac f π) → ∃ φ : Fin r ≃ Fin (c false), IsSubquotient ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) π := by
  atlas_forward_decl GlobalTheory.EmptySecondBlock.isSubquotient_of_empty_second_block
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EmptySecondBlockProd

variable {c : Bool → ℕ} {r : ℕ}

def falseEquiv (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0) : Fin (c false) ≃ Fin r :=
  Equiv.ofBijective (fun i => f ⟨false, i⟩) ⟨fun i j h => by
    have := f.injective h
    simpa using this, fun x => by
    obtain ⟨⟨b, i⟩, rfl⟩ := f.surjective x
    cases b with
    | false => exact ⟨i, rfl⟩
    | true => exact absurd i.2 (by omega)⟩

theorem mem_parab_all {R : Type} [CommRing R] (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (g : GL (Fin r) R) : g ∈ parab R f := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  cases a with
  | false => exact absurd hab (by cases b <;> decide)
  | true => exact absurd i.2 (by omega)

theorem eq_one_true {R : Type} [CommRing R] (hc : c true = 0) (h : GL (Fin (c true)) R) : h = 1 :=
  Units.ext (Matrix.ext fun i _ => (Fin.cast hc i).elim0)

def levi {R : Type} [CommRing R] (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0) :
    GL (Fin r) R →* Levi R (fun j => Fin (c j)) :=
  (leviProj R f).comp ((MonoidHom.id _).codRestrict (parab R f) (mem_parab_all f hc))

theorem levi_false {R : Type} [CommRing R] (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (g : GL (Fin r) R) : levi f hc g false = reix R (falseEquiv f hc).symm g :=
  Units.ext (Matrix.ext fun _ _ => rfl)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem deltaHalf_eq_one (hc : c true = 0) (g : Levi F (fun j => Fin (c j))) :
    deltaHalf F (fun j => Fin (c j)) g = 1 := by
  rw [deltaHalf_apply, Fintype.prod_bool]
  have h1 : modExp (fun j => Fin (c j)) false = 0 := by
    simp only [modExp, Finset.sum_filter, Fintype.sum_bool]
    simp [hc]
  have h2 : Matrix.GeneralLinearGroup.det (g true) = 1 := by
    rw [eq_one_true hc (g true), map_one]
  rw [h1, h2]
  simp

end GlobalTheory.EmptySecondBlockProd

namespace GlobalTheory.EmptySecondBlockProd

variable {c : Bool → ℕ} {r : ℕ}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def evOne (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (ρ : Representation ℂ (Levi F (fun j => Fin (c j))) W) :
    (parInd f ρ).IntertwiningMap (ρ.comp (levi f hc)) where
  toLinearMap :=
    { toFun := fun x => x.1.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    show x.1.1 (1 * g) = ρ (levi f hc g) (x.1.1 1)
    have := parInd_law f ρ x ⟨g, mem_parab_all f hc g⟩ 1
    rw [mul_one] at this
    rw [one_mul, this, deltaHalf_eq_one hc, Units.val_one, one_smul]
    rfl

theorem evOne_apply (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (ρ : Representation ℂ (Levi F (fun j => Fin (c j))) W) (x : IndSp f ρ) :
    evOne f hc ρ x = x.1.1 1 := rfl

theorem evOne_injective (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (ρ : Representation ℂ (Levi F (fun j => Fin (c j))) W) : Function.Injective (evOne f hc ρ) := by
  refine (injective_iff_map_eq_zero (evOne f hc ρ)).2 fun x hx => ?_
  rw [evOne_apply] at hx
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  have := parInd_law f ρ x ⟨g, mem_parab_all f hc g⟩ 1
  rw [mul_one] at this
  show x.1.1 g = 0
  rw [this, hx, map_zero, smul_zero]

end GlobalTheory.EmptySecondBlockProd

namespace GlobalTheory.EmptySecondBlockProd

variable {c : Bool → ℕ} {r : ℕ}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_smul_eq (hc : c true = 0) (σ : IrrRep (GL (Fin (c true)) F)) {z : σ.V} (hz : z ≠ 0)
    (y : σ.V) : ∃ a : ℂ, a • z = y := by
  let S : Subrepresentation σ.ρ := ⟨ℂ ∙ z, fun g v hv => by
    rw [eq_one_true hc g, map_one]
    exact hv⟩
  haveI := σ.irr
  rcases eq_bot_or_eq_top S with h | h
  · exfalso
    have : z ∈ S.toSubmodule := Submodule.mem_span_singleton_self z
    rw [h] at this
    exact hz this
  · have : y ∈ S.toSubmodule := by rw [h]; trivial
    exact Submodule.mem_span_singleton.1 this

def tensorMap (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (s : ∀ j, IrrRep (GL (Fin (c j)) F)) (x₀ : ∀ j, (s j).V) :
    Representation.IntertwiningMap
      ((s false).ρ.comp (reix F (falseEquiv f hc).symm) : Representation ℂ (GL (Fin r) F) (s false).V)
      ((piTensor fun j => (s j).ρ).comp (levi f hc)) where
  toLinearMap := (PiTensorProduct.tprod ℂ).toLinearMap x₀ false
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      MultilinearMap.toLinearMap_apply, piTensor_tprod]
    congr 1
    funext j
    cases j with
    | false => simp [levi_false]
    | true => simp [eq_one_true hc (levi f hc g true)]

theorem tensorMap_surjective (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (s : ∀ j, IrrRep (GL (Fin (c j)) F)) (x₀ : ∀ j, (s j).V) (hx : x₀ true ≠ 0) :
    Function.Surjective (tensorMap f hc s x₀) := by
  show Function.Surjective (tensorMap f hc s x₀).toLinearMap
  rw [← LinearMap.range_eq_top]
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, ha⟩ := exists_smul_eq hc (s true) hx (y true)
  refine ⟨a • y false, ?_⟩
  have e1 : y = Function.update (Function.update x₀ false (y false)) true (a • x₀ true) := by
    funext j
    cases j <;> simp [ha]
  show (PiTensorProduct.tprod ℂ).toLinearMap x₀ false (a • y false) = PiTensorProduct.tprod ℂ y
  rw [map_smul, MultilinearMap.toLinearMap_apply]
  conv_rhs => rw [e1, MultilinearMap.map_update_smul]
  congr 2
  funext j
  cases j <;> simp

theorem isSubquotient_multiProd : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r)
    (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → ∃ φ : Fin r ≃ Fin (c false),
      IsSubquotient (multiProd f fun j => (s j).ρ)
        ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) := by
  intro F _ _ _ _ r c f s hc
  haveI := nontrivial_of_irreducible (s true).irr
  obtain ⟨z, hz⟩ := exists_ne (0 : (s true).V)
  let x₀ : ∀ j, (s j).V := fun j => Bool.rec (motive := fun j => (s j).V) 0 z j
  refine ⟨(falseEquiv f hc).symm, ?_⟩
  exact (IsSubquotient.of_injective (evOne f hc _) (evOne_injective f hc _)).trans
    (IsSubquotient.of_surjective (tensorMap f hc s x₀) (tensorMap_surjective f hc s x₀ hz))

end GlobalTheory.EmptySecondBlockProd
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInduction_emptySecond_isSubquotient_first : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → ∃ φ : Fin r ≃ Fin (c false), IsSubquotient (multiProd f fun j => (s j).ρ) ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) := by
  atlas_forward_decl GlobalTheory.EmptySecondBlockProd.isSubquotient_multiProd
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem reix_eq_conj (R : Type) [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ φ' : m ≃ n) : ∃ w : GL n R, ∀ g : GL m R, reix R φ g * w = w * reix R φ' g := by
  let e : n ≃ n := φ'.symm.trans φ
  have h1 : ((e.symm.toPEquiv.toMatrix : Matrix n n R) * e.toPEquiv.toMatrix) = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  have h2 : ((e.toPEquiv.toMatrix : Matrix n n R) * e.symm.toPEquiv.toMatrix) = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  let w : GL n R := ⟨e.symm.toPEquiv.toMatrix, e.toPEquiv.toMatrix, h1, h2⟩
  refine ⟨w, fun g => ?_⟩
  have key : (reix R φ g).val = w.val * (reix R φ' g).val * w⁻¹.val := by
    change _ = e.symm.toPEquiv.toMatrix * _ * e.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [val_reix, e]
  apply Units.ext
  rw [Units.val_mul, key, mul_assoc, Units.inv_mul, mul_one, Units.val_mul]

theorem subquotient_reix (R : Type) [CommRing R] (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ φ' : m ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n R) V) :
    IsSubquotient (σ.comp (reix R φ) : Representation ℂ (GL m R) V) (σ.comp (reix R φ') : Representation ℂ (GL m R) V) := by
  obtain ⟨w, hw⟩ := reix_eq_conj R φ φ'
  refine IsSubquotient.of_surjective ⟨σ w, fun g => ?_⟩ fun v => ⟨σ w⁻¹ v, ?_⟩
  · change σ w * σ (reix R φ' g) = σ (reix R φ g) * σ w
    rw [← map_mul, ← map_mul, hw]
  · change σ w (σ w⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end GlobalTheory.LevelType
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotientRepresentation_two_reindexings : ∀ (R : Type) [CommRing R] (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (φ φ' : m ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n R) V), IsSubquotient (σ.comp (reix R φ) : Representation ℂ (GL m R) V) (σ.comp (reix R φ') : Representation ℂ (GL m R) V) := by
  atlas_forward_decl GlobalTheory.LevelType.subquotient_reix
end

section
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem exists_map_of_typeVec (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (n : Type) [Fintype n] [DecidableEq n] (W : Type) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL n F) W) (ρ : FDRep ℂ (GL n (ZMod p))) (y : W) :
    resCard F = p → TypeVec π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y → ∃ φ : ρ →ₗ[ℂ] W, φ ≠ 0 ∧
      ∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, π h (φ w) = φ (ρ.ρ g w) := by
  intro hp hy
  obtain ⟨h1, ℓ, hℓ, h0⟩ := hy
  let Φ : Module.Dual ℂ ρ → (ρ →ₗ[ℂ] W) := fun μ =>
    ∑ g : GL n (ZMod p), LinearMap.smulRight (μ ∘ₗ ρ.ρ g⁻¹) (π (ℓ g) y)
  have hΦ : ∀ μ w, Φ μ w = ∑ g, μ (ρ.ρ g⁻¹ w) • π (ℓ g) y := by
    intro μ w
    simp [Φ, LinearMap.sum_apply]
  have heq : ∀ μ (g₀ : GL n (ZMod p)) (h : GL n F), IsLift g₀ h → ∀ w, π h (Φ μ w) = Φ μ (ρ.ρ g₀ w) := by
    intro μ g₀ h H w
    rw [hΦ, hΦ, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, IsLift.apply_eq hp h1 (H.mul hp (hℓ g)) (hℓ _)]
    simp [mul_inv_rev, map_mul, Module.End.mul_apply]
  by_contra hne
  have hz : ∀ μ, Φ μ = 0 := fun μ => by
    by_contra e
    exact hne ⟨_, e, heq μ⟩
  apply h0
  let b := Module.finBasis ℂ ρ
  have key : ∑ g, LinearMap.trace ℂ ρ (ρ.ρ g⁻¹) • π (ℓ g) y = 0 := by
    have : ∑ i, Φ (b.coord i) (b i) = 0 := by simp [hz]
    rw [← this]
    simp_rw [hΦ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp_rw [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff, mul_smul]
  rw [← Finset.smul_sum, key, smul_zero]

end GlobalTheory.LevelType
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariantMap_of_levelTypeVector : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (n : Type) [Fintype n] [DecidableEq n] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL n F) W) (ρ : FDRep ℂ (GL n (ZMod p))) (y : W), resCard F = p → TypeVec π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y → ∃ φ : ρ →ₗ[ℂ] W, φ ≠ 0 ∧ ∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, π h (φ w) = φ (ρ.ρ g w) := by
  atlas_forward_decl GlobalTheory.LevelType.exists_map_of_typeVec
end

section
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType GlobalTheory.StepData GlobalTheory.ProdSupport Matrix ValuativeRel
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem exists_parVec_of_map : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (α n : Type) [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (s : ∀ a, Representation ℂ (GL (m a) F) (X a)) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL n (ZMod p)) U) (φ : U →ₗ[ℂ] IndSp e (piTensor s)), resCard F = p → CharLift θ χ → (∀ g ∈ KO F (m a), ∀ v, s a g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) → φ ≠ 0 → (∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, multiProd e s h (φ w) = φ (ρ g w)) → ∃ v : U, v ≠ 0 ∧ ParVec ρ e a θ v := by
  intro F _ _ _ _ p _ α n _ _ _ _ m _ _ e X _ _ s a θ χ U _ _ ρ φ hp hθ hs hφ hint
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  let Λ : U →ₗ[ℂ] (⨂[ℂ] b, X b) :=
    { toFun := fun w => (φ w).1.1 1
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hΛ : ∀ w, Λ w = (φ w).1.1 1 := fun _ => rfl
  have hΛ0 : Λ ≠ 0 := by
    obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
      by_contra! h
      exact hφ (LinearMap.ext h)
    obtain ⟨x, hx⟩ : ∃ x, (φ w).1.1 x ≠ 0 := by
      by_contra! h
      exact hw (Subtype.ext (Subtype.ext (funext h)))
    obtain ⟨q, κ, hκ, rfl⟩ := MultiIrr.exists_parab_mul e x
    obtain ⟨g, hg⟩ := exists_isLift_of_mem_KO hp hκ
    intro h0
    apply hx
    have h1 : (φ w).1.1 κ = 0 := by
      have h2 : Λ (ρ g w) = 0 := by rw [h0]; rfl
      rw [hΛ, ← hint g κ hg w] at h2
      have h3 : (multiProd e s κ (φ w)).1.1 1 = (φ w).1.1 (1 * κ) := rfl
      rwa [h3, one_mul] at h2
    rw [parInd_law, h1, map_zero, smul_zero]
  let H : Subgroup (GL n (ZMod p)) := Subgroup.map (parab (ZMod p) e).subtype
    (⨅ b : {b // b ≠ a}, ((Pi.evalMonoidHom (fun c => GL (m c) (ZMod p)) b.1).comp (leviProj (ZMod p) e)).ker)
  have hH : ∀ x : parab (ZMod p) e, (∀ b, b ≠ a → leviProj (ZMod p) e x b = 1) → (x : GL n (ZMod p)) ∈ H := by
    intro x hx
    refine ⟨x, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_iInf]
    intro b
    exact MonoidHom.mem_ker.2 (hx b.1 b.2)
  have hH' : ∀ y ∈ H, ∃ x : parab (ZMod p) e, (x : GL n (ZMod p)) = y ∧
      ∀ b, b ≠ a → leviProj (ZMod p) e x b = 1 := by
    rintro y ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_iInf] at hx
    exact ⟨x, rfl, fun b hb => MonoidHom.mem_ker.1 (hx ⟨b, hb⟩)⟩
  have key : ∀ y ∈ H, ∀ w, Λ (ρ y w) = ((θ.comp GeneralLinearGroup.det y : ℂˣ) : ℂ) • Λ w := by
    intro y hy w
    obtain ⟨x, rfl, hx⟩ := hH' y hy
    obtain ⟨h, hh, hl⟩ := exists_canon_lift hp (x : GL n (ZMod p))
    have hP : h ∈ parab F e := mem_parab.2 fun i j hij => by
      have h0 := mem_parab.1 x.2 i j hij
      change h.val i j = 0
      rw [hh]
      change ((((x : GL n (ZMod p)) : Matrix n n (ZMod p)) i j).val : F) = 0
      rw [h0]
      simp
    let q : parab F e := ⟨h, hP⟩
    have hq : ∀ b, b ≠ a → leviProj F e q b = 1 := by
      intro b hb
      have h2 := hx b hb
      refine Units.ext (Matrix.ext fun i j => ?_)
      have h3 := congrArg (fun g : GL (m b) (ZMod p) => (g : Matrix (m b) (m b) (ZMod p)) i j) h2
      simp only [leviProj_apply] at h3
      rw [leviProj_apply]
      change h.val _ _ = _
      rw [hh]
      change ((((x : GL n (ZMod p)) : Matrix n n (ZMod p)) _ _).val : F) = _
      rw [h3]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, ZMod.val_one]
    have hqa : leviProj F e q = Pi.mulSingle a (leviProj F e q a) := by
      funext b
      by_cases hb : b = a
      · subst hb; simp
      · rw [Pi.mulSingle_eq_of_ne hb, hq b hb]
    have hKa : leviProj F e q a ∈ KO F (m a) := by
      refine IsLift.mem_KO hp (g := leviProj (ZMod p) e x a) fun i j => ?_
      change valuation F (h.val _ _ - _) < 1
      rw [hh]
      simp
    have hδ : deltaHalf F m (leviProj F e q) = 1 := by
      rw [deltaHalf_apply]
      refine Finset.prod_eq_one fun b _ => isUnram_absPow F _ _ ?_
      by_cases hb : b = a
      · subst hb; exact valuation_det_of_mem_KO hKa
      · rw [hq b hb, map_one]; simp
    have hdet : χ (GeneralLinearGroup.det (leviProj F e q a)) = θ (GeneralLinearGroup.det (x : GL n (ZMod p))) := by
      rw [← CharLift.det hp hθ hl]
      congr 1
      change _ = GeneralLinearGroup.det (q : GL n F)
      rw [det_parab F e q, Finset.prod_eq_single a]
      · intro b _ hb; rw [hq b hb, map_one]
      · simp
    have hv := hint _ h hl w
    rw [hΛ, hΛ, ← hv]
    change (φ w).1.1 (1 * h) = _
    rw [one_mul]
    have hlaw := parInd_law e (piTensor s) (φ w) q 1
    rw [mul_one] at hlaw
    change (φ w).1.1 (q : GL n F) = _
    rw [hlaw, hδ, Units.val_one, one_smul, hqa, piTensor_mulSingle s a _ _ (hs _ hKa), MonoidHom.comp_apply, hdet]
  obtain ⟨v, hv0, hv⟩ := exists_eigen_of_map ρ H (θ.comp GeneralLinearGroup.det) Λ hΛ0 key
  exact ⟨v, hv0, fun x hx => hv _ (hH x hx)⟩

end GlobalTheory.LevelType

end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parabolicTypeVector_of_equivariantMap : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (α n : Type) [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (s : ∀ a, Representation ℂ (GL (m a) F) (X a)) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL n (ZMod p)) U) (φ : U →ₗ[ℂ] IndSp e (piTensor s)), resCard F = p → CharLift θ χ → (∀ g ∈ KO F (m a), ∀ v, s a g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) → φ ≠ 0 → (∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, multiProd e s h (φ w) = φ (ρ g w)) → ∃ v : U, v ≠ 0 ∧ ParVec ρ e a θ v := by
  atlas_forward_decl GlobalTheory.LevelType.exists_parVec_of_map
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LevelType
open Matrix

theorem exists_stdVec_of_parVec : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL (Fin r) (ZMod p)) U) (v : U), Fintype.card (m a) = 1 → v ≠ 0 → ParVec ρ e a θ v → ∃ (c : ℕ) (v' : U), c < r ∧ v' ≠ 0 ∧ StdVec ρ c θ v' := by
  intro p _ r α _ _ m _ _ e a θ U _ _ ρ v hm hv hpar
  obtain ⟨k0⟩ : Nonempty (m a) := Fintype.card_pos_iff.1 (by omega)
  let σ := Tuple.sort (blk e)
  let i₀ := e ⟨a, k0⟩
  have hi₀ : blk e i₀ = a := blk_apply e a k0
  have hmono := Tuple.monotone_sort (blk e)
  have hlt : ∀ i, blk e i < a → σ.symm i < σ.symm i₀ := fun i h => hmono.reflect_lt (by
    show blk e (σ (σ.symm i)) < blk e (σ (σ.symm i₀))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hi₀]; exact h)
  have hgt : ∀ i, a < blk e i → σ.symm i₀ < σ.symm i := fun i h => hmono.reflect_lt (by
    show blk e (σ (σ.symm i₀)) < blk e (σ (σ.symm i))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hi₀]; exact h)
  have hlo : ∀ i, (σ.symm i).val ≤ (σ.symm i₀).val → blk e i ≤ a := fun i h => by
    by_contra h'
    exact absurd h (not_le.2 (Fin.lt_def.1 (hgt i (not_le.1 h'))))
  have hhi : ∀ j, (σ.symm i₀).val ≤ (σ.symm j).val → a ≤ blk e j := fun j h => by
    by_contra h'
    exact absurd h (not_le.2 (Fin.lt_def.1 (hlt j (not_le.1 h'))))
  refine ⟨(σ.symm i₀).val, ρ (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm) v, (σ.symm i₀).isLt, ?_, ?_⟩
  · intro h0
    apply hv
    have := congrArg (ρ (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm)⁻¹) h0
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at this
  · intro x hx
    set y := (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm)⁻¹ * x * GlobalTheory.Parabolic.permGL (ZMod p) σ.symm with hy
    have hyij : ∀ i j, ¬ (blk e i ≤ a ∧ a ≤ blk e j) → y.val i j = if i = j then 1 else 0 := by
      intro i j hij
      have hyv : y.val i j = x.val (σ.symm i) (σ.symm j) := by
        rw [← GlobalTheory.Parabolic.conj_permGL_apply σ.symm y i j, hy]
        congr 2
        group
      rw [hyv, hx _ _ (fun h => hij ⟨hlo i h.1, hhi j h.2⟩)]
      simp
    have hyP : y ∈ parab (ZMod p) e := mem_parab.2 fun i j hji => by
      rw [hyij i j (fun h => absurd (h.1.trans h.2) (not_le.2 hji)), if_neg]
      rintro rfl
      exact lt_irrefl _ hji
    have hlev : ∀ b, b ≠ a → leviProj (ZMod p) e ⟨y, hyP⟩ b = 1 := by
      intro b hb
      refine Units.ext (Matrix.ext fun k l => ?_)
      rw [leviProj_apply, Units.val_one]
      rw [hyij _ _ (fun h => hb (le_antisymm (by simpa using h.1) (by simpa using h.2)))]
      simp [Matrix.one_apply]
    have h1 := hpar ⟨y, hyP⟩ hlev
    change ρ y v = (θ (GeneralLinearGroup.det y) : ℂ) • v at h1
    have hdet : GeneralLinearGroup.det y = GeneralLinearGroup.det x := by
      rw [hy, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    have hxP : x * GlobalTheory.Parabolic.permGL (ZMod p) σ.symm = GlobalTheory.Parabolic.permGL (ZMod p) σ.symm * y := by rw [hy]; group
    rw [← Module.End.mul_apply, ← map_mul, hxP, map_mul, Module.End.mul_apply, h1, hdet, map_smul]

end GlobalTheory.LevelType
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardTypeVector_of_parabolicTypeVector : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL (Fin r) (ZMod p)) U) (v : U), Fintype.card (m a) = 1 → v ≠ 0 → ParVec ρ e a θ v → ∃ (c : ℕ) (v' : U), c < r ∧ v' ≠ 0 ∧ StdVec ρ c θ v' := by
  atlas_forward_decl GlobalTheory.LevelType.exists_stdVec_of_parVec
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LevelType

theorem StdBlock.mul {p r : ℕ} {a : ℕ} {x y : GL (Fin r) (ZMod p)} (hx : StdBlock a x) (hy : StdBlock a y) :
    StdBlock a (x * y) := by
  intro i j hij
  rw [Units.val_mul, Matrix.mul_apply]
  by_cases hi : i.val ≤ a
  · have hj : ¬ a ≤ j.val := fun h => hij ⟨hi, h⟩
    have : ∀ k, y.val k j = if k = j then 1 else 0 := fun k => hy k j (fun h => hj h.2)
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hx i j hij
  · have : ∀ k, x.val i k = if i = k then 1 else 0 := fun k => hx i k (fun h => hi h.1)
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hy i j hij

theorem stdBlock_one {p r : ℕ} (a : ℕ) : StdBlock a (1 : GL (Fin r) (ZMod p)) := by
  intro i j _
  simp [Matrix.one_apply]

theorem stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (r a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (v : ρ), v ≠ 0 → StdVec ρ.ρ a θ v → stdTrace a θ ρ.character ≠ 0 := by
  intro p _ r a θ ρ v hv0 hv
  classical
  set S : Finset (GL (Fin r) (ZMod p)) := Finset.univ.filter (StdBlock a) with hS
  set c : GL (Fin r) (ZMod p) → ℂ := fun x => (((θ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) with hc
  have hcm : ∀ x y, c (x * y) = c x * c y := fun x y => by
    simp [hc, map_mul, mul_inv, Units.val_mul, mul_comm]
  set E : Module.End ℂ ρ := ∑ x ∈ S, c x • ρ.ρ x with hE
  have htr : stdTrace a θ ρ.character = LinearMap.trace ℂ ρ E := by
    rw [hE, map_sum, stdTrace, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp [FDRep.character, hc]
  have himg : ∀ x ∈ S, S.image (x * ·) = S := fun x hx => by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
      exact hx.mul hy
    · rw [Finset.card_image_of_injective _ (mul_right_injective x)]
  have hEE : E * E = (S.card : ℂ) • E := by
    have : ∀ x ∈ S, (c x • ρ.ρ x) * E = E := fun x hx => by
      rw [hE, Finset.mul_sum]
      conv_rhs => rw [← himg x hx]
      rw [Finset.sum_image (fun y _ z _ h => mul_left_cancel h)]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [smul_mul_smul_comm, ← map_mul, hcm x y]
    calc E * E = ∑ x ∈ S, (c x • ρ.ρ x) * E := by rw [hE, Finset.sum_mul]
      _ = ∑ x ∈ S, E := Finset.sum_congr rfl this
      _ = (S.card : ℂ) • E := by rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hEv : E v = (S.card : ℂ) • v := by
    rw [hE, LinearMap.sum_apply, Finset.sum_congr rfl (g := fun _ => v), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro x hx
    rw [LinearMap.smul_apply, hv x (by simpa [hS] using hx), smul_smul]
    simp [hc]
  have hcard : (S.card : ℂ) ≠ 0 := by
    have : (1 : GL (Fin r) (ZMod p)) ∈ S := by simpa [hS] using stdBlock_one (p := p) (r := r) a
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem this)
  set P : Module.End ℂ ρ := (S.card : ℂ)⁻¹ • E with hP
  have hPP : IsIdempotentElem P := by
    rw [IsIdempotentElem, hP, smul_mul_smul_comm, hEE, smul_smul]
    congr 1
    field_simp
  have hPv : P v = v := by
    rw [hP, LinearMap.smul_apply, hEv, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hP0 : P ≠ 0 := fun h => hv0 (by rw [← hPv, h, LinearMap.zero_apply])
  have htP : LinearMap.trace ℂ ρ P ≠ 0 := fun h => hP0 ((LinearMap.IsIdempotentElem.trace_eq_zero_iff hPP).1 h)
  rw [htr]
  have : E = (S.card : ℂ) • P := by rw [hP, smul_smul, mul_inv_cancel₀ hcard, one_smul]
  rw [this, map_smul, smul_eq_mul]
  exact mul_ne_zero hcard htP

end GlobalTheory.LevelType

end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdParabolicTwistedTraceSum_ne_zero_of_vector : ∀ (p : ℕ) [Fact p.Prime] (r a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (v : ρ), v ≠ 0 → StdVec ρ.ρ a θ v → stdTrace a θ ρ.character ≠ 0 := by
  atlas_forward_decl GlobalTheory.LevelType.stdTrace_ne_zero
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LevelType.RestrictionTwo

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

theorem stdBlock_iff (a : ℕ) (y : Gn p (a + 1)) :
    StdBlock a y ↔ InPar a (y : Mt p (a + 1)) ∧ tl a (y : Mt p (a + 1)) = 1 := by
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_⟩
    · rw [h i j (by omega)]
      have : i ≠ j := fun e => by rw [e] at hi; omega
      simp [this]
    · ext i j
      have hi : (i : ℕ) < a + 1 := by omega
      have hj : (j : ℕ) < a + 1 := by omega
      have := h ⟨i, hi⟩ ⟨j, hj⟩ (by first | omega | simp | (simp; omega))
      simp only [tl, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff] at this ⊢
      exact this
  · rintro ⟨h1, h2⟩ i j hij
    have hj : (j : ℕ) < a := by omega
    by_cases hi : (i : ℕ) < a
    · have := congrFun (congrFun h2 ⟨i, hi⟩) ⟨j, hj⟩
      have hi' : (i : ℕ) < a + 1 := by omega
      have hj' : (j : ℕ) < a + 1 := by omega
      simp only [tl, entN, hi', hj', and_self, dif_pos, Matrix.one_apply, Fin.ext_iff] at this
      simp only [Fin.ext_iff]
      exact this
    · have hne : i ≠ j := fun e => by rw [e] at hi; omega
      rw [if_neg hne]
      exact h1 i j hj (by omega)

theorem det_eq_of_stdBlock (a : ℕ) (y : Gn p (a + 1)) (h : StdBlock a y) :
    Matrix.GeneralLinearGroup.det y = Matrix.GeneralLinearGroup.det (toG (br a 1 (y : Mt p (a + 1)))) := by
  obtain ⟨h1, h2⟩ := (stdBlock_iff a y).1 h
  rw [GlobalTheory.GLq.LabelDet.det_par a 1 y h1, h2, GlobalTheory.GLq.LabelDet.toG_one, map_one, one_mul]

theorem br_eq_iff (a : ℕ) (y : Gn p (a + 1)) (h : InPar a (y : Mt p (a + 1))) (x : Gn p 1) :
    br a 1 (y : Mt p (a + 1)) = (x : Mt p 1) ↔ x = toG (br a 1 (y : Mt p (a + 1))) := by
  have hd := GlobalTheory.GLq.LabelDet.det_inPar a 1 _ h
  have h0 : (tl a (y : Mt p (a + 1))).det * (br a 1 (y : Mt p (a + 1))).det ≠ 0 := hd ▸ y.det_ne_zero
  have hu : IsUnit (br a 1 (y : Mt p (a + 1))) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (right_ne_zero_of_mul h0))
  have hv : ((toG (br a 1 (y : Mt p (a + 1))) : Gn p 1) : Mt p 1) = br a 1 (y : Mt p (a + 1)) := by
    unfold toG; rw [dif_pos hu]; exact IsUnit.unit_spec hu
  constructor
  · intro e; apply Units.ext; rw [hv, e]
  · intro e; rw [e, hv]

theorem sum_res_eq (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (α : Gn p (a + 1) → ℂ) :
    ∑ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res a 1 α 1 x =
      ((p : ℂ) ^ a)⁻¹ * stdTrace a θ α := by
  rw [stdTrace, Finset.mul_sum]
  unfold res
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hs : StdBlock a y
  · obtain ⟨h1, h2⟩ := (stdBlock_iff a y).1 hs
    rw [if_pos hs]
    have e : ∀ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * (((p : ℂ) ^ (a * 1))⁻¹ *
        if InPar a (y : Mt p (a + 1)) ∧ tl a (y : Mt p (a + 1)) = ((1 : Gn p a) : Mt p a) ∧
          br a 1 (y : Mt p (a + 1)) = (x : Mt p 1) then α y else 0) =
        if x = toG (br a 1 (y : Mt p (a + 1))) then
          ((p : ℂ) ^ a)⁻¹ * ((((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * α y) else 0 := by
      intro x
      by_cases hx : x = toG (br a 1 (y : Mt p (a + 1)))
      · rw [if_pos ⟨h1, by rw [h2, Units.val_one], (br_eq_iff a y h1 x).2 hx⟩, if_pos hx, det_eq_of_stdBlock a y hs, ← hx,
          MonoidHom.inv_apply, Nat.mul_one]
        ring
      · rw [if_neg (fun h => hx ((br_eq_iff a y h1 x).1 h.2.2)), if_neg hx, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_ite_eq']
    simp
  · rw [if_neg hs, mul_zero]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg, mul_zero, mul_zero]
    rintro ⟨h1, h2, -⟩
    exact hs ((stdBlock_iff a y).2 ⟨h1, by rw [h2, Units.val_one]⟩)

theorem exists_irr_hc_of_stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ)
    (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ), GlobalTheory.GLq.IsIrr α → stdTrace a θ α ≠ 0 →
    ∃ σ : GlobalTheory.GLq.Gn p a → ℂ, GlobalTheory.GLq.IsIrr σ ∧ GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ
      (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 := by
  intro p _ a θ α hα hne
  have key : ∑ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res a 1 α 1 x ≠ 0 := by
    rw [sum_res_eq]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))) hne
  obtain ⟨σ, hσ, h⟩ := (GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv p a α hα θ⁻¹).1 key
  exact ⟨σ, hσ, by simpa only [inv_inv] using h⟩

end GlobalTheory.LevelType.RestrictionTwo
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_detTwist_of_stdTrace_twoBlock : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ), GlobalTheory.GLq.IsIrr α → stdTrace a θ α ≠ 0 → ∃ σ : GlobalTheory.GLq.Gn p a → ℂ, GlobalTheory.GLq.IsIrr σ ∧ GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 := by
  atlas_forward_decl GlobalTheory.LevelType.RestrictionTwo.exists_irr_hc_of_stdTrace_ne_zero
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GLq.DetSplit

open GlobalTheory.GLq Polynomial
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem ip_hc_mono_left (m k n : ℕ) (hn : n = m + k) (ψ : Gn g n → ℂ) (hψ : IsIrr ψ)
    (α A : Gn g m → ℂ) (hα : IsIrr α) (hA : IsChar A) (hαA : ip α A ≠ 0)
    (β : Gn g k → ℂ) (hβ : IsChar β) (h : ip ψ (hc m k α β n) ≠ 0) : ip ψ (hc m k A β n) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hα hA hαA
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_left]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m k n hn).1
  exact GlobalTheory.GLq.DetRoot.ip_add_ne_zero hψ (hc α β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hα) hβ) (hc R β hR hβ) h

theorem ip_hc_mono_right (m k n : ℕ) (hn : n = m + k) (ψ : Gn g n → ℂ) (hψ : IsIrr ψ)
    (α : Gn g m → ℂ) (hα : IsChar α) (β B : Gn g k → ℂ) (hβ : IsIrr β) (hB : IsChar B) (hβB : ip β B ≠ 0)
    (h : ip ψ (hc m k α β n) ≠ 0) : ip ψ (hc m k α B n) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hβ hB hβB
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_right]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m k n hn).1
  exact GlobalTheory.GLq.DetRoot.ip_add_ne_zero hψ (hc α β hα (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβ)) (hc α R hα hR) h

theorem hcL_append_of (K₁ K₂ : List (Pc g)) (h₁ : ∀ q ∈ K₁, IsCusp q.2) (h₂ : ∀ q ∈ K₂, IsCusp q.2)
    (m₁ m₂ n : ℕ) (e₁ : degL K₁ = m₁) (e₂ : degL K₂ = m₂) (hn : n = m₁ + m₂) :
    hcL (K₁ ++ K₂) n = hc m₁ m₂ (hcL K₁ m₁) (hcL K₂ m₂) n := by
  subst e₁ e₂
  exact GlobalTheory.GLq.LabelMul.hcL_append K₁ K₂ (fun q hq => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (h₁ q hq))
    (fun q hq => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (h₂ q hq)) n hn

theorem root_of_constituent : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (u : ZMod p) (f : Polynomial (ZMod p)) (ψ : GlobalTheory.GLq.Gn p r → ℂ) (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ) (σ : GlobalTheory.GLq.Gn p a → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsIrr ψ → GlobalTheory.GLq.IsIrr α → GlobalTheory.GLq.IsIrr β → GlobalTheory.GLq.IsIrr σ → GlobalTheory.GLq.HasLabel L ψ f → GlobalTheory.GLp.IsCharLab L θ u → GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 → GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 → f.IsRoot u := by
  intro p _ L r a c θ u f ψ α β σ hr hψ hα hβ hσ hL hlab hψαβ hασ
  obtain ⟨Q, hQ, hQd, rfl, hQi⟩ := hL
  obtain ⟨Kσ, hKσ, hKσd, hKσi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list p a σ hσ
  obtain ⟨Kβ, hKβ, hKβd, hKβi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list p c β hβ
  have hθI : IsIrr (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    GlobalTheory.GLq.LabelDet.isIrr_hom (θ.comp Matrix.GeneralLinearGroup.det)
  have hθC := GlobalTheory.GLq.LabelMul.isChar_of_isIrr hθI
  have hθcusp : IsCusp (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    ⟨one_pos, hθI, fun a h1 h2 => by omega⟩
  have hQc : ∀ q ∈ Q.map Prod.snd, IsCusp q.2 := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    exact (hQ q' hq').2.1
  have hA := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hQc _ hQd
  have fin : ∀ K' : List (Pc p), (Q.map Prod.snd).Perm K' →
      (⟨1, fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc p) ∈ K' →
      ((Q.map Prod.fst).prod).IsRoot u := by
    intro K' hp hm
    obtain ⟨⟨P, s⟩, hq, hs⟩ := List.mem_map.1 (hp.mem_iff.2 hm)
    dsimp only at hs
    subst hs
    have hP := GlobalTheory.GLq.DetRoot.eq_of_isCuspOf_det L θ u hlab P (hQ _ hq)
    have hdvd : P ∣ (Q.map Prod.fst).prod := List.dvd_prod (List.mem_map.2 ⟨_, hq, rfl⟩)
    exact Polynomial.IsRoot.dvd (by rw [hP]; exact root_X_sub_C.2 rfl) hdvd
  generalize (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) = θd at hθI hθC hθcusp hασ fin
  have h1 := GlobalTheory.GLq.DetRoot.ip_hc_left a α hα σ hσ θd hθC Kσ hKσ hKσd hKσi hασ
  have hT : ∀ q ∈ [(⟨1, θd⟩ : Pc p)], IsCusp q.2 := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hθcusp
  have hTd : degL [(⟨1, θd⟩ : Pc p)] = 1 := by simp [degL]
  have eα : hcL (Kσ ++ [(⟨1, θd⟩ : Pc p)]) (a + 1) = hc a 1 (hcL Kσ a) θd (a + 1) := by
    rw [hcL_append_of Kσ _ hKσ hT a 1 (a + 1) hKσd hTd rfl,
      GlobalTheory.GLq.IpCuspProd.hcL_single 1 θd (GlobalTheory.GLq.IpCuspProd.isClass_of_isChar hθC)]
  rw [← eα] at h1
  have hKα : ∀ q ∈ Kσ ++ [(⟨1, θd⟩ : Pc p)], IsCusp q.2 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hKσ q hq
    · exact hT q hq
  have hKαd : degL (Kσ ++ [(⟨1, θd⟩ : Pc p)]) = a + 1 := by
    rw [GlobalTheory.GLq.LabelMul.degL_append, hKσd, hTd]
  have hAα := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKα _ hKαd
  have h2 := ip_hc_mono_left (a + 1) c r hr ψ hψ α _ hα hAα h1 β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβ) hψαβ
  have h3 := ip_hc_mono_right (a + 1) c r hr ψ hψ _ hAα β (hcL Kβ c) hβ
    (GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKβ _ hKβd) hKβi h2
  rw [← hcL_append_of _ Kβ hKα hKβ (a + 1) c r hKαd hKβd hr] at h3
  have hKall : ∀ q ∈ (Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ, IsCusp q.2 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hKα q hq
    · exact hKβ q hq
  have hKd : degL ((Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ) = r := by
    rw [GlobalTheory.GLq.LabelMul.degL_append, hKαd, hKβd, hr]
  have hB := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKall _ hKd
  have hAB := GlobalTheory.GLq.DetRoot.ip_ne_zero_of_common hψ hA hB hQi h3
  refine fin ((Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ) ?_ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))))
  by_contra hn
  exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp p _ _ _ hQd hKd hQc hKall).1 hn)

end GlobalTheory.GLq.DetSplit
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLabel_root_of_harishChandraConstituent : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (u : ZMod p) (f : Polynomial (ZMod p)) (ψ : GlobalTheory.GLq.Gn p r → ℂ) (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ) (σ : GlobalTheory.GLq.Gn p a → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsIrr ψ → GlobalTheory.GLq.IsIrr α → GlobalTheory.GLq.IsIrr β → GlobalTheory.GLq.IsIrr σ → GlobalTheory.GLq.HasLabel L ψ f → GlobalTheory.GLp.IsCharLab L θ u → GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 → GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 → f.IsRoot u := by
  atlas_forward_decl GlobalTheory.GLq.DetSplit.root_of_constituent
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockTypeSplit

open ValuativeRel Polynomial

section Finite

theorem isRoot_of_parVec {p : ℕ} [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) {r : ℕ} {α : Type} [Fintype α] [LinearOrder α]
    {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α)
    {θ : (ZMod p)ˣ →* ℂˣ} {u : ZMod p} {f : (ZMod p)[X]} (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    (hf : GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f) (hθ : GlobalTheory.GLp.IsCharLab L θ u) (ha : Fintype.card (m a) = 1)
    {v : ρ} (hv : v ≠ 0) (h : ParVec ρ.ρ e a θ v) : f.IsRoot u := by
  obtain ⟨c, v', hc, hv', hs⟩ := GlobalTheory.T.exists_standardTypeVector_of_parabolicTypeVector p r α m e a θ _ ρ.ρ v ha hv h
  have ht := GlobalTheory.T.stdParabolicTwistedTraceSum_ne_zero_of_vector p r c θ ρ v' hv' hs
  have hr : r = c + 1 + (r - c - 1) := by omega
  obtain ⟨A, B, hA, hB, h1, h2⟩ := GlobalTheory.T.exists_irreducible_harishChandra_of_stdTrace_ne_zero p r c (r - c - 1) θ ρ.character hr ⟨ρ, fun _ => rfl⟩ ht
  obtain ⟨σ, hσ, h3⟩ := GlobalTheory.T.exists_irreducible_detTwist_of_stdTrace_twoBlock p c θ A hA h2
  exact GlobalTheory.T.thetaLabel_root_of_harishChandraConstituent p L r c _ θ u f _ A B σ hr ⟨ρ, hρ, fun _ => rfl⟩ hA hB hσ hf hθ h1 h3

end Finite

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isSubquotient_jac_two {a b n V W : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n]
    [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : a ⊕ b ≃ n)
    {π : Representation ℂ (GL n F) V} {τ : Representation ℂ (GL n F) W} (hτ : IsSmooth τ) (h : IsSubquotient π τ) :
    IsSubquotient (jac (two e) π) (jac (two e) τ) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap τ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  refine (IsSubquotient.of_surjective (jacMap (two e) f) fun y => ?_).trans (.of_injective (jacMap (two e) ι) ?_)
  · obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : ι v ∈ twKer τ (unipRad F (two e)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    have hN := GlobalTheory.InertSupp.unipRad_eq_unipOf F (e := two e) (c := fun i => ((blk (two e) i).toNat : ℤ))
      fun i j => by cases blk (two e) i <;> cases blk (two e) j <;> simp
    obtain ⟨T, hT, h2⟩ := GlobalTheory.JacquetExact.exists_finset_of_mem_twKer h1
    obtain ⟨H, hle, hH, hSH⟩ := GlobalTheory.UnipCompact.exists_compact_subgroup F n _ T (hN ▸ hT)
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    exact GlobalTheory.IwahoriInj.twKer_mono (hle.trans hN.ge)
      (GlobalTheory.JacquetExact.mem_twKer_of_compact hτ ι Subtype.val_injective hH (h2 H hSH))

variable {p : ℕ} [Fact p.Prime] {r t : ℕ}

theorem typeVec_first {X : Bool → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]
    (ρ : ∀ j, Representation ℂ (GL (Two (Fin r) (Fin t) j) F) (X j)) (hρ : ∀ j, IsSmooth (ρ j))
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] {τ : Representation ℂ (Levi F (Two (Fin r) (Fin t))) Y}
    (h : IsSubquotient τ (piTensor ρ)) {z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))} {w : Y}
    (hw : TypeVec (n := Fin r) (τ.comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false)) z w) :
    ∃ x, TypeVec (n := Fin r) (ρ false) z x := by
  obtain ⟨y, hy⟩ := TypeVec.up (n := Fin r)
    (π := (piTensor ρ).comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false))
    (isSmooth_comp (isSmooth_piTensor hρ) _ (continuous_mulSingle (A := fun j => GL (Two (Fin r) (Fin t) j) F) false))
    (GlobalTheory.CuspRep.ParLaws.isSubquotient_comp h _) hw
  exact TypeVec.factor (m := Two (Fin r) (Fin t)) ρ false hy

theorem typeVec_iff {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin r) F) W)
    (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (y : W) (h : TypeVec π z y) : IsLevelOne π y ∧ NotKilled π z y := by
  obtain ⟨h1, ℓ, hℓ, h0⟩ := h
  refine ⟨fun h hh => h1 h (GlobalTheory.StepData.mem_KOne.2 fun a b => ?_), ℓ, fun g a b => ?_, h0⟩
  · simpa [Matrix.one_apply] using hh a b
  · rw [dif_pos ⟨a.2, b.2⟩]
    exact hℓ g a b

theorem split_local (hP : GlobalTheory.NRows.Hypotheses₂) (hp : resCard F = p) (L : GlobalTheory.GLq.LabelDatum p) {χ : Fˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) (hχt : IsTame χ) {θ : (ZMod p)ˣ →* ℂˣ} (hθχ : CharLift θ χ) {u : ZMod p}
    (hθ : GlobalTheory.GLp.IsCharLab L θ u) (π : Irr F (r + t)) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    {f : (ZMod p)[X]} (hf : GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f) (hu : ¬ f.IsRoot u) {x : π.V}
    (hx : IsBlockVec χ π.π x) (hxρ : NotKilled π.π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) x) :
    ∃ (π₁ : Irr F r) (π₂ : Irr F t), IsSpherical π₂.π ∧
      Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin t) χ)))) ∧
      ∃ y, IsLevelOne π₁.π y ∧ NotKilled π₁.π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y := by
  classical
  have hBZ := hP.bz
  have hG := hP.geo
  have hM := hP.mp
  obtain ⟨v, hv, hb, ℓ, hℓ, hzv⟩ := GlobalTheory.T.exists_fixed_parahoricBlockVector_of_idempotent F p r t χ _ π.π _ x hp (GlobalTheory.SerOSys.zIdem_idem_central ρ hρ).1 hx hxρ
  obtain ⟨Y, _, _, τ, hτ, hsub, y, hy0, hy, hyρ⟩ :=
    GlobalTheory.T.tame_character_parahoric_invariant hM F p r t χ _ π.π _ v ℓ hp π.smooth π.irr hχt hv hb hℓ hzv
  obtain ⟨s, d, σ, hsupp, hle⟩ := GlobalTheory.T.parahoricBlockTypeVector_cuspidalSupport_tame_characters hBZ hG hP.unl hM F r t χ π v hχ hχt hv hb
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨-, hσ, e₀, hπσ⟩ := hsupp
    obtain ⟨b, fr, gc, S, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG F).1 (hG F).2 e₀
      (two (stdSum (rfl : r + t = r + t))) (fun a => (σ a).smooth)
      (fun a => hasFiniteLength_of_isIrreducible (σ a).irr) hτ
      (hsub.trans (isSubquotient_jac_two _ (isSmooth_parInd _ _) hπσ))
    set A := {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar F α)))} with hA
    obtain ⟨i, hi, hi0⟩ : ∃ i ∈ A, b.1 i true = 0 := by
      by_contra! hc
      have h2 := b.2.2 true
      have h3 : A.ncard ≤ ∑ i, b.1 i true := by
        rw [Set.ncard_eq_toFinset_card' A, Finset.card_eq_sum_ones]
        exact (Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.2 (hc i (Set.mem_toFinset.1 hi))).trans
          (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
      simp only [Fintype.card_fin] at h2
      omega
    obtain ⟨hd, α, hα⟩ := hi
    have hi1 : b.1 i false = 1 := by
      have h1 := b.2.1 i
      simp [Fintype.sum_bool] at h1
      omega
    have hact := GlobalTheory.T.jacquetSubquotient_detCharacter_factors_integral F _ Bool (b.1 i) (fr i) _ (σ i).π _ (S i) hα (hrow i) false
    obtain ⟨w, hw⟩ := typeVec_first (fun j => multiProd (gc j) fun i => (S i j).ρ) (fun j => isSmooth_parInd _ _) hcol hyρ
    obtain ⟨φ, hφ0, hφ⟩ := GlobalTheory.T.exists_equivariantMap_of_levelTypeVector F p (Fin r) _ _ ρ w hp hw
    obtain ⟨v', hv', hpar⟩ := GlobalTheory.T.exists_parabolicTypeVector_of_equivariantMap F p (Fin s) (Fin r) (fun i => Fin (b.1 i false)) (gc false) _
      (fun i => (S i false).ρ) i θ χ _ ρ.ρ φ hp hθχ (fun g hg v => by
        rw [hact g hg v, MonoidHom.mul_apply,
          isUnram_unrChar F α _ (GlobalTheory.StepData.valuation_det_of_mem_KO hg), mul_one]) hφ0 hφ
    exact hu (isRoot_of_parVec L (gc false) i ρ hρ hf hθ (by rw [Fintype.card_fin, hi1]) hv' hpar)
  · obtain ⟨π₁, π₂, ⟨φ⟩, hno⟩ := GlobalTheory.T.irreducible_split_exact_twistCount_product hBZ hG hP.unl F r t χ π s d σ hχ hsupp heq.symm
    have hsph := GlobalTheory.T.spherical_twist_of_blockTypeVector hBZ hG hM F r t χ π π₁ π₂ v hχ hχt hno ⟨φ⟩ hv hb
    refine ⟨π₁, GlobalTheory.SplitPairLift.twistIrr π₂ hχ.inv, hsph, ?_, ?_⟩
    · have h := GlobalTheory.SplitPairLift.twist_twist_inv π₂ χ⁻¹
      rw [inv_inv] at h
      show Nonempty (π.π.Equiv (prod₂ π₁.π (twist (twist π₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
      rw [h]
      exact ⟨φ⟩
    obtain ⟨E⟩ := Exponents.prod₂_equiv_multiProd F r t _ _ π₁.π π₂.π
    let Ψ := φ.trans E
    have hρs : ∀ i, IsSmooth (Exponents.twoRep π₁.π π₂.π i) := fun i => by
      cases i
      · exact π₁.smooth
      · exact π₂.smooth
    have hρl : ∀ i, HasFiniteLength (Exponents.twoRep π₁.π π₂.π i) := fun i => by
      cases i
      · exact hasFiniteLength_of_isIrreducible π₁.irr
      · exact hasFiniteLength_of_isIrreducible π₂.irr
    obtain ⟨b, fr, gc, S, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG F).1 (hG F).2
      (two (stdSum (rfl : r + t = r + t))) (two (stdSum (rfl : r + t = r + t))) hρs hρl hτ
      (hsub.trans (isSubquotient_jac_two _ (isSmooth_parInd _ _)
        (IsSubquotient.of_injective Ψ.toIntertwiningMap Ψ.toLinearEquiv.injective)))
    obtain ⟨z, hz0, hz⟩ := GlobalTheory.T.levi_rep_parabolic_char F Bool (Two (Fin r) (Fin t)) _ (fun j => multiProd (gc j) fun i => (S i j).ρ)
      Y τ true χ y (fun j => isSmooth_parInd _ _) hχ hcol hy0 hy
    obtain ⟨w, hw0, hw⟩ := GlobalTheory.T.exists_levi_block_eigenvector_at_identity F Bool (fun i => Fin (b.1 i true)) (Fin t) (gc true) _
      (fun i => (S i true).ρ) χ z hz0 hz
    have hm : b.1 false true = 0 := by
      by_contra hm
      obtain ⟨z', hz'0, hz'⟩ := GlobalTheory.T.levi_rep_parabolic_char F Bool (fun i => Fin (b.1 i true)) _ (fun i => (S i true).ρ) _
        (piTensor fun i => (S i true).ρ) false χ w (fun i => (S i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw false)
      obtain ⟨α, hα⟩ := GlobalTheory.T.inSupport_mul_unramifiedChar_of_integralEigenvector hBZ hG hM F _ _ (S false true).ρ χ z' (S false true).smooth (S false true).irr hχ
        (Nat.pos_of_ne_zero hm) hz'0 hz'
      exact hno α (GlobalTheory.T.charInCuspidalSupport_of_jacquet_subquotient_factor hBZ hG F r _ π₁.π Bool (b.1 false) (fr false) (S false) true _ π₁.smooth (hrow false) hα)
    have hm' : b.1 true false = 0 := by
      have h1 := b.2.1 false
      have h2 := b.2.2 false
      simp [Fintype.sum_bool] at h1 h2
      omega
    obtain ⟨w₁, hw₁⟩ := typeVec_first (fun j => multiProd (gc j) fun i => (S i j).ρ) (fun j => isSmooth_parInd _ _) hcol hyρ
    obtain ⟨φ₁, h1⟩ := GlobalTheory.T.jacquetSubquotient_firstFactor_of_emptySecondBlock F r (b.1 false) (fr false) _ π₁.π (S false) hm (hrow false)
    obtain ⟨φ₂, h2⟩ := GlobalTheory.T.parabolicInduction_emptySecond_isSubquotient_first F r (fun i => b.1 i false) (gc false) (fun i => S i false) hm'
    obtain ⟨y₁, hy₁⟩ := TypeVec.up π₁.smooth (h2.trans ((GlobalTheory.T.isSubquotientRepresentation_two_reindexings F _ _ φ₂ φ₁ _ (S false false).ρ).trans h1)) hw₁
    exact ⟨y₁, typeVec_iff _ _ _ hy₁⟩

end Local

theorem hasLabelO_of_mul {p : ℕ} [Fact p.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod p)}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod p) C) {r : ℕ} (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    {f : (ZMod p)[X]} (h0 : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ ≠ 0)
    (h : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * Formalism.L2.NT.eSerO O r f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) : Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O ρ f := by
  classical
  rw [GlobalTheory.SerOSys.eSerO_eq_sum, Finset.mul_sum] at h
  obtain ⟨z, hz, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h.trans_ne h0)
  obtain ⟨τ, hτ, rfl, hl⟩ := (GlobalTheory.SerOSys.Zl_finite O r f).mem_toFinset.1 hz
  refine GlobalTheory.SerOSys.hasLabelO_of_repIso O hl (GlobalTheory.SerOSys.repIso_of_zIdem_eq ρ τ hρ hτ ?_)
  by_contra e
  exact hne (GlobalTheory.SerOSys.zIdem_mul_eq_zero ρ τ hρ hτ e)

theorem exists_hasLabel {p : ℕ} [Fact p.Prime] (t : Formalism.CyclotomicNorms.Fbar p →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar p, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar p) (hζ : Formalism.L2.NT.IsGenSys ζ)
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod p) (Formalism.L2.NT.convC t ht ζ hζ))
    (hO : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod p))), 1 ≤ d → CategoryTheory.Simple τ →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod p) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (Formalism.L2.NT.convC t ht ζ hζ) τ (O.lab d τ))
    {r : ℕ} (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ) {f : (ZMod p)[X]}
    (h0 : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ ≠ 0)
    (h : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * Formalism.L2.NT.eSerO O r f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) :
    ∃ L : GlobalTheory.GLq.LabelDatum p, L.teich = t ∧ L.gen = ζ ∧ GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f := by
  let L : GlobalTheory.GLq.LabelDatum p := ⟨t, ht, ζ, fun d hd => (hζ d hd).1,
    fun d e hd he => (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)⟩
  exact ⟨L, rfl, rfl, GlobalTheory.T.classFunctionLabel_of_labelMap_label p L O (fun d V hd hs hc => GlobalTheory.T.isCuspidalCharacterOfPolynomial_of_cuspidalLabel p L t ht hζ rfl d V _ hd
    ((GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField p d V hd hs).2 hc) (hO d V hd hs hc)) (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters p) (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero p) r ρ f hρ
    (hasLabelO_of_mul O ρ hρ h0 h)⟩

open Formalism.BasicNotions GlobalTheory.HeightCounting in

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (Γ : GrpSide D),
    GreenLab Γ → SplitLoc hL D := by
  intro hP hDZ hL D Γ hΓ k v χ hχ u π ρ f ht hlab hser hu ⟨x, hx, hxρ⟩
  have hchi := GlobalTheory.T.label_tame_character hDZ hL D Γ k v χ hχ u ht hlab
  have h0 : idemOf D k ρ ≠ 0 := fun e => by
    obtain ⟨ℓ, -, h⟩ := hxρ
    refine h ?_
    rw [e]
    simp
  obtain ⟨L, h1, h2, hf⟩ := @exists_hasLabel _ ⟨D.host.g_prime k⟩ _ (D.ntypes.teichC_inj k) _ (Γ.ζ_gen k) (Γ.O k) (hΓ k)
    _ ρ hser.1 f h0 (by rw [← Γ.eSer_def]; exact hser.2)
  refine (And.right hchi L h1 h2).elim fun θ hθ => ?_
  exact @split_local _ _ _ _ _ _ ⟨D.host.g_prime k⟩ _ _ hP (And.left hchi) L χ hχ ht θ hθ.1 u hθ.2 π ρ hser.1 f hf hu x hx hxρ

end GlobalTheory.BlockTypeSplit

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_local_of_green : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (Γ : GrpSide D), GreenLab Γ → SplitLoc hL D := by
  atlas_forward_decl GlobalTheory.BlockTypeSplit.main
end
