module

public import Aesop.BuiltinRules
public import GroundTheory.AutomorphicForms.GL2.IsAddHaarMeasureMatrixMeasureFinSq
public import GroundTheory.AutomorphicForms.GL2.GJFELeviMulti
import GroundTheory.AutomorphicForms.GL2.GJLocalZeta
import GroundTheory.AutomorphicForms.LocallyProfinite
import Mathlib.Algebra.Order.Star.Int
import Mathlib.CategoryTheory.Countable
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.UniformSpace.Uniformizable
public import GroundTheory.AutomorphicForms.GL2.GJFELeviConv

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal MeasureTheory Measure Parabolic
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

section Twist

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] {W : Type*} [AddCommGroup W] [Module ℂ W]

def nnrealCharC (χ : G →* ℝ≥0) : G →* ℂ :=
  (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom.comp χ

@[simp]
theorem nnrealCharC_apply (χ : G →* ℝ≥0) (g : G) : nnrealCharC χ g = ((χ g : ℝ) : ℂ) := rfl

theorem nnrealCharC_ne_zero (χ : G →* ℝ≥0) (g : G) : nnrealCharC χ g ≠ 0 := by
  rw [nnrealCharC_apply]
  have h := map_mul_eq_one χ (mul_inv_cancel g)
  exact_mod_cast (left_ne_zero_of_mul_eq_one h)

theorem exists_compact_open_char_eq_one (χ : G →* ℝ≥0) (hχ : Continuous χ) {U : Set G}
    (hU : U ∈ nhds (1 : G)) : ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U ∧
      ∀ k ∈ (K : Set G), χ k = 1 := by
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  exact ⟨K, hKc, hKU, fun k hk => eq_one_of_mem_compact χ hχ hKc hk⟩

variable (χ : G →* ℝ≥0) (hχ : Continuous χ) (ρ : Representation ℂ G W)
include hχ

theorem fixedVectors_twist {K : Subgroup G} (hKc : IsCompact (K : Set G)) :
    fixedVectors (twist (nnrealCharC χ) ρ) K = fixedVectors ρ K := by
  ext v
  simp only [mem_fixedVectors, twist_apply, nnrealCharC_apply]
  refine forall₂_congr fun k hk => ?_
  rw [eq_one_of_mem_compact χ hχ hKc hk]
  simp

theorem isSmooth_twist (hρ : IsSmooth ρ) : IsSmooth (twist (nnrealCharC χ) ρ) := by
  intro v
  obtain ⟨K, hKc, hKU, hK1⟩ := exists_compact_open_char_eq_one χ hχ
    ((hρ v).mem_nhds (one_mem (stabilizerOf ρ v)))
  refine Subgroup.isOpen_mono (H₁ := (K : Subgroup G)) (fun k hk => ?_) K.isOpen
  rw [mem_stabilizerOf, twist_apply, nnrealCharC_apply, hK1 k hk, mem_stabilizerOf.1 (hKU hk)]
  simp

theorem isAdmissible_twist (hρ : IsAdmissible ρ) : IsAdmissible (twist (nnrealCharC χ) ρ) :=
  ⟨isSmooth_twist χ hχ ρ hρ.1, fun K hKc hKo => by
    rw [fixedVectors_twist χ hχ ρ hKc]
    exact hρ.2 K hKc hKo⟩


omit hχ in
def subrepresentationTwistOrderIso :
    Subrepresentation (twist (nnrealCharC χ) ρ) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    have h := S.apply_mem_toSubmodule g hv
    rw [twist_apply] at h
    have := S.toSubmodule.smul_mem (nnrealCharC χ g)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ (nnrealCharC_ne_zero χ g), one_smul] at this⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => by
    rw [twist_apply]
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
  left_inv S := rfl
  right_inv S := rfl
  map_rel_iff' := Iff.rfl

omit hχ in
theorem isIrreducible_twist [ρ.IsIrreducible] :
    (twist (nnrealCharC χ) ρ).IsIrreducible :=
  (OrderIso.isSimpleOrder_iff (subrepresentationTwistOrderIso χ ρ)).2 inferInstance

theorem mem_smoothVectors_dual_twist_iff {ℓ : Module.Dual ℂ W} :
    ℓ ∈ smoothVectors (Representation.dual (twist (nnrealCharC χ) ρ)) ↔
      ℓ ∈ smoothVectors (Representation.dual ρ) := by
  have key : ∀ (ρ₁ ρ₂ : Representation ℂ G W), (∀ g, ∀ x, χ g = 1 → ρ₁ g x = ρ₂ g x) →
      ℓ ∈ smoothVectors (Representation.dual ρ₁) → ℓ ∈ smoothVectors (Representation.dual ρ₂) := by
    intro ρ₁ ρ₂ h12 hℓ
    obtain ⟨K, hKc, hKU, hK1⟩ := exists_compact_open_char_eq_one χ hχ
      (hℓ.mem_nhds (one_mem (stabilizerOf (Representation.dual ρ₁) ℓ)))
    refine Subgroup.isOpen_mono (H₁ := (K : Subgroup G)) (fun k hk => ?_) K.isOpen
    have h1 := mem_stabilizerOf.1 (hKU hk)
    rw [mem_stabilizerOf]
    ext x
    have := LinearMap.congr_fun h1 x
    rw [dual_apply_apply] at this ⊢
    rw [← h12 k⁻¹ x (by rw [map_inv, hK1 k hk, inv_one]), this]
  constructor
  · exact key _ _ fun g x hg => by rw [twist_apply, nnrealCharC_apply, hg]; simp
  · exact key _ _ fun g x hg => by rw [twist_apply, nnrealCharC_apply, hg]; simp

end Twist

section PUnitProd

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def prodPUnitEquiv : (G × PUnit) ≃ₜ* G where
  toFun p := p.1
  invFun g := (g, 1)
  left_inv p := by ext1 <;> rfl
  right_inv g := rfl
  map_mul' p q := rfl
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prodMk continuous_const

end PUnitProd

section LeviBlocks

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem leviEquivPi_symm_apply_entry (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F)
    (a : Set.range β) (k l : Fin (blockSize β a)) :
    (((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) (fiberFin β a k).1
      (fiberFin β a l).1 = ((x a : GL (Fin (blockSize β a)) F) : Matrix _ _ F) k l := by
  rw [← leviEquivPi_apply, ContinuousMulEquiv.apply_symm_apply]

theorem det_leviEquivPi (m : levi F n β) (a : Set.range β) :
    Matrix.det ((leviEquivPi F β m a : GL (Fin (blockSize β a)) F) :
      Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) =
      Matrix.det ((leviBlock F m a : GL (Fiber β a) F) : Matrix (Fiber β a) (Fiber β a) F) := by
  show (Matrix.reindex _ _ ((leviBlock F m a : GL (Fiber β a) F) :
    Matrix (Fiber β a) (Fiber β a) F)).det = _
  exact Matrix.det_reindex_self _ _

theorem ordDet_leviEquivPi (m : levi F n β) (a : Set.range β) :
    ordDet (leviEquivPi F β m a) = blockOrd F a m := by
  rw [ordDet, det_leviEquivPi]
  rfl

theorem detPow_leviEquivPi_symm (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) (s : ℂ) :
    detPow (((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) s =
      ∏ a, detPow (x a) s := by
  rw [detPow_eq_qs_zpow, ordDet_eq_sum_blockOrd]
  have : ∀ a, blockOrd F a ((leviEquivPi F β).symm x) = ordDet (x a) := fun a => by
    rw [← ordDet_leviEquivPi, ContinuousMulEquiv.apply_symm_apply]
  simp_rw [this, detPow_eq_qs_zpow]
  classical
  induction (Finset.univ : Finset (Set.range β)) using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (qs_ne_zero s), ih]

theorem leviModulus_leviEquivPi_symm (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) :
    leviModulus β ((leviEquivPi F β).symm x) = ∏ a, detModulusPow (x a) := by
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [detModulusPow, ← det_leviEquivPi, ContinuousMulEquiv.apply_symm_apply]

theorem leviEquivPi_symm_mulSingle (a : Set.range β) :
    (leviEquivPi F β).symm (Pi.mulSingle a (centralUnif F (blockSize β a))) = blockUnif F a := by
  classical
  apply (leviEquivPi F β).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  funext b
  ext k l
  rw [leviEquivPi_apply]
  simp only [blockUnif, Cartan.diagPow, Matrix.diagonal_apply]
  have hk : blockOf β (fiberFin β b k).1 = b := (fiberFin β b k).2
  have hkl : (fiberFin β b k).1 = (fiberFin β b l).1 ↔ k = l := by
    rw [← Subtype.ext_iff, (fiberFin β b).injective.eq_iff]
  by_cases hb : b = a
  · subst hb
    rw [Pi.mulSingle_eq_same, coe_centralUnif]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, blockIndicator, hk, ite_true,
      zpow_one, hkl]
    split_ifs <;> simp
  · rw [Pi.mulSingle_eq_of_ne hb]
    simp only [Units.val_one, Matrix.one_apply, blockIndicator, hk, ite_eq_right hb, zpow_zero, hkl]


variable (β) in
def leviIdx (a : Set.range β) (k l : Fin (blockSize β a)) : LeviIndex n β :=
  ⟨((fiberFin β a k).1, (fiberFin β a l).1), by
    have hk := congrArg Subtype.val (fiberFin β a k).2
    have hl := congrArg Subtype.val (fiberFin β a l).2
    exact hk.trans hl.symm⟩

theorem leviIdx_bijective :
    Function.Bijective fun p : (Σ a : Set.range β, Fin (blockSize β a) × Fin (blockSize β a)) =>
      leviIdx β p.1 p.2.1 p.2.2 := by
  constructor
  · rintro ⟨a, k, l⟩ ⟨a', k', l'⟩ h
    have h1 : (fiberFin β a k).1 = (fiberFin β a' k').1 :=
      congrArg (fun ij : LeviIndex n β => ij.1.1) h
    have h2 : (fiberFin β a l).1 = (fiberFin β a' l').1 :=
      congrArg (fun ij : LeviIndex n β => ij.1.2) h
    have ha : a = a' := (fiberFin β a k).2.symm.trans (by rw [h1]; exact (fiberFin β a' k').2)
    subst ha
    have hk : k = k' := (fiberFin β a).injective (Subtype.ext h1)
    have hl : l = l' := (fiberFin β a).injective (Subtype.ext h2)
    subst hk hl
    rfl
  · rintro ⟨⟨i, j⟩, hij⟩
    have hj : blockOf β j = blockOf β i := Subtype.ext hij.symm
    refine ⟨⟨blockOf β i, ((fiberFin β (blockOf β i)).symm ⟨i, rfl⟩,
      (fiberFin β (blockOf β i)).symm ⟨j, hj⟩)⟩, ?_⟩
    simp only [leviIdx, Equiv.apply_symm_apply]

theorem prod_leviIndex {M : Type*} [CommMonoid M] (f : LeviIndex n β → M) :
    ∏ ij, f ij = ∏ a : Set.range β, ∏ p : Fin (blockSize β a) × Fin (blockSize β a),
      f (leviIdx β a p.1 p.2) := by
  rw [← Fintype.prod_equiv (Equiv.ofBijective _ leviIdx_bijective) (fun p => f (leviIdx β p.1 p.2.1 p.2.2)) f
    (fun p => rfl), Fintype.prod_sigma]


variable (β) in
def blockTensor (φ : LeviIndex n β → F → ℂ) (a : Set.range β)
    (X : Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) : ℂ :=
  ∏ p : Fin (blockSize β a) × Fin (blockSize β a), φ (leviIdx β a p.1 p.2) (X p.1 p.2)

theorem leviTensor_leviEquivPi_symm (φ : LeviIndex n β → F → ℂ)
    (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) :
    leviTensor β φ ((((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) : Matrix _ _ F) =
      ∏ a, blockTensor β φ a (x a : Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) := by
  rw [leviTensor, prod_leviIndex]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun p _ => ?_
  simp only [leviIdx]
  rw [leviEquivPi_symm_apply_entry]

theorem isSchwartzBruhat_blockTensor {φ : LeviIndex n β → F → ℂ}
    (hφ : ∀ ij, φ ij ∈ LocalField.schwartzBruhat F) (a : Set.range β) :
    IsSchwartzBruhat (blockTensor β φ a) := by
  rw [GJMatrix.isSchwartzBruhat_iff_comp_symm]
  have : blockTensor β φ a ∘ (GJMatrix.matrixCoordHomeomorph (Fin (blockSize β a)) F).symm =
      GJMatrix.localTensor fun p : Fin (blockSize β a) × Fin (blockSize β a) =>
        φ (leviIdx β a p.1 p.2) := by
    funext z
    rfl
  rw [this]
  exact GJMatrix.localTensor_mem fun p => hφ _

variable [MeasurableSpace F] [BorelSpace F]

theorem localMatrixFourier_entryTensor (ψ : AddChar F Circle) {m : ℕ}
    (g : Fin m × Fin m → F → ℂ) (Y : Matrix (Fin m) (Fin m) F) :
    GJMatrix.localMatrixFourier ψ (fun X => ∏ p : Fin m × Fin m, g p (X p.1 p.2)) Y =
      ∏ p : Fin m × Fin m,
        LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g p) (Y p.2 p.1) := by
  rw [GJMatrix.localMatrixFourier_eq]
  have : (fun X : Matrix (Fin m) (Fin m) F => ∏ p : Fin m × Fin m, g p (X p.1 p.2)) ∘
      (GJMatrix.matrixCoordHomeomorph (Fin m) F).symm = GJMatrix.localTensor g := by
    funext z
    rfl
  rw [this, GJMatrix.localFourierPi_localTensor]
  rfl

theorem leviTensorHat_leviEquivPi_symm (ψ : AddChar F Circle) (φ : LeviIndex n β → F → ℂ)
    (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) :
    leviTensorHat β ψ φ ((((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) : Matrix _ _ F) =
      ∏ a, GJMatrix.localMatrixFourier ψ (blockTensor β φ a)
        (x a : Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) := by
  rw [leviTensorHat, prod_leviIndex]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [show blockTensor β φ a = fun X => ∏ p : Fin (blockSize β a) × Fin (blockSize β a),
    φ (leviIdx β a p.1 p.2) (X p.1 p.2) from rfl, localMatrixFourier_entryTensor]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp only [leviIdx]
  rw [leviEquivPi_symm_apply_entry]

end LeviBlocks

section Main

universe uF u w

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type u} [LinearOrder α] {β : Fin n → α}
  {W : Type w} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem nontrivial_of_isIrreducible {G : Type*} [Group G] (ρ : Representation ℂ G W)
    [ρ.IsIrreducible] : Nontrivial W := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Subsingleton (Subrepresentation ρ) := ⟨fun S T => by
    cases S; cases T; congr 1; exact Subsingleton.elim _ _⟩
  exact bot_ne_top (Subsingleton.elim (⊥ : Subrepresentation ρ) ⊤)

theorem detPow_add (g : GL (Fin n) F) (a b : ℂ) : detPow g (a + b) = detPow g a * detPow g b := by
  rw [detPow_eq_qs_zpow, detPow_eq_qs_zpow, detPow_eq_qs_zpow, qs_add, mul_zpow]

theorem borelSpace_GL_units (m : ℕ) : BorelSpace (GL (Fin m) F) := by
  refine ⟨?_⟩
  have hM : (GJMatrix.measurableSpace_matrix : MeasurableSpace (Matrix (Fin m) (Fin m) F)) =
      _root_.borel (Matrix (Fin m) (Fin m) F) := BorelSpace.measurable_eq
  show MeasurableSpace.comap Units.val _ = _
  rw [hM, ← borel_comap, ← (Measures.isOpenEmbedding_val F m).isEmbedding.eq_induced]

end Main

end GodementJacquet

end GroundTheory.Automorphic
