import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleImageNeZeroOfBlockTypeVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientCommonEigenvector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardLeUnramifiedTwistsCuspidalSupportJacquet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSupercuspidalSupportOfTorusJacquetEigenform
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharInCuspidalSupportOfJacquetSubquotientFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlock

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetModule_image_ne_zero_of_blockTypeVector : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V), IsSmooth π → π.IsIrreducible → IsTame χ → v ≠ 0 → IsBlockVec χ π v → (Submodule.Quotient.mk v : Jacquet π (unipRad k (two (stdSum (rfl : r + t = r + t))))) ≠ 0 ∧ ∀ g ∈ KO k (Fin t), jac (two (stdSum (rfl : r + t = r + t))) π (Pi.mulSingle true g) (Submodule.Quotient.mk v) = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • Submodule.Quotient.mk v := by
  first | exact @GlobalTheory.JacBlockTwo.jacquet_ne_zero_of_isBlockVec_two | exact GlobalTheory.JacBlockTwo.jacquet_ne_zero_of_isBlockVec_two | (intros; apply GlobalTheory.JacBlockTwo.jacquet_ne_zero_of_isBlockVec_two <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_subquotient_common_eigenvector : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (S : Set G) (θ : G → ℂ) (x : V), x ≠ 0 → (∀ g ∈ S, ρ g x = θ g • x) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y), τ.IsIrreducible ∧ IsSubquotient τ ρ ∧ ∃ y : Y, y ≠ 0 ∧ ∀ g ∈ S, τ g y = θ g • y := by
  first | exact @GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen | exact GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen | (intros; apply GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen <;> assumption)
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.AugmentationEigenvector

section General

variable {K X Y : Type} [Group K] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

def aug (ψ : K →* ℂˣ) : MonoidAlgebra ℂ K →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ K ((Units.coeHom ℂ).comp ψ)

theorem aug_single (ψ : K →* ℂˣ) (g : K) (r : ℂ) :
    aug ψ (MonoidAlgebra.single g r) = r * (ψ g : ℂ) := by
  simp [aug]

theorem act_eigen (σ : Representation ℂ K X) (ψ : K →* ℂˣ) (y : X)
    (hy : ∀ g, σ g y = (ψ g : ℂ) • y) (c : MonoidAlgebra ℂ K) :
    σ.asAlgebraHom c y = aug ψ c • y := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, ha, hb, add_smul]
  | single g r => rw [aug_single, Representation.asAlgebraHom_single, LinearMap.smul_apply, hy, smul_smul]

theorem act_comm (σ : Representation ℂ K X) (τ : Representation ℂ K Y) (f : X →ₗ[ℂ] Y)
    (hf : ∀ g x, f (σ g x) = τ g (f x)) (c : MonoidAlgebra ℂ K) (x : X) :
    f (σ.asAlgebraHom c x) = τ.asAlgebraHom c (f x) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single g r => simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul, hf]

theorem exists_kill [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (σ : Representation ℂ K X) (ψ : K →* ℂˣ) (hσ : IsSmooth σ) (hψ : IsSmoothChar ψ)
    (h0 : ∀ z, (∀ g, σ g z = (ψ g : ℂ) • z) → z = 0) (z : X) :
    ∃ c, aug ψ c ≠ 0 ∧ σ.asAlgebraHom c z = 0 := by
  classical
  let π := twist σ ψ⁻¹
  have hπ : IsSmooth π := isSmooth_twist hσ hψ.inv
  have hlc : IsLocallyConstant fun g : K => π g z := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have h : {g : K | π g z = z} ∈ nhds ((fun y => x⁻¹ * y) x) :=
      IsOpen.mem_nhds (hπ z) (by simp)
    filter_upwards [(continuous_const_mul x⁻¹).continuousAt.preimage_mem_nhds h] with y hy
    have hy' : π (x⁻¹ * y) z = z := hy
    calc π y z = π x (π (x⁻¹ * y) z) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = π x z := by rw [hy']
  have hfin := hlc.range_finite
  let O : Finset X := hfin.toFinset
  have hO : ∀ w, w ∈ O ↔ ∃ g, π g z = w := fun w => by simp [O]
  have hmem : ∀ g, ∀ w ∈ O, π g w ∈ O := fun g w hw => by
    obtain ⟨x, rfl⟩ := (hO w).1 hw
    exact (hO _).2 ⟨g * x, by rw [map_mul, Module.End.mul_apply]⟩
  have hinv : ∀ g, π g (∑ w ∈ O, w) = ∑ w ∈ O, w := fun g => by
    rw [map_sum]
    refine Finset.sum_nbij' (fun w => π g w) (fun w => π g⁻¹ w) (hmem g) (hmem g⁻¹)
      (fun w _ => ?_) (fun w _ => ?_) (fun _ _ => rfl)
    · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hz : ∑ w ∈ O, w = 0 := h0 _ fun g => by
    have h1 := hinv g
    have h2 : π g (∑ w ∈ O, w) = ((ψ g)⁻¹ : ℂˣ).val • σ g (∑ w ∈ O, w) := rfl
    rw [h2] at h1
    conv_rhs => rw [← h1]
    rw [smul_smul, Units.mul_inv, one_smul]
  choose s hs using fun w : O => (hO w).1 w.2
  refine ⟨∑ w : O, MonoidAlgebra.single (s w) ((ψ (s w))⁻¹ : ℂˣ).val, ?_, ?_⟩
  · rw [map_sum]
    simp only [aug_single, Units.inv_mul]
    have : O.Nonempty := ⟨z, (hO z).2 ⟨1, by simp⟩⟩
    simpa using this.ne_empty
  · rw [map_sum, LinearMap.sum_apply, ← hz, ← Finset.sum_coe_sort O]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
    exact hs w

end General

section Tensor

variable {β : Type} [DecidableEq β] {Γ X : β → Type} [∀ j, Group (Γ j)] [∀ j, AddCommGroup (X j)]
  [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (Γ j) (X j)) (a : β) {K : Type} [Group K]
  (i : K →* Γ a)

def viaFactor : Representation ℂ K (⨂[ℂ] j, X j) :=
  (piTensor ρ).comp ((MonoidHom.mulSingle Γ a).comp i)

theorem viaFactor_tprod (x : ∀ j, X j) (g : K) (z : X a) :
    viaFactor ρ a i g (PiTensorProduct.tprod ℂ (Function.update x a z)) =
      PiTensorProduct.tprod ℂ (Function.update x a (ρ a (i g) z)) := by
  show piTensor ρ (Pi.mulSingle a (i g)) _ = _
  rw [piTensor_tprod]
  congr 1
  funext j
  by_cases h : j = a
  · subst h; simp
  · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]

theorem viaFactor_alg (x : ∀ j, X j) (c : MonoidAlgebra ℂ K) (z : X a) :
    (viaFactor ρ a i).asAlgebraHom c (PiTensorProduct.tprod ℂ (Function.update x a z)) =
      PiTensorProduct.tprod ℂ
        (Function.update x a (Representation.asAlgebraHom ((ρ a).comp i) c z)) :=
  (act_comm ((ρ a).comp i) (viaFactor ρ a i) ((PiTensorProduct.tprod ℂ).toLinearMap x a)
    (fun g z => (viaFactor_tprod ρ a i x g z).symm) c z).symm

theorem exists_kill_tensor (ψ : K →* ℂˣ)
    (h : ∀ z, ∃ c, aug ψ c ≠ 0 ∧ Representation.asAlgebraHom ((ρ a).comp i) c z = 0)
    (v : ⨂[ℂ] j, X j) (b : MonoidAlgebra ℂ K) :
    ∃ c, aug ψ c ≠ 0 ∧
      (viaFactor ρ a i).asAlgebraHom c ((viaFactor ρ a i).asAlgebraHom b v) = 0 := by
  induction v using PiTensorProduct.induction_on generalizing b with
  | smul_tprod r x =>
    obtain ⟨c, hc, hc'⟩ := h (Representation.asAlgebraHom ((ρ a).comp i) b (x a))
    refine ⟨c, hc, ?_⟩
    rw [← Function.update_eq_self a x, map_smul, map_smul, viaFactor_alg, viaFactor_alg, hc',
      MultilinearMap.map_update_zero, smul_zero]
  | add v w hv hw =>
    obtain ⟨c, hc, hc'⟩ := hv b
    obtain ⟨d, hd, hd'⟩ := hw (c * b)
    refine ⟨d * c, by rw [map_mul]; exact mul_ne_zero hd hc, ?_⟩
    rw [map_mul, Module.End.mul_apply] at hd'
    rw [map_mul, Module.End.mul_apply, map_add, map_add, hc', zero_add, hd']

end Tensor

theorem exists_eigenvector (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type)
    [(j : β) → Fintype (m j)] [(j : β) → DecidableEq (m j)] (X : β → Type)
    [(j : β) → AddCommGroup (X j)] [(j : β) → Module ℂ (X j)]
    (ρ : (j : β) → Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y)
    (hρ : ∀ j, IsSmooth (ρ j)) (hχ : IsSmoothChar χ) (hs : IsSubquotient τ (piTensor ρ))
    (hy : y ≠ 0)
    (he : ∀ g ∈ KO k (m a),
      τ (Pi.mulSingle a g) y = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • y) :
    ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a),
      ρ a g z = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • z := by
  by_contra hne
  haveI : CompactSpace (KO k (m a)) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  let i := (KO k (m a)).subtype
  let ψ : KO k (m a) →* ℂˣ := χ.comp (Matrix.GeneralLinearGroup.det.comp i)
  have hψ : IsSmoothChar ψ :=
    hχ.comp _ (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  have h1 := exists_kill ((ρ a).comp i) ψ (isSmooth_comp (hρ a) i continuous_subtype_val) hψ
    fun z hz => by
      by_contra h
      exact hne ⟨z, h, fun g hg => hz ⟨g, hg⟩⟩
  obtain ⟨S, f, hf⟩ := hs
  obtain ⟨v, rfl⟩ := hf y
  obtain ⟨c, hc, hc'⟩ := exists_kill_tensor ρ a i ψ h1 v.1 1
  rw [map_one, Module.End.one_apply] at hc'
  let e : KO k (m a) →* Levi k m := (MonoidHom.mulSingle (fun j => GL (m j) k) a).comp i
  have h2 := act_comm (S.toRepresentation.comp e) (viaFactor ρ a i) S.toSubmodule.subtype
    (fun _ _ => rfl) c v
  have h3 : Representation.asAlgebraHom (S.toRepresentation.comp e) c v = 0 :=
    Subtype.ext (h2.trans hc')
  have h4 := act_comm (S.toRepresentation.comp e) (τ.comp e) f.toLinearMap
    (fun g x => f.isIntertwining _ _ (e g) x) c v
  rw [h3, map_zero, act_eigen (τ.comp e) ψ (f.toLinearMap v) (fun g => he g.1 g.2)] at h4
  exact hy ((smul_eq_zero.1 h4.symm).resolve_left hc)

end GlobalTheory.AugmentationEigenvector
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EigenFactor

section Avg

variable {H W W' : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def avgOp (σ : Representation ℂ H W) (θ : H →* ℂˣ) (U : Subgroup H) [Fintype (H ⧸ U)] : W →ₗ[ℂ] W :=
  ∑ q : H ⧸ U, (((θ q.out)⁻¹ : ℂˣ) : ℂ) • σ q.out

end Avg

section Tensor

variable {β : Type} [Fintype β] [DecidableEq β] {Γ X : β → Type} [∀ j, Group (Γ j)] [∀ j, AddCommGroup (X j)]
  [∀ j, Module ℂ (X j)]

end Tensor

theorem exists_eig_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type) [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] (X : β → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y), (∀ j, IsSmooth (ρ j)) → IsSmoothChar χ → IsSubquotient τ (piTensor ρ) → y ≠ 0 → (∀ g ∈ KO k (m a), τ (Pi.mulSingle a g) y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a), ρ a g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z := by
  first
  | exact @_root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector
  | exact _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector
  | (apply _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> assumption)
  | (intros; apply _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector ..)

end GlobalTheory.EigenFactor
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_rep_parabolic_char : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type) [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] (X : β → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y), (∀ j, IsSmooth (ρ j)) → IsSmoothChar χ → IsSubquotient τ (piTensor ρ) → y ≠ 0 → (∀ g ∈ KO k (m a), τ (Pi.mulSingle a g) y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a), ρ a g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z := by
  atlas_forward_decl GlobalTheory.EigenFactor.exists_eig_factor
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open Matrix ValuativeRel

noncomputable section

namespace GlobalTheory.SphBlock

theorem exists_eigen_at_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ) (x : IndSp e (piTensor σ)), x ≠ 0 → (∀ g ∈ KO k n, multiProd e σ g x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → ∃ w : PiTensorProduct ℂ X, w ≠ 0 ∧ ∀ a, ∀ h ∈ KO k (m a), piTensor σ (Pi.mulSingle a h) w = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • w := by
  intro k _ _ _ _ α _ _ m _ _ n _ _ e X _ _ σ χ x hx hK
  classical
  set f := x.1.1 with hf
  have hval : ∀ {d : Type} [Fintype d] [DecidableEq d] {g : GL d k}, g ∈ KO k d →
      valuation k (GeneralLinearGroup.det g : k) = 1 := by
    intro d _ _ g hg
    obtain ⟨g, rfl⟩ := hg
    have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
        algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
      ((algebraMap 𝒪[k] k).map_det _).symm
    rw [h1]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
  have hfK : ∀ κ ∈ KO k n, f κ = (χ (GeneralLinearGroup.det κ) : ℂ) • f 1 := by
    intro κ hκ
    have h := congrArg (fun y : IndSp e (piTensor σ) => y.1.1 1) (hK κ hκ)
    have h2 : (multiProd e σ κ x).1.1 1 = f (1 * κ) := parInd_apply e (piTensor σ) κ 1 x
    rw [h2, one_mul] at h
    exact h
  refine ⟨f 1, ?_, ?_⟩
  · intro h0
    apply hx
    have hall : ∀ g, f g = 0 := by
      intro g
      obtain ⟨u, l, κ, hκ, rfl⟩ := UnitInd.exists_iwasawa e g
      let p : parab k e := ⟨(u : GL n k) * leviEmb k e l,
        mul_mem (unipRad_le_parab k e u.2) (leviEmb_mem_parab k e l)⟩
      have := parInd_law e (piTensor σ) x p κ
      change f ((u : GL n k) * leviEmb k e l * κ) = _ at this
      rw [this, show x.1.1 κ = f κ from rfl, hfK κ hκ, h0, smul_zero, map_zero, smul_zero]
    apply Subtype.ext; apply Subtype.ext; funext g
    exact hall g
  · intro a h hh
    set l : Levi k m := Pi.mulSingle a h with hl
    have hlK : ∀ b, l b ∈ KO k (m b) := by
      intro b
      by_cases hb : b = a
      · subst hb; simp [l, hh]
      · simp [l, Pi.mulSingle_eq_of_ne hb, one_mem]
    have hemb : leviEmb k e l ∈ KO k n := by
      have := (UnitInd.unip_mul_levi_mem_KO e (1 : unipRad k e) l).2 ⟨one_mem _, hlK⟩
      simpa using this
    have hdet : GeneralLinearGroup.det (leviEmb k e l) = GeneralLinearGroup.det h := by
      rw [det_leviEmb, Finset.prod_eq_single a]
      · simp [l]
      · intro b _ hb; simp [l, Pi.mulSingle_eq_of_ne hb]
      · simp
    have hδ : deltaHalf k m l = 1 := by
      rw [deltaHalf_apply]
      refine Finset.prod_eq_one fun b _ => isUnram_absPow k _ _ (hval (hlK b))
    let p : parab k e := ⟨leviEmb k e l, leviEmb_mem_parab k e l⟩
    have hlaw := parInd_law e (piTensor σ) x p 1
    have hp : leviProj k e p = l := leviProj_leviEmb k e l
    rw [mul_one, hp, hδ, Units.val_one, one_smul] at hlaw
    change f (leviEmb k e l) = piTensor σ l (f 1) at hlaw
    rw [hfK _ hemb, hdet] at hlaw
    exact hlaw.symm

end GlobalTheory.SphBlock
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levi_block_eigenvector_at_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ) (x : IndSp e (piTensor σ)), x ≠ 0 → (∀ g ∈ KO k n, multiProd e σ g x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → ∃ w : PiTensorProduct ℂ X, w ≠ 0 ∧ ∀ a, ∀ h ∈ KO k (m a), piTensor σ (Pi.mulSingle a h) w = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • w := by
  atlas_forward_decl GlobalTheory.SphBlock.exists_eigen_at_one
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.SphSupport

open ValuativeRel Cardinal

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gl_one_comm (x y : GL (Fin 1) k) : x * y = y * x := by
  apply Units.ext
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem levi_comm {m : ℕ} (g h : Levi k (fun _ : Fin m => Fin 1)) : g * h = h * g :=
  funext fun a => gl_one_comm (g a) (h a)

theorem scalar_det_fin_one (g : GL (Fin 1) k) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det g) = g := by
  apply Units.ext
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_one]

theorem det_scalar_fin_one (z : kˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) z) = z := by
  ext; simp [Matrix.GeneralLinearGroup.scalar]

theorem mk_ne_zero (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V) (hs : IsSmooth σ) (hi : σ.IsIrreducible)
    (hχ : IsSmoothChar χ) (hy : y ≠ 0)
    (hK : ∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y)
    {s : ℕ} (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin m) :
    (Submodule.Quotient.mk y : Jacquet σ (unipRad k e)) ≠ 0 := by
  intro h0
  let σ' : Representation ℂ (GL (Fin m) k) V := twist σ (detChar (Fin m) χ⁻¹)
  let π : Irr k m := ⟨V, σ', isSmooth_twist hs hχ.inv.detChar, GlobalTheory.LocGL.isIrreducible_twist hi _⟩
  have hker : twKer σ' (unipRad k e) 1 = twKer σ (unipRad k e) 1 := by
    unfold twKer
    congr 1
    ext w
    constructor <;> rintro ⟨u, v, rfl⟩ <;> refine ⟨u, v, ?_⟩ <;>
      simp [σ', det_eq_one_of_mem_unipRad k u.2]
  have hle : KOne k (Fin m) ⊔ (unipRad k e ⊓ KO k (Fin m)) ≤ KO k (Fin m) :=
    sup_le (Subgroup.map_le_range _ _) inf_le_right
  refine hy (hD k m s d e π y ?_ ?_)
  · intro h
    have hKO := hle h.2
    show σ' h y = _
    simp only [σ', twist_apply, detChar_apply, hK _ hKO, smul_smul, MonoidHom.inv_apply]
    simp
  · show (Submodule.Quotient.mk y : V ⧸ twKer σ' (unipRad k e) 1) = 0
    rw [Submodule.Quotient.mk_eq_zero, hker]
    exact (Submodule.Quotient.mk_eq_zero _).1 h0

theorem inSupport_of_KO_eigen (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {m : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V) (hs : IsSmooth σ)
    (hi : σ.IsIrreducible) (hχ : IsSmoothChar χ) (hm : 0 < m) (hy : y ≠ 0)
    (hK : ∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) :
    ∃ α : ℂˣ, InSupport σ (χ * unrChar k α) := by
  let e : (Σ _ : Fin m, Fin 1) ≃ Fin m := Equiv.sigmaUnique (Fin m) fun _ => Fin 1
  have hy' := mk_ne_zero hD σ χ y hs hi hχ hy hK (fun _ : Fin m => 1) e
  let a0 : Fin m := ⟨0, hm⟩
  let S : Set (Levi k (fun _ : Fin m => Fin 1)) :=
    {g | ∀ a, valuation k ((Matrix.GeneralLinearGroup.det (g a) : kˣ) : k) = 1}
  let θ : Levi k (fun _ : Fin m => Fin 1) → ℂ := fun g =>
    (((deltaHalf k (fun _ : Fin m => Fin 1) g)⁻¹ : ℂˣ) : ℂ) *
      (χ (Matrix.GeneralLinearGroup.det (leviEmb k e g)) : ℂ)
  have hKOlevi : ∀ g ∈ S, leviEmb k e g ∈ KO k (Fin m) := by
    intro g hg
    have h1 : leviEmb k e g = diagT k (Fin m) (fun j => Matrix.GeneralLinearGroup.det (g j)) := by
      conv_lhs => rw [GlobalTheory.EigenSupport.eq_torusToLevi m g]
      exact GlobalTheory.SmGL.EmptyBlocks.leviEmb_torusToLevi k e _
    rw [h1]
    exact iwahori_le_KO k (Fin m) (diagT_mem_iwahori (t := fun j => Matrix.GeneralLinearGroup.det (g j)) hg)
  have hδ : ∀ g ∈ S, deltaHalf k (fun _ : Fin m => Fin 1) g = 1 := by
    intro g hg
    rw [deltaHalf_apply]
    exact Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ (hg a)
  have hθ : ∀ g ∈ S, jac e σ g (Submodule.Quotient.mk y) = θ g • (Submodule.Quotient.mk y : Jacquet σ (unipRad k e)) := by
    intro g hg
    rw [jac_mk, hK _ (hKOlevi g hg), Submodule.Quotient.mk_smul, smul_smul]
  obtain ⟨Y, _, _, τ, hτi, hτs, y₀, hy₀, hy₀θ⟩ :=
    GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen _ _ (jac e σ) S θ _ hy' hθ
  have hrank : Module.rank ℂ Y ≤ ℵ₀ := by
    obtain ⟨S', f, hf⟩ := hτs
    haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin m)
    exact (LinearMap.rank_le_of_surjective f.toLinearMap hf).trans ((Submodule.rank_le _).trans
      ((LinearMap.rank_le_of_surjective _ (Submodule.mkQ_surjective _)).trans (GlobalTheory.LocGL.rank_le_aleph0_of_isIrreducible hs hi)))
  have hc : ∀ g : GL (Fin 1) k, ∃ c : ℂ, ∀ w, τ (Pi.mulSingle a0 g) w = c • w := fun g =>
    GlobalTheory.LocGL.exists_eq_smul_of_rank_le hτi hrank ⟨τ (Pi.mulSingle a0 g), fun h => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, levi_comm]⟩
  choose c hc using hc
  have hc1 : c 1 = 1 := smul_left_injective ℂ hy₀ (by
    show c 1 • y₀ = (1 : ℂ) • y₀
    rw [← hc, Pi.mulSingle_one, map_one, one_smul]; rfl)
  have hcmul : ∀ g h, c (g * h) = c g * c h := fun g h => smul_left_injective ℂ hy₀ (by
    show c (g * h) • y₀ = (c g * c h) • y₀
    rw [← hc, Pi.mulSingle_mul, map_mul, Module.End.mul_apply, hc h, hc g, smul_smul])
  let ω' : GL (Fin 1) k →* ℂˣ := MonoidHom.toHomUnits ⟨⟨c, hc1⟩, hcmul⟩
  let ω : kˣ →* ℂˣ := ω'.comp (Matrix.GeneralLinearGroup.scalar (Fin 1))
  have hω : ∀ u : kˣ, valuation k (u : k) = 1 → ω u = χ u := by
    intro u hu
    let g : Levi k (fun _ : Fin m => Fin 1) := Pi.mulSingle a0 (Matrix.GeneralLinearGroup.scalar (Fin 1) u)
    have hg : g ∈ S := by
      intro a
      by_cases ha : a = a0
      · subst ha; simp [g, det_scalar_fin_one, hu]
      · simp [g, Pi.mulSingle_eq_of_ne ha]
    have hdet : Matrix.GeneralLinearGroup.det (leviEmb k e g) = u := by
      rw [det_leviEmb, Finset.prod_eq_single a0]
      · simp [g, det_scalar_fin_one]
      · intro b _ hb; simp [g, Pi.mulSingle_eq_of_ne hb]
      · simp
    have h1 := (hc _ y₀).symm.trans (hy₀θ g hg)
    simp only [θ, hδ g hg, hdet, inv_one, Units.val_one, one_mul] at h1
    exact Units.ext (smul_left_injective ℂ hy₀ h1)
  obtain ⟨α, hα⟩ := GlobalTheory.JacSuppCount.eq_mul_unrChar_of_eq_on_units k χ ω hω
  refine ⟨α, m, fun _ => 1, e, a0, rfl, Y, inferInstance, inferInstance, τ, hτi, hτs, fun g w => ?_⟩
  rw [← hα]
  show τ (Pi.mulSingle a0 g) w = c (Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det g)) • w
  rw [scalar_det_fin_one, hc]

end GlobalTheory.SphSupport

theorem GlobalTheory.SphSupport.inSupport_mul_unrChar_of_KO_eigen : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V), IsSmooth σ → σ.IsIrreducible → IsSmoothChar χ → 0 < m → y ≠ 0 → (∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ α : ℂˣ, InSupport σ (χ * unrChar k α) := by
  intro _ _ hD k _ _ _ _ m V _ _ σ χ y hs hi hχ hm hy hK
  exact GlobalTheory.SphSupport.inSupport_of_KO_eigen hD σ χ y hs hi hχ hm hy hK
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inSupport_mul_unramifiedChar_of_integralEigenvector : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V), IsSmooth σ → σ.IsIrreducible → IsSmoothChar χ → 0 < m → y ≠ 0 → (∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ α : ℂˣ, InSupport σ (χ * unrChar k α) := by
  atlas_forward_decl GlobalTheory.SphSupport.inSupport_mul_unrChar_of_KO_eigen
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charInCuspidalSupport_of_jacquet_subquotient_factor : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) k) V) (β : Type) [Fintype β] [LinearOrder β] (c : β → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (j₀ : β) (ψ : kˣ →* ℂˣ), IsSmooth ρ → IsSubquotient (piTensor fun j => (s j).ρ) (jac f ρ) → InSupport (s j₀).ρ ψ → InSupport ρ ψ := by
  first | exact @GlobalTheory.SuppStage.main | exact GlobalTheory.SuppStage.main | (intros; apply GlobalTheory.SuppStage.main <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSpherical_twist_of_jacquet_constituent_empty_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin t) k) W) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin t) (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (χ : kˣ →* ℂˣ) (z : (s true).V), IsSmooth π → π.IsIrreducible → c false = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (jac f π) → z ≠ 0 → (∀ g ∈ KO k (Fin (c true)), (s true).ρ g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z) → IsSpherical (twist π (detChar (Fin t) χ⁻¹)) := by
  first | exact @GlobalTheory.EmptyFirstBlock.isSpherical_twist_of_empty_block | exact GlobalTheory.EmptyFirstBlock.isSpherical_twist_of_empty_block | (intros; apply GlobalTheory.EmptyFirstBlock.isSpherical_twist_of_empty_block <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.BlockSph

theorem sph_of_isBlockVec : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (π₁ : Irr k r) (π₂ : Irr k t) (v : π.V), IsSmoothChar χ → IsTame χ → (∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α)) → Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) → v ≠ 0 → IsBlockVec χ π.π v → IsSpherical (twist π₂.π (detChar (Fin t) χ⁻¹)) := by
  intro hBZ hG hDZ k _ _ _ _ r t χ π π₁ π₂ v hχ hχt hsupp ⟨φ⟩ hv hblk
  obtain ⟨E⟩ := Exponents.prod₂_equiv_multiProd k r t _ _ π₁.π π₂.π
  let Ψ := φ.trans E
  have hsm : IsSmooth (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)) :=
    isSmooth_parInd _ _
  have hirr : (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)).IsIrreducible :=
    (MultiIrr.isIrreducible_iff_of_equiv Ψ).1 π.irr
  have hv' : Ψ v ≠ 0 := fun h => hv (Ψ.injective (h.trans (map_zero Ψ).symm))
  have hblk' : IsBlockVec χ (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)) (Ψ v) :=
    fun h hh h1 h2 u hu => by
      have := Ψ.toIntertwiningMap.isIntertwining _ _ h v
      rw [hblk h hh h1 h2 u hu, map_smul] at this
      exact this.symm
  obtain ⟨hx0, hx⟩ := GlobalTheory.T.jacquetModule_image_ne_zero_of_blockTypeVector hDZ k r t χ _ _ (Ψ v) hsm hirr hχt hv' hblk'
  obtain ⟨Y, _, _, τ, hτ, hsub, y, hy0, hy⟩ := GlobalTheory.T.exists_irreducible_subquotient_common_eigenvector _ _ (jac (two (stdSum (rfl : r + t = r + t)))
    (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)))
    {h | ∃ g ∈ KO k (Fin t), h = Pi.mulSingle true g}
    (fun h => (χ (Matrix.GeneralLinearGroup.det (h true)) : ℂ)) _ hx0
    (by rintro _ ⟨g, hg, rfl⟩; simpa using hx g hg)
  have hρs : ∀ i, IsSmooth (Exponents.twoRep π₁.π π₂.π i) := fun i => by
    cases i
    · exact π₁.smooth
    · exact π₂.smooth
  have hρl : ∀ i, HasFiniteLength (Exponents.twoRep π₁.π π₂.π i) := fun i => by
    cases i
    · exact hasFiniteLength_of_isIrreducible π₁.irr
    · exact hasFiniteLength_of_isIrreducible π₂.irr
  obtain ⟨b, f, g, s, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2
    (two (stdSum (rfl : r + t = r + t))) (two (stdSum (rfl : r + t = r + t))) hρs hρl hτ hsub
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.T.levi_rep_parabolic_char k Bool (Two (Fin r) (Fin t)) _ (fun j => multiProd (g j) fun i => (s i j).ρ)
    Y τ true χ y (fun j => isSmooth_parInd _ _) hχ hcol hy0
    (fun h hh => by simpa using hy (Pi.mulSingle true h) ⟨h, hh, rfl⟩)
  obtain ⟨w, hw0, hw⟩ := GlobalTheory.T.exists_levi_block_eigenvector_at_identity k Bool (fun i => Fin (b.1 i true)) (Fin t) (g true) _ (fun i => (s i true).ρ) χ z hz0 hz
  by_cases hm : b.1 false true = 0
  · obtain ⟨z', hz'0, hz'⟩ := GlobalTheory.T.levi_rep_parabolic_char k Bool (fun i => Fin (b.1 i true)) _ (fun i => (s i true).ρ) _
      (piTensor fun i => (s i true).ρ) true χ w (fun i => (s i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw true)
    have hc : b.1 true false = 0 := by
      have h1 := b.2.1 true
      have h2 := b.2.2 true
      simp [Fintype.sum_bool] at h1 h2
      omega
    exact GlobalTheory.T.isSpherical_twist_of_jacquet_constituent_empty_block k t _ π₂.π (b.1 true) (f true) (s true) χ z' π₂.smooth π₂.irr hc (hrow true) hz'0 hz'
  · obtain ⟨z', hz'0, hz'⟩ := GlobalTheory.T.levi_rep_parabolic_char k Bool (fun i => Fin (b.1 i true)) _ (fun i => (s i true).ρ) _
      (piTensor fun i => (s i true).ρ) false χ w (fun i => (s i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw false)
    obtain ⟨α, hα⟩ := GlobalTheory.T.inSupport_mul_unramifiedChar_of_integralEigenvector hBZ hG hDZ k _ _ (s false true).ρ χ z' (s false true).smooth (s false true).irr hχ
      (Nat.pos_of_ne_zero hm) hz'0 hz'
    exact absurd (GlobalTheory.T.charInCuspidalSupport_of_jacquet_subquotient_factor hBZ hG k r _ π₁.π Bool (b.1 false) (f false) (s false) true _ π₁.smooth (hrow false) hα) (hsupp α)

end GlobalTheory.BlockSph
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_twist_of_blockTypeVector : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (π₁ : Irr k r) (π₂ : Irr k t) (v : π.V), IsSmoothChar χ → IsTame χ → (∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α)) → Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) → v ≠ 0 → IsBlockVec χ π.π v → IsSpherical (twist π₂.π (detChar (Fin t) χ⁻¹)) := by
  atlas_forward_decl GlobalTheory.BlockSph.sph_of_isBlockVec
end
