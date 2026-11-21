import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDualStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SpanRealProjectionRationalPointsEqTop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPointStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationa
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledFiniteMatrixMemLattice
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPoint
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FockVacuumAnnihilationEquationRealCoordinatesStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realSymplecticForm_alternating_invariant_definite : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ x, jO S T sS sT (jO S T sS sT x) = -x) ∧ (∀ x y, omO S T x y = -omO S T y x) ∧ (∀ x y, omO S T (jO S T sS sT x) (jO S T sS sT y) = omO S T x y) ∧ ∀ x, x ≠ 0 → omO S T (jO S T sS sT x) x < 0 := by
  first | exact @GlobalTheory.RealSymplForm.form_alt_inv_def | exact GlobalTheory.RealSymplForm.form_alt_inv_def | (intros; apply GlobalTheory.RealSymplForm.form_alt_inv_def <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticAdelicForm_biadditive_alternating_rational : ∀ (D : D7) (S T : HSp D), (∀ x x' y : WO S T, symplO S T (x + x') y = symplO S T x y + symplO S T x' y) ∧ (∀ x y y' : WO S T, symplO S T x (y + y') = symplO S T x y + symplO S T x y') ∧ (∀ x y : WO S T, symplO S T x y = -symplO S T y x) ∧ (∀ x : WO S T, symplO S T x x = 0) ∧ ∀ γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ a : D.host.F, symplO S T (ratW T S γ) (ratW T S γ') = algebraMap D.host.F (AF D.host.F) a := by
  first | exact @GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt | exact GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt | (intros; apply GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_finite_matrix_mem_lattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem | exact GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem | (intros; apply GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem <;> assumption)
end

section
section
open Matrix

namespace GlobalTheory

open Matrix in

theorem _root_.GlobalTheory.differentiable_exp_mul_of_annihilated :
    ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℝ f → (∀ w z : Fin g → ℂ, (fderiv ℝ f w z + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star z)).im : ℂ) * f w) + Complex.I * (fderiv ℝ f w (Complex.I • z) + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star (Complex.I • z))).im : ℂ) * f w) = 0) → Differentiable ℂ fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w := by
  intro g Hm _ f hfd hann
  let B0 : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℂ :=
    LinearMap.mk₂ ℝ (fun u v => u ⬝ᵥ Hm.mulVec (star v))
      (fun u₁ u₂ v => by simp [add_dotProduct])
      (fun r u v => by simp [smul_dotProduct])
      (fun u v₁ v₂ => by simp [star_add, Matrix.mulVec_add, dotProduct_add])
      (fun r u v => by simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])
  let B : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B0)
  have hB : ∀ u v, B u v = u ⬝ᵥ Hm.mulVec (star v) := fun u v => rfl
  have hQ : ∀ w : Fin g → ℂ, HasFDerivAt (fun w : Fin g → ℂ => w ⬝ᵥ Hm.mulVec (star w))
      (B.precompR _ w (ContinuousLinearMap.id ℝ _) + B.precompL _ (ContinuousLinearMap.id ℝ _) w) w :=
    fun w => B.hasFDerivAt_of_bilinear (hasFDerivAt_id w) (hasFDerivAt_id w)
  intro w
  have hF : HasFDerivAt (fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w) _ w :=
    (((hQ w).const_mul ((Real.pi : ℂ) / 2)).cexp).mul (hfd w).hasFDerivAt
  refine (differentiableAt_iff_restrictScalars ℝ hF.differentiableAt).2 ?_
  rw [hF.fderiv]
  set e := Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) with he
  set T := e • fderiv ℝ f w + f w • (e • (((Real.pi : ℂ) / 2) •
    (B.precompR _ w (ContinuousLinearMap.id ℝ _) + B.precompL _ (ContinuousLinearMap.id ℝ _) w)))
    with hTdef
  have hT : ∀ z, T z = e * fderiv ℝ f w z + f w * (e * ((Real.pi : ℂ) / 2 *
      (w ⬝ᵥ Hm.mulVec (star z) + z ⬝ᵥ Hm.mulVec (star w)))) := by
    intro z
    clear hann hQ hF hTdef
    simp only [T, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, hB, smul_eq_mul]
  have key : ∀ z, T (Complex.I • z) = Complex.I • T z := by
    intro z
    have h1 := hann w z
    have hs1 : w ⬝ᵥ Hm.mulVec (star (Complex.I • z)) = -Complex.I * (w ⬝ᵥ Hm.mulVec (star z)) := by
      simp [Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_neg, dotProduct_smul]
    have hs2 : (Complex.I • z) ⬝ᵥ Hm.mulVec (star w) = Complex.I * (z ⬝ᵥ Hm.mulVec (star w)) := by
      simp [smul_dotProduct]
    rw [hs1] at h1
    rw [hT, hT, hs1, hs2, smul_eq_mul]
    set b := w ⬝ᵥ Hm.mulVec (star z)
    have him : (-Complex.I * b).im = -b.re := by simp
    rw [him] at h1
    have hb : b = b.re + b.im * Complex.I := (Complex.re_add_im b).symm
    push_cast at h1
    linear_combination (-Complex.I * e) * h1 + (-Complex.I * e * Real.pi * f w) * hb +
      (e * fderiv ℝ f w (Complex.I • z) - Real.pi * Complex.I * e * b.re * f w) * Complex.I_sq
  let L : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun c z => by
        have hc : c • z = c.re • z + c.im • (Complex.I • z) := by
          ext i
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im c]
          ring
        rw [hc, T.map_add, T.map_smul, T.map_smul, key, RingHom.id_apply]
        simp only [Complex.real_smul, smul_eq_mul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring }
  exact ⟨LinearMap.toContinuousLinearMap L, ContinuousLinearMap.ext fun z => rfl⟩

end GlobalTheory
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiable_exp_mul_of_annihilated' : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℝ f → (∀ w z : Fin g → ℂ, (fderiv ℝ f w z + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star z)).im : ℂ) * f w) + Complex.I * (fderiv ℝ f w (Complex.I • z) + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star (Complex.I • z))).im : ℂ) * f w) = 0) → Differentiable ℂ fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w := by
  atlas_forward_decl GlobalTheory.differentiable_exp_mul_of_annihilated
end

section
namespace GlobalTheory.RationalValueRealScalar

theorem map_rat_smul_real {U : Type} [AddCommGroup U] [Module ℝ U] {V : Type} [AddCommGroup V]
    [Module ℚ V] (p : V →+ U) (c : ℚ) (x : V) : p (c • x) = (c : ℝ) • p x := by
  have h1 : (c.den : ℤ) • (c • x) = c.num • x := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    rw [Int.cast_natCast, mul_comm, Rat.mul_den_eq_num]
  have h2 : (c.den : ℝ) • p (c • x) = (c.num : ℝ) • p x := by
    rw [← Int.cast_natCast, Int.cast_smul_eq_zsmul ℝ, Int.cast_smul_eq_zsmul ℝ, ← map_zsmul, ← map_zsmul, h1]
  have hd : (c.den : ℝ) ≠ 0 := by positivity
  calc p (c • x) = ((c.den : ℝ)⁻¹ * c.den) • p (c • x) := by rw [inv_mul_cancel₀ hd, one_smul]
    _ = (c.den : ℝ)⁻¹ • ((c.den : ℝ) • p (c • x)) := by rw [smul_smul]
    _ = (c.den : ℝ)⁻¹ • ((c.num : ℝ) • p x) := by rw [h2]
    _ = (c : ℝ) • p x := by rw [smul_smul, Rat.cast_def, inv_mul_eq_div]

theorem exists_rat_value {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) (u v : V) :
    ∃ q : ℚ, (q : ℝ) = -(om (p u) (p v)) := by
  obtain ⟨N, hN, hNu⟩ := hL u
  obtain ⟨M, hM, hMv⟩ := hL v
  obtain ⟨k, hk⟩ := hint _ hNu _ hMv
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hk
  refine ⟨-(k / (N * M) : ℚ), ?_⟩
  have hNM : (N : ℝ) * M ≠ 0 := by positivity
  push_cast
  rw [neg_inj, div_eq_iff hNM, ← hk]
  ring

theorem exists_rat_bilinForm {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] [Module ℚ V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) :
    ∃ B : LinearMap.BilinForm ℚ V, ∀ u v : V, ((B u v : ℚ) : ℝ) = -(om (p u) (p v)) := by
  choose q hq using exists_rat_value om p L hL hint
  refine ⟨LinearMap.mk₂ ℚ q ?_ ?_ ?_ ?_, fun u v => hq u v⟩
  · intro u1 u2 v
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_add, hq, hq, hq, map_add, LinearMap.map_add, LinearMap.add_apply]
    ring
  · intro c u v
    apply Rat.cast_injective (α := ℝ)
    rw [smul_eq_mul, Rat.cast_mul, hq, hq, map_rat_smul_real, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro u v1 v2
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_add, hq, hq, hq, map_add, LinearMap.map_add]
    ring
  · intro c u v
    apply Rat.cast_injective (α := ℝ)
    rw [smul_eq_mul, Rat.cast_mul, hq, hq, map_rat_smul_real, LinearMap.map_smul, smul_eq_mul]
    ring

end GlobalTheory.RationalValueRealScalar
end

section
section
open Matrix

namespace GlobalTheory.VacuumLine

theorem exists_coord {U : Type} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
    (J : U →ₗ[ℝ] U) (hJ : ∀ x, J (J x) = -x) :
    ∃ (g : ℕ) (e : U ≃ₗ[ℝ] (Fin g → ℂ)), ∀ v, e (J v) = Complex.I • e v := by
  let φ : ℂ →ₐ[ℝ] Module.End ℝ U := Complex.liftAux (J : Module.End ℝ U) (by ext x; simp [hJ])
  letI : Module ℂ U := Module.compHom U (φ : ℂ →+* Module.End ℝ U)
  have hsm : ∀ (z : ℂ) (v : U), z • v = z.re • v + z.im • J v := fun z v => by
    change φ z v = _
    simp [φ, Complex.liftAux_apply]
  haveI : IsScalarTower ℝ ℂ U := ⟨fun r z v => by
    simp [hsm, smul_add, smul_smul]⟩
  haveI : FiniteDimensional ℂ U := Module.Finite.of_restrictScalars_finite ℝ ℂ U
  have hI : ∀ v : U, Complex.I • v = J v := fun v => by simp [hsm]
  let e := (Module.finBasis ℂ U).equivFun
  exact ⟨_, e.restrictScalars ℝ, fun v => by rw [← hI]; exact e.map_smul _ _⟩

theorem exists_ratForm {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] [Module ℚ V] (p : V →+ U) (L : AddSubgroup V)
    (hN : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k) :
    ∃ B : LinearMap.BilinForm ℚ V, ∀ u v, (B u v : ℝ) = -om (p u) (p v) := by
  first
  | exact @_root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm
  | exact _root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm
  | (apply _root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm <;> assumption)
  | (intros; apply _root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm ..)

theorem span_image {U : Type} [AddCommGroup U] [Module ℝ U]
    {V : Type} [AddCommGroup V] (p : V →+ U) (hsp : Submodule.span ℝ (Set.range p) = ⊤)
    (L : AddSubgroup V) (hN : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L) :
    Submodule.span ℝ (p '' (L : Set V)) = ⊤ := by
  rw [eq_top_iff, ← hsp, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨N, hN0, hx⟩ := hN x
  have h0 : (N : ℝ) ≠ 0 := by positivity
  have : p x = (N : ℝ)⁻¹ • p (N • x) := by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ h0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hx, rfl⟩)

theorem fg_of_integral {U : Type} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
    (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (hom : ∀ x, om x = 0 → x = 0)
    {V : Type} [AddCommGroup V] (p : V →+ U) (hp : Function.Injective p) (L : AddSubgroup V)
    (hsp : Submodule.span ℝ (p '' (L : Set V)) = ⊤)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k) :
    (AddSubgroup.toIntSubmodule L).FG := by
  have hfg : (Submodule.span ℝ (p '' (L : Set V))).FG := hsp ▸ Module.Finite.fg_top
  obtain ⟨s, hs, hss⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  rw [hsp] at hss
  have h : ∀ (x : AddSubgroup.toIntSubmodule L) (y : s), ∃ k : ℤ, (k : ℝ) = om (p x) y := by
    rintro x ⟨y, hy⟩
    obtain ⟨y, hy', rfl⟩ := hs hy
    obtain ⟨k, hk⟩ := hint x x.2 y hy'
    exact ⟨k, hk.symm⟩
  choose k hk using h
  let φ : AddSubgroup.toIntSubmodule L →+ (s → ℤ) := AddMonoidHom.mk' k fun a b => by
    funext y
    apply Int.cast_injective (α := ℝ)
    simp [hk]
  have hφ : Function.Injective φ.toIntLinearMap := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => Subtype.ext (hp ?_)
    rw [ZeroMemClass.coe_zero, map_zero]
    refine hom _ (LinearMap.ext_on hss.symm fun y hy => ?_)
    have : k x ⟨y, hy⟩ = 0 := congrFun hx ⟨y, hy⟩
    have h2 := hk x ⟨y, hy⟩
    rw [this] at h2
    simpa using h2.symm
  exact Module.Finite.iff_fg.1 (Module.Finite.of_injective _ hφ)

theorem not_linearIndependent : ∀ (U : Type) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] (J : U →ₗ[ℝ] U) (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ), (∀ x, J (J x) = -x) → (∀ x y, om x y = -om y x) → (∀ x y, om (J x) (J y) = om x y) → (∀ x, x ≠ 0 → om (J x) x < 0) → ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (p : V →+ U), Function.Injective p → Submodule.span ℝ (Set.range p) = ⊤ → ∀ L : AddSubgroup V, (∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L) → (∀ x : V, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k) → ∀ c : V → ℂ, (∀ v, ‖c v‖ = 1) → ∀ f : Fin 2 → U → ℂ, (∀ k, Differentiable ℝ (f k)) → (∀ k w z, (fderiv ℝ (f k) w z - Real.pi * Complex.I * (om w z : ℂ) * f k w) + Complex.I * (fderiv ℝ (f k) w (J z) - Real.pi * Complex.I * (om w (J z) : ℂ) * f k w) = 0) → (∀ k, ∀ v ∈ L, ∀ z, f k (z + p v) = c v * Complex.exp (-(Real.pi * Complex.I) * (om z (p v) : ℂ)) * f k z) → ¬ LinearIndependent ℂ f := by
  intro U _ _ _ J om hJ halt hinv hpos V _ _ _ p hp hsp L hN hL c hc f hd hann hf hli
  obtain ⟨g, e, he⟩ := exists_coord J hJ
  have hs : ∀ z, e.symm (Complex.I • z) = J (e.symm z) := fun z => by
    rw [e.symm_apply_eq, he, e.apply_symm_apply]
  obtain ⟨Hm, hH, hHpos, hHim⟩ := GlobalTheory.PeriodNonempty.exists_herm
    (-(om.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap))
    (fun x y => by simp [halt (e.symm x)]) (fun x y => by simp [hs, hinv])
    (fun x hx => by simpa [hs] using hpos (e.symm x) (by simpa using hx))
  have him : ∀ x y, (x ⬝ᵥ Hm.mulVec (star y)).im = -om (e.symm x) (e.symm y) := hHim
  have hpos' : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := hHpos
  have hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k := fun x hx => (hL x).1 hx
  obtain ⟨B, hB⟩ := exists_ratForm om p L hN hint
  have hspL := span_image p hsp L hN
  have hom : ∀ x, om x = 0 → x = 0 := fun x hx => by
    by_contra h
    have := hpos x h
    rw [halt, hx] at this
    simp at this
  have hfg := fg_of_integral om hom p hp L hspL hint
  let P : V →ₗ[ℤ] (Fin g → ℂ) := (e.toLinearMap.toAddMonoidHom.comp p).toIntLinearMap
  have hP : ∀ v, P v = e (p v) := fun _ => rfl
  let E : (Fin g → ℂ) →L[ℝ] U := LinearMap.toContinuousLinearMap e.symm.toLinearMap
  have hE : ∀ z, E z = e.symm z := fun _ => rfl
  have hconj : ∀ x y : Fin g → ℂ,
      x ⬝ᵥ Hm.mulVec (star y) = starRingEnd ℂ (y ⬝ᵥ Hm.mulVec (star x)) := fun x y => by
    change _ = star _
    rw [← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]
  refine GlobalTheory.Dict.ThetaOne.proportional_of_selfDual B P (e.injective.comp hp)
    (AddSubgroup.toIntSubmodule L) hfg ?_ ?_ hH hpos' ?_ c hc
    (fun k w => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f k (e.symm w)) ?_ ?_ ?_
  · intro x
    refine (hL x).trans (forall₂_congr fun y _ => ⟨?_, ?_⟩)
    · rintro ⟨k, hk⟩
      refine ⟨-k, Rat.cast_injective (α := ℝ) ?_⟩
      rw [hB, hk]; simp
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      have := hB x y
      rw [hk] at this
      push_cast at this ⊢
      linarith
  · have : P '' (AddSubgroup.toIntSubmodule L : Set V) = e.toLinearMap '' (p '' (L : Set V)) := by
      rw [Set.image_image]; rfl
    rw [this, ← Submodule.map_span, hspL, Submodule.map_top, LinearEquiv.range]
  · intro u v
    rw [him, hB, hP, hP, e.symm_apply_apply, e.symm_apply_apply]
  · intro k
    refine GlobalTheory.T.differentiable_exp_mul_of_annihilated' g Hm hH (fun w => f k (E w)) ((hd k).comp E.differentiable) fun w z => ?_
    have h1 : fderiv ℝ (fun w => f k (E w)) w = (fderiv ℝ (f k) (E w)).comp E :=
      ((hd k (E w)).hasFDerivAt.comp w E.hasFDerivAt).fderiv
    have h2 := hann k (e.symm w) (e.symm z)
    rw [h1]
    simp only [ContinuousLinearMap.comp_apply, hE, him, hs]
    push_cast
    linear_combination h2
  · intro k v hv z
    have h1 : (om (e.symm z) (p v) : ℂ) = -((z ⬝ᵥ Hm.mulVec (star (P v))).im : ℂ) := by
      rw [him, hP, e.symm_apply_apply]; simp
    have h2 : e.symm (z + P v) = e.symm z + p v := by rw [map_add, hP, e.symm_apply_apply]
    have h3 : (Real.pi / 2 * ((z + P v) ⬝ᵥ Hm.mulVec (star (z + P v))) : ℂ) +
        -(Real.pi * Complex.I) * (om (e.symm z) (p v) : ℂ) =
        (Real.pi * (z ⬝ᵥ Hm.mulVec (star (P v))) +
          Real.pi / 2 * (P v ⬝ᵥ Hm.mulVec (star (P v)))) +
          Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)) := by
      rw [h1, star_add, mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hconj (P v) z]
      have h4 := Complex.sub_conj (z ⬝ᵥ Hm.mulVec (star (P v)))
      push_cast at h4
      linear_combination (-(Real.pi : ℂ) / 2) * h4
    have h5 := congrArg Complex.exp h3
    rw [Complex.exp_add, Complex.exp_add _ (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)))] at h5
    simp only [h2, hf k v hv]
    linear_combination c v * f k (e.symm z) * h5
  · rw [Fintype.linearIndependent_iff] at hli ⊢
    intro a ha
    refine hli a (funext fun u => ?_)
    have h1 := congrFun ha (e u)
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      e.symm_apply_apply] at h1 ⊢
    refine mul_left_cancel₀
      (Complex.exp_ne_zero (Real.pi / 2 * (e u ⬝ᵥ Hm.mulVec (star (e u))))) ?_
    linear_combination h1

end GlobalTheory.VacuumLine
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_linearIndependent_alt : ∀ (U : Type) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] (J : U →ₗ[ℝ] U) (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ), (∀ x, J (J x) = -x) → (∀ x y, om x y = -om y x) → (∀ x y, om (J x) (J y) = om x y) → (∀ x, x ≠ 0 → om (J x) x < 0) → ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (p : V →+ U), Function.Injective p → Submodule.span ℝ (Set.range p) = ⊤ → ∀ L : AddSubgroup V, (∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L) → (∀ x : V, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k) → ∀ c : V → ℂ, (∀ v, ‖c v‖ = 1) → ∀ f : Fin 2 → U → ℂ, (∀ k, Differentiable ℝ (f k)) → (∀ k w z, (fderiv ℝ (f k) w z - Real.pi * Complex.I * (om w z : ℂ) * f k w) + Complex.I * (fderiv ℝ (f k) w (J z) - Real.pi * Complex.I * (om w (J z) : ℂ) * f k w) = 0) → (∀ k, ∀ v ∈ L, ∀ z, f k (z + p v) = c v * Complex.exp (-(Real.pi * Complex.I) * (om z (p v) : ℂ)) * f k z) → ¬ LinearIndependent ℂ f := by
  atlas_forward_decl GlobalTheory.VacuumLine.not_linearIndependent
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

noncomputable section

namespace GlobalTheory.RatSelfDual

variable {D : D7}

def symplB (S T : HSp D) : WO S T →+ WO S T →+ AF D.host.F :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => symplO S T x y) ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1 x))
    (fun x x' => AddMonoidHom.ext fun y => (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1 x x' y)

theorem symplO_nsmul (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T x (N • y) = symplO S T (N • x) y := by
  have h1 : symplO S T x (N • y) = N • symplO S T x y := (symplB S T x).map_nsmul N y
  have h2 : symplO S T (N • x) y = N • symplO S T x y := ((symplB S T).flip y).map_nsmul N x
  rw [h1, h2]

theorem symplO_eq_add (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]

theorem psi_real {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1))
    (S T : HSp D) (x y : WO S T) (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    ψ (symplO S T x y) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (piW θ T S x) (piW θ T S y) : ℂ)) := by
  rw [symplO_eq_add, AddChar.map_add_eq_mul, GlobalTheory.OrientedChar.char_symplOH D θ ψ hθ hψ S T x y h, ← Complex.exp_add]
  congr 1
  ring

theorem psi_fin_mul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplO S T (finRat S T x) (finRat S T y)) *
      Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℂ)) = 1 := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨a, ha⟩ := (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.2.2.2 x y
  have h1 : ψ (symplO S T (ratW T S x) (ratW T S y)) = 1 := by rw [ha]; exact hψ.1.2.2.1 a
  have hx : (iotaW σ T S (infRat S T x) : WO S T).map (finPart D) = 0 := hσ.real_iota T S _
  have hy : (iotaW σ T S (infRat S T y) : WO S T).map (finPart D) = 0 := hσ.real_iota T S _
  have e1 := psi_real hθ hψ S T (iotaW σ T S (infRat S T x)) (ratW T S y) (Or.inl hx)
  have e2 := psi_real hθ hψ S T (finRat S T x) (iotaW σ T S (infRat S T y)) (Or.inr hy)
  rw [hσ.pi_iota, piW_ratW hθ] at e1
  rw [piW_of_inf θ (finRat_inf S T x), LinearMap.map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero] at e2
  have d1 : symplO S T (ratW T S x) (ratW T S y) =
      symplO S T (iotaW σ T S (infRat S T x)) (ratW T S y) + symplO S T (finRat S T x) (ratW T S y) :=
    (congrArg (fun w => symplO S T w (ratW T S y)) (ratW_eq hσ S T x)).trans ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1 _ _ _)
  have d2 : symplO S T (finRat S T x) (ratW T S y) =
      symplO S T (finRat S T x) (iotaW σ T S (infRat S T y)) + symplO S T (finRat S T x) (finRat S T y) :=
    (congrArg (fun w => symplO S T (finRat S T x) w) (ratW_eq hσ S T y)).trans ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1 _ _ _)
  rw [d1, d2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e1, e2, one_mul, mul_comm] at h1
  exact h1

theorem psi_fin_iff {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplO S T (finRat S T x) (finRat S T y)) = 1 ↔ ∃ k : ℤ, omO S T (infRat S T x) (infRat S T y) = k := by
  have h := psi_fin_mul hψ S T x y
  constructor
  · intro h1
    rw [h1, one_mul, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨-n, ?_⟩
    have h2 : ((omO S T (infRat S T x) (infRat S T y) : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
      apply mul_left_cancel₀ (neg_ne_zero.2 Complex.two_pi_I_ne_zero)
      rw [hn]; push_cast; ring
    exact_mod_cast h2
  · rintro ⟨k, hk⟩
    have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℂ)) = 1 := by
      rw [hk, Complex.exp_eq_one_iff]
      exact ⟨-k, by push_cast; ring⟩
    rwa [h2, mul_one] at h

theorem eq_zero_of_parts {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {z : WO S T}
    (hf : z.map (finPart D) = 0) (hi : z.map (infPart D) = 0) : z = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  funext i j
  refine hσ.ext _ (congrFun (congrFun hf i) j) fun τ => ?_
  have : infPart D (z i j) = 0 := congrFun (congrFun hi i) j
  rw [this, RingHom.map_zero]

theorem exists_div {S T : HSp D} {u : WO S T} (hu : u.map (infPart D) = 0) {N : ℕ} (hN : 0 < N) :
    ∃ γ : WO S T, γ.map (infPart D) = 0 ∧ N • γ = u := by
  refine ⟨Matrix.of fun i j => incA D ((N : D.host.E)⁻¹) * u i j, ?_, ?_⟩
  · funext i j
    have : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
    show infPart D (incA D ((N : D.host.E)⁻¹) * u i j) = 0
    rw [RingHom.map_mul, this, mul_zero]
  · funext i j
    show N • (incA D ((N : D.host.E)⁻¹) * u i j) = u i j
    have h1 : (N : AE D) = incA D (N : D.host.E) := (map_natCast (incA D) N).symm
    have h2 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [nsmul_eq_mul, ← mul_assoc, h1, ← map_mul, mul_inv_cancel₀ h2, map_one, one_mul]

theorem finRat_mem_iff : ∀ (D : D7) (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)), IsStdChar D ψ (-1) → (∀ u ∈ Λ, u.map (infPart D) = 0) → (∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)) → (∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0) → (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ Λ) → ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T x ∈ Λ ↔ ∀ y : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T y ∈ Λ → ∃ k : ℤ, omO S T (infRat S T x) (infRat S T y) = k := by
  intro D S T ψ Λ hψ hinf hdual happ hden x
  constructor
  · intro hx y hy
    exact (psi_fin_iff hψ S T x y).1 ((hdual _ (finRat_inf S T x)).1 hx _ hy)
  · intro h
    refine (hdual _ (finRat_inf S T x)).2 fun u' hu' => ?_
    obtain ⟨θ, hθ⟩ := hψ.2.1
    obtain ⟨N, hN, hNx⟩ := hden x
    obtain ⟨γ, hγ, hNγ⟩ := exists_div (hinf u' hu') hN
    obtain ⟨ρ, ⟨y₀, hy₀⟩, u, hu, hz⟩ := happ γ hγ
    have hz0 : γ - finRat S T y₀ - u = 0 := by
      refine eq_zero_of_parts hθ ?_ ?_
      · funext i j
        have e0 : finPart D (γ i j - ρ i j - u i j) = 0 := congrFun (congrFun hz i) j
        have e1 : finPart D (finRat S T y₀ i j) = finPart D (ρ i j) := by rw [← hy₀]; rfl
        show finPart D (γ i j - finRat S T y₀ i j - u i j) = 0
        rw [RingHom.map_sub, RingHom.map_sub] at e0 ⊢
        rw [e1, e0]
      · funext i j
        have e0 : infPart D (γ i j) = 0 := congrFun (congrFun hγ i) j
        have e1 : infPart D (finRat S T y₀ i j) = 0 := congrFun (congrFun (finRat_inf S T y₀) i) j
        have e2 : infPart D (u i j) = 0 := congrFun (congrFun (hinf u hu) i) j
        show infPart D (γ i j - finRat S T y₀ i j - u i j) = 0
        rw [RingHom.map_sub, RingHom.map_sub, e0, e1, e2, sub_zero, sub_zero]
    have hγe : γ = finRat S T y₀ + u := by
      rw [sub_sub] at hz0
      exact sub_eq_zero.1 hz0
    have hu'e : u' = finRat S T (N • y₀) + N • u := by
      rw [← hNγ, hγe, nsmul_add, (finRat S T).map_nsmul]
    have hmem : finRat S T (N • y₀) ∈ Λ := by
      have : finRat S T (N • y₀) = u' - N • u := (sub_eq_of_eq_add hu'e).symm
      rw [this]
      exact Λ.sub_mem hu' (Λ.nsmul_mem hu N)
    rw [hu'e, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1, AddChar.map_add_eq_mul, (psi_fin_iff hψ S T x _).2 (h _ hmem), one_mul,
      symplO_nsmul]
    exact (hdual _ (hinf _ hNx)).1 hNx u hu

end GlobalTheory.RatSelfDual

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff : ∀ (D : D7) (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)), IsStdChar D ψ (-1) → (∀ u ∈ Λ, u.map (infPart D) = 0) → (∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)) → (∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0) → (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ Λ) → ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T x ∈ Λ ↔ ∀ y : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T y ∈ Λ → ∃ k : ℤ, omO S T (infRat S T x) (infRat S T y) = k := by
  first | exact @GlobalTheory.RatSelfDual.finRat_mem_iff | exact GlobalTheory.RatSelfDual.finRat_mem_iff | (intros; apply GlobalTheory.RatSelfDual.finRat_mem_iff <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare

noncomputable section

namespace GlobalTheory.VacUnique

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem apply_real_add (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {u : WO S T} (hu : u.map (infPart D) = 0)
    {f : WO S T → ℂ} {ε : ℂ} (hf : heisO ψ S T u f = ε • f) (z : RW T S) :
    f (iotaW σ T S z + u) = ε * f (iotaW σ T S z) := by
  have e : ψ (symplOH S T (iotaW σ T S z) u) * f (iotaW σ T S z + u) = ε * f (iotaW σ T S z) := congrFun hf _
  rw [GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ h.inf hψ S T _ _ (Or.inl (h.real_iota T S z)), piW_of_inf θ hu, LinearMap.map_zero] at e
  simpa using e

theorem exists_decomp (h : Chart θ σ) {Λ : AddSubgroup (WO S T)}
    (h2 : ∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0)
    (w : WO S T) : ∃ γ z, ∃ u ∈ Λ, w = ratW T S γ + (iotaW σ T S z + u) := by
  have h0 : (w - iotaW σ T S (piW θ T S w) : WO S T).map (infPart D) = 0 := by
    have hp : piW θ T S (w - iotaW σ T S (piW θ T S w)) = 0 := by
      rw [AddMonoidHom.map_sub, h.pi_iota, sub_self]
    funext i j
    exact ThetaCont.infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
  obtain ⟨_, ⟨γ, rfl⟩, u, hu, hr⟩ := h2 _ h0
  refine ⟨γ, piW θ T S w + piW θ T S (w - iotaW σ T S (piW θ T S w) - ratW T S γ - u), u, hu, ?_⟩
  rw [AddMonoidHom.map_add, h.iota_pi (x := w - iotaW σ T S (piW θ T S w) - ratW T S γ - u) hr]
  abel

theorem apply_add_infRat (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {ε : ℂ} (he : heisO ψ S T (finRat S T (-v)) f = ε • f) (z : RW T S) :
    f (iotaW σ T S (z + infRat S T v)) =
      (ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε) *
        Complex.exp (-(Real.pi * Complex.I) * (-omO S T (infRat S T v) z : ℝ)) * f (iotaW σ T S z) := by
  have e : iotaW σ T S (z + infRat S T v) = ratW T S v + (iotaW σ T S z + finRat S T (-v)) := by
    rw [ratW_eq h, AddMonoidHom.map_add, AddMonoidHom.map_neg]
    abel
  have e2 : symplOH S T (ratW T S v) (iotaW σ T S z + finRat S T (-v)) =
      symplOH S T (ratW T S v) (iotaW σ T S z) + symplOH S T (ratW T S v) (finRat S T (-v)) := by
    unfold symplOH
    rw [(GlobalTheory.T.symplecticAdelicForm_biadditive_alternating_rational D S T).2.1, mul_add]
  rw [e, hf.quasi, apply_real_add h hψ (finRat_inf S T _) he, e2, neg_add, AddChar.map_add_eq_mul,
    AddChar.map_neg_eq_inv ψ (symplOH S T (ratW T S v) (iotaW σ T S z)),
    GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ h.inf hψ S T _ _ (Or.inr (h.real_iota T S z)), piW_ratW h.inf, h.pi_iota, ← Complex.exp_neg]
  push_cast
  ring_nf

theorem infRat_injective (S T : HSp D) : Function.Injective (infRat S T) := by
  intro x y e
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    exact ⟨((GlobalTheory.CMTypePlaces.places_bijective D).2 w).choose⟩
  funext i j
  exact (tauE D τ).injective (congrFun (congrFun (congrFun e τ) i) j)

theorem vacUniqueO : ∀ D : D7, VacUniqueO D := by
  classical
  intro D ψ θ hψ hθ S T sS sT _ _ hS hT ΛS ΛT hΛS hΛT f f' hf hf'
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hΛS hΛT
  have hden := GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT hΛS.1 hΛT.1
  have hlat := hf.2.lat
  have hlat' := hf'.2.lat
  have hinf := fun u => latO_inf (u := u) S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at h1 h2 h3 hden hlat hlat' hinf
  choose ε hε1 hε2 using h3 f hlat

  have det : ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      IsLatVac (heisO ψ S T) Λ g → IsLatVac (heisO ψ S T) Λ g' →
      (∀ z, g' (iotaW σ T S z) = c * g (iotaW σ T S z)) → g' = c • g := by
    intro g g' c hg hg' hl hl' hz
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := exists_decomp h h2 w
    rw [Pi.smul_apply, smul_eq_mul, hg.quasi, hg'.quasi, apply_real_add h hψ (hinf u hu) (hε2 u hu g hl),
      apply_real_add h hψ (hinf u hu) (hε2 u hu g' hl'), hz]
    ring
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 f = 1 := hn p hp
  have n2 : nrm2 p.1 p.2 f' = 1 := hf'.2.norm.2 p hp
  have hne : (fun z : RW T S => f (iotaW σ T S z)) ≠ 0 := by
    intro h0
    have e := det f f 0 hf.2.theta hf.2.theta hlat hlat fun z => by rw [zero_mul]; exact congrFun h0 z
    rw [e] at n1
    simp [nrm2] at n1
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := span_piW_ratW_eq_top D θ σ h T S
    simpa only [piW_ratW hθ] using this
  have a1 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f hf.2.theta hf.2.fock
  have a2 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f' hf'.2.theta hf'.2.fock
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε _ hv else 1
  have hc : ∀ v, ‖c v‖ = 1 := fun v => by
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψ.1.2.1]
      rcases hε1 _ hv with e | e <;> rw [e] <;> simp
    · exact norm_one
  have law : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) Λ g →
      ∀ v ∈ Λ.comap (finRat S T), ∀ z, g (iotaW σ T S (z + infRat S T v)) =
        c v * Complex.exp (-(Real.pi * Complex.I) * (omO S T z (infRat S T v) : ℂ)) * g (iotaW σ T S z) := by
    intro g hg hl v hv z
    have hv' : finRat S T (-v) ∈ Λ := (Λ.comap (finRat S T)).neg_mem hv
    rw [apply_add_infRat h hψ hg v (hε2 _ hv' g hl) z, ← j2]
    simp only [c, dif_pos hv']
  have hli := GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) j1 j2 j3 j4 (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (infRat S T) (infRat_injective S T) hsp (Λ.comap (finRat S T))
    (fun x => by
      obtain ⟨N, hN, hx⟩ := hden x
      exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, AddMonoidHom.map_nsmul]⟩)
    (GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf h1 h2 hden) c hc
    ![fun z => f (iotaW σ T S z), fun z => f' (iotaW σ T S z)]
    (fun k => by fin_cases k; exacts [a1.1, a2.1]) (fun k => by fin_cases k; exacts [a1.2, a2.2])
    (fun k => by fin_cases k; exacts [law f hf.2.theta hlat, law f' hf'.2.theta hlat'])
  rw [LinearIndependent.pair_iff' hne] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  have e := det f f' a hf.2.theta hf'.2.theta hlat hlat' fun z => (congrFun ha z).symm
  refine ⟨a, ?_, e⟩
  have n3 : nrm2 p.1 p.2 (a • f) = ‖a‖ ^ 2 * nrm2 p.1 p.2 f := by
    simp only [nrm2, Pi.smul_apply, norm_smul, mul_pow]
    exact integral_const_mul _ _
  rw [e, n3, n1, mul_one] at n2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) two_ne_zero).1 n2

end GlobalTheory.VacUnique

end
end
