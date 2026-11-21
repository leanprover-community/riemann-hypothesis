import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeElementComponentMemStandardDoubleCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankReductionRangeAddCorank
import BuildAid.ForwardExisting

section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_ker_subspaces_and_heckePolyOf_convolution : (∀ (k U U' : Type) [Field k] [Fintype k] [AddCommGroup U] [Module k U] [FiniteDimensional k U] [AddCommGroup U'] [Module k U'] [FiniteDimensional k U'] (n t d : ℕ) (f : U →ₗ[k] U'), Module.finrank k U = n + t → Module.finrank k U' = n → Nat.card {W : Submodule k U // Module.finrank k W + d = n + t ∧ W ≤ LinearMap.ker f} = ∑ j ∈ Finset.range (d + 1), Fintype.card k ^ ((n - j) * (d - j)) * gaussBin (Fintype.card k) t (d - j) * Nat.card {W' : Submodule k U' // Module.finrank k W' = j ∧ LinearMap.range f ≤ W'}) ∧ ∀ (L : Type) [Field L] (q n t : ℕ) (a : ℕ → L) (ν s : L), (∀ j, n < j → a j = 0) → heckePolyOf (n + t) q (fun d => ∑ j ∈ Finset.range (d + 1), (q : L) ^ ((n - j) * (d - j)) * (gaussBin q t (d - j) : L) * ν ^ (d - j) * s ^ j * a j) = (heckePolyOf n q a).comp (C s * X) * blockPoly (ν * (q : L) ^ n) q t := by
  first | exact @GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv | exact GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv | (intros; apply GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitChart_uniformiser_and_residueCard : ∀ {D : D7} (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → Chart e v π → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (∃ p : Ov D v, algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D (ϖ : D.host.E)) ∧ Irreducible p) ∧ Nat.card (IsLocalRing.ResidueField (Ov D v)) = Ideal.absNorm P.asIdeal := by
  first | exact @GlobalTheory.SplitUnif.unif_chart | exact GlobalTheory.SplitUnif.unif_chart | (intros; apply GlobalTheory.SplitUnif.unif_chart <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitFrame_selfDualLattice_completion : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ V : HSp D, ∃ β : GL (Fin V.rank) (Fv D.host.F v), Frame V e π β := by
  first | exact @GlobalTheory.SplitFrame.exists_frame | exact GlobalTheory.SplitFrame.exists_frame | (intros; apply GlobalTheory.SplitFrame.exists_frame <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_homLattice_iff_integralMatrix_splitChart : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (S T : HSp D) (βS : GL (Fin S.rank) (Fv D.host.F v)) (βT : GL (Fin T.rank) (Fv D.host.F v)), Frame S e π βS → Frame T e π βT → ∃ c : Fv D.host.F v, c ≠ 0 ∧ ∀ u : WO S T, IsHalf e u → (u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) ↔ IntM (Ov D v) (c • ((βT⁻¹).1 * Matrix.map u π * βS.1))) := by
  first | exact @GlobalTheory.SplitHomLattice.mem_latO_iff_intM | exact GlobalTheory.SplitHomLattice.mem_latO_iff_intM | (intros; apply GlobalTheory.SplitHomLattice.mem_latO_iff_intM <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hyperspecial_iff_gInt_of_suppAt_split : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ g : GA D V, SuppAt e V g → (g ∈ KsphC V ∅ ↔ GInt (Ov D v) (rho V π β g)) := by
  first | exact @GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt | exact GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt | (intros; apply GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitSupported_unitary_component : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β x : GL (Fin V.rank) (Fv D.host.F v)), ∃ g : GA D V, SuppAt e V g ∧ rho V π β g = x := by
  first | exact @GlobalTheory.SplitOnto.exists_suppAt_rho_eq | exact GlobalTheory.SplitOnto.exists_suppAt_rho_eq | (intros; apply GlobalTheory.SplitOnto.exists_suppAt_rho_eq <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeElement_component_mem_standardDoubleCoset : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ (ϖ : D.host.E) (p : Ov D v) (k : ℕ) (α : GA D V), algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D ϖ) → IsHeckeElt V e ϖ k α → Hk (Ov D v) p k (rho V π β α) := by
  first | exact @GlobalTheory.SplitHecke.HeckeComp.hk_of_isHeckeElt | exact GlobalTheory.SplitHecke.HeckeComp.hk_of_isHeckeElt | (intros; apply GlobalTheory.SplitHecke.HeckeComp.hk_of_isHeckeElt <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_reduction_range_add_corank : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (n j : ℕ) (a : GL (Fin n) K) (A : Matrix (Fin n) (Fin n) O), j ≤ n → Hk O p j a → A.map (algebraMap O K) = a.1 → Module.finrank (IsLocalRing.ResidueField O) (LinearMap.range (A.map (IsLocalRing.residue O)).mulVecLin) + j = n := by
  first | exact @GlobalTheory.SplitHecke.finrank_range_reduction | exact GlobalTheory.SplitHecke.finrank_range_reduction | (intros; apply GlobalTheory.SplitHecke.finrank_range_reduction <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem exists_linearEquiv_map_eq_of_finrank_eq {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (W W' : Submodule k V)
    (h : Module.finrank k W = Module.finrank k W') :
    ∃ e : V ≃ₗ[k] V, W.map e.toLinearMap = W' := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  obtain ⟨U', hU'⟩ := W'.exists_isCompl
  have h1 := Submodule.finrank_add_eq_of_isCompl hU
  have h2 := Submodule.finrank_add_eq_of_isCompl hU'
  have h3 : Module.finrank k U = Module.finrank k U' := by omega
  let a : W ≃ₗ[k] W' := LinearEquiv.ofFinrankEq _ _ h
  let b : U ≃ₗ[k] U' := LinearEquiv.ofFinrankEq _ _ h3
  let e : V ≃ₗ[k] V := (Submodule.prodEquivOfIsCompl W U hU).symm ≪≫ₗ (a.prodCongr b) ≪≫ₗ
    Submodule.prodEquivOfIsCompl W' U' hU'
  have he : ∀ w : W, e w = a w := by
    intro w
    simp [e]
  refine ⟨e, ?_⟩
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have := he ⟨w, hw⟩
    change e w ∈ W'
    simp only at this
    rw [this]
    exact (a ⟨w, hw⟩).2
  · intro w hw
    refine ⟨a.symm ⟨w, hw⟩, (a.symm ⟨w, hw⟩).2, ?_⟩
    change e _ = w
    rw [he]
    simp

theorem exists_gl_map_residue_eq (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ)
    (W W' : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O))
    (h : Module.finrank (IsLocalRing.ResidueField O) W =
      Module.finrank (IsLocalRing.ResidueField O) W') :
    ∃ g : GL (Fin n) O, W.map (g.1.map (IsLocalRing.residue O)).mulVecLin = W' := by
  obtain ⟨e, he⟩ := exists_linearEquiv_map_eq_of_finrank_eq W W' h
  let M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O) := LinearMap.toMatrix' e.toLinearMap
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := O) (M i j)
  have hAM : (Matrix.of A).map (IsLocalRing.residue O) = M := by
    ext i j
    exact hA i j
  have hM : M.det ≠ 0 := by
    have : M.det = LinearMap.det e.toLinearMap := LinearMap.det_toMatrix' _
    rw [this]
    exact (LinearEquiv.isUnit_det' e).ne_zero
  have hu : IsUnit (Matrix.of A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    change ((Matrix.of A).map (IsLocalRing.residue O)).det ≠ 0
    rw [hAM]
    exact hM
  obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨g, ?_⟩
  rw [hg, hAM, ← he]
  congr 1
  exact Matrix.toLin'_toMatrix' e.toLinearMap

end GlobalTheory.SplitHecke
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke.Cosets

open IsLocalRing

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {p : O}

theorem map_res_eq_zero_iff (hp : Irreducible p) {m n : ℕ} (X : Matrix (Fin m) (Fin n) O) :
    X.map (residue O) = 0 ↔ ∃ C : Matrix (Fin m) (Fin n) O, X = p • C := by
  have hm : maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  constructor
  · intro h
    have : ∀ i j, ∃ c, X i j = p * c := by
      intro i j
      have h1 : residue O (X i j) = 0 := congrFun (congrFun h i) j
      rw [residue_eq_zero_iff, hm, Ideal.mem_span_singleton] at h1
      exact h1
    choose C hC using this
    exact ⟨Matrix.of C, Matrix.ext hC⟩
  · rintro ⟨C, rfl⟩
    ext i j
    have : residue O (p * C i j) = 0 := by
      rw [residue_eq_zero_iff, hm, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    exact this

theorem map_inj {m n : ℕ} {X Y : Matrix (Fin m) (Fin n) O}
    (h : X.map (algebraMap O K) = Y.map (algebraMap O K)) : X = Y := by
  ext i j
  exact IsFractionRing.injective O K (congrFun (congrFun h i) j)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem map_smul' {m n : ℕ} (c : O) (X : Matrix (Fin m) (Fin n) O) :
    (c • X).map (algebraMap O K) = algebraMap O K c • X.map (algebraMap O K) := by
  ext i j
  simp

theorem intM_inv_smul_iff (hp : Irreducible p) {m n : ℕ} (X : Matrix (Fin m) (Fin n) O) :
    IntM O ((algebraMap O K p)⁻¹ • X.map (algebraMap O K)) ↔ X.map (residue O) = 0 := by
  have h0 : algebraMap O K p ≠ 0 := by
    intro h
    exact hp.ne_zero (IsFractionRing.injective O K (by rw [h, map_zero]))
  rw [map_res_eq_zero_iff hp, intM_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, map_inj (K := K) ?_⟩
    rw [map_smul', hC, smul_smul, mul_inv_cancel₀ h0, one_smul]
  · rintro ⟨C, rfl⟩
    refine ⟨C, ?_⟩
    rw [map_smul', smul_smul, inv_mul_cancel₀ h0, one_smul]

theorem exists_of_range_le (hp : Irreducible p) {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O}
    (h : LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin) :
    ∃ B C : Matrix (Fin n) (Fin n) O, A' = A * B + p • C := by
  have h1 : ∀ j, ∃ b : Fin n → O, (A.map (residue O)) *ᵥ (fun i => residue O (b i)) =
      (A'.map (residue O)) *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨y, hy⟩ := h ⟨Pi.single j 1, rfl⟩
    choose b hb using fun i => residue_surjective (R := O) (y i)
    refine ⟨b, ?_⟩
    have : (fun i => residue O (b i)) = y := funext hb
    rw [this]
    exact hy
  choose b hb using h1
  obtain ⟨C, hC⟩ := (map_res_eq_zero_iff hp (A' - A * Matrix.of fun i j => b j i)).1 (by
    ext i j
    have := congrFun (hb j) i
    rw [Matrix.mulVec_single_one] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.col_apply] at this
    simp [Matrix.mul_apply, ← this])
  exact ⟨_, C, by rw [← hC]; abel⟩

theorem range_le_of_mul {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O} {a a' : GL (Fin n) K}
    (hA : A.map (algebraMap O K) = a.1) (hA' : A'.map (algebraMap O K) = a'.1) (h : IntM O (a⁻¹ * a').1) :
    LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin := by
  obtain ⟨B, hB⟩ := intM_iff.1 h
  have : A' = A * B := by
    refine map_inj (K := K) ?_
    rw [Matrix.map_mul, hA, hA', hB, ← Units.val_mul, mul_inv_cancel_left]
  rw [this, Matrix.map_mul, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

theorem intM_of_range_le (hp : Irreducible p) {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O} {a a' : GL (Fin n) K}
    (hA : A.map (algebraMap O K) = a.1) (hA' : A'.map (algebraMap O K) = a'.1)
    (ha : IntM O (algebraMap O K p • (a⁻¹).1))
    (h : LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin) :
    IntM O (a⁻¹ * a').1 := by
  obtain ⟨B, C, hBC⟩ := exists_of_range_le hp h
  have : (a⁻¹ * a').1 = B.map (algebraMap O K) + (algebraMap O K p • (a⁻¹).1) * C.map (algebraMap O K) := by
    rw [Units.val_mul, ← hA', hBC, Matrix.map_add _ (map_add _), Matrix.map_mul, map_smul', hA, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [this]
  exact (intM_iff.2 ⟨B, rfl⟩).add (ha.mul (intM_iff.2 ⟨C, rfl⟩))

theorem GInt.exists_det {n : ℕ} {k : GL (Fin n) K} (hk : GInt O k) : ∃ u : Oˣ, k.1.det = algebraMap O K u := by
  obtain ⟨A, hA⟩ := intM_iff.1 hk.1
  obtain ⟨B, hB⟩ := intM_iff.1 hk.2
  have : A * B = 1 := by
    refine map_inj (K := K) ?_
    rw [Matrix.map_mul, hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : IsUnit A.det := Matrix.isUnit_det_of_right_inverse this
  refine ⟨hu.unit, ?_⟩
  rw [← hA, IsUnit.unit_spec, RingHom.map_det]
  rfl

theorem hk_mul {n j : ℕ} {α k₁ k₂ : GL (Fin n) K} (hα : Hk O p j α) (h₁ : GInt O k₁) (h₂ : GInt O k₂) :
    Hk O p j (k₁ * α * k₂) := by
  refine ⟨(h₁.1.mul hα.1).mul h₂.1, ?_, ?_⟩
  · have := (h₂.2.mul hα.2.1).mul h₁.2
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    rwa [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] at this
  · obtain ⟨u, hu⟩ := hα.2.2
    obtain ⟨u₁, hu₁⟩ := GInt.exists_det h₁
    obtain ⟨u₂, hu₂⟩ := GInt.exists_det h₂
    refine ⟨u₁ * u * u₂, ?_⟩
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hu, hu₁, hu₂, ← map_mul, ← map_mul]
    congr 1
    push_cast
    ring

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem gInt_map {n : ℕ} (g : GL (Fin n) O) : GInt O (Matrix.GeneralLinearGroup.map (algebraMap O K) g) :=
  ⟨intM_iff.2 ⟨g.1, rfl⟩, by rw [← map_inv]; exact intM_iff.2 ⟨(g⁻¹).1, rfl⟩⟩

theorem cond_iff (hp : Irreducible p) {m n : ℕ} (z : Matrix (Fin m) (Fin n) O) {A : Matrix (Fin n) (Fin n) O}
    {a : Matrix (Fin n) (Fin n) K} (hA : A.map (algebraMap O K) = a) :
    IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * a) ↔
      LinearMap.range (A.map (residue O)).mulVecLin ≤ LinearMap.ker (z.map (residue O)).mulVecLin := by
  rw [← hA, Matrix.smul_mul, ← Matrix.map_mul, intM_inv_smul_iff hp, LinearMap.range_le_ker_iff,
    ← Matrix.mulVecLin_mul, Matrix.map_mul]
  constructor
  · intro h
    rw [h, Matrix.mulVecLin_zero]
  · intro h
    apply Matrix.toLin'.injective
    rw [map_zero]
    exact h

theorem card_cosets : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (m n j : ℕ) (ι : Type) (α : GL (Fin n) K) (R : Finset ι) (ρ : ι → GL (Fin n) K) (z : Matrix (Fin m) (Fin n) O), j ≤ n → Hk O p j α → Reps O α R ρ → Nat.card {γ : ι // γ ∈ R ∧ IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * (ρ γ).1)} = Nat.card {W : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O) // Module.finrank (IsLocalRing.ResidueField O) W + j = n ∧ W ≤ LinearMap.ker (z.map (IsLocalRing.residue O)).mulVecLin} := by
  intro O K _ _ _ _ _ _ p hp m n j ι α R ρ z hj hα hR
  have hH : ∀ γ ∈ R, Hk O p j (ρ γ) := by
    intro γ hγ
    obtain ⟨k₁, k₂, h₁, h₂, h⟩ := hR.1 γ hγ
    rw [h]
    exact hk_mul hα h₁ h₂
  choose A hA using fun γ (hγ : γ ∈ R) => intM_iff.1 (hH γ hγ).1
  refine Nat.card_eq_of_bijective (fun γ => ⟨LinearMap.range ((A γ.1 γ.2.1).map (residue O)).mulVecLin,
    GlobalTheory.SplitHecke.finrank_range_reduction O K p hp n j _ _ hj (hH _ γ.2.1) (hA _ γ.2.1), (cond_iff hp z (hA _ γ.2.1)).1 γ.2.2⟩) ⟨?_, ?_⟩
  · rintro ⟨γ, hγ, hγ1⟩ ⟨γ', hγ', hγ2⟩ h
    have h' : LinearMap.range ((A γ hγ).map (residue O)).mulVecLin =
        LinearMap.range ((A γ' hγ').map (residue O)).mulVecLin := congrArg Subtype.val h
    have hG : GInt O ((ρ γ)⁻¹ * ρ γ') := by
      refine ⟨intM_of_range_le hp (hA γ hγ) (hA γ' hγ') (hH γ hγ).2.1 h'.ge, ?_⟩
      rw [_root_.mul_inv_rev, inv_inv]
      exact intM_of_range_le hp (hA γ' hγ') (hA γ hγ) (hH γ' hγ').2.1 h'.le
    obtain ⟨k₁, k₂, h₁, h₂, he⟩ := hR.1 γ' hγ'
    have hu := hR.2 k₁ k₂ h₁ h₂
    rw [← he] at hu
    exact Subtype.ext (hu.unique ⟨hγ, hG⟩ ⟨hγ', by rw [inv_mul_cancel]; exact gInt_one⟩)
  · rintro ⟨W, hW, hWz⟩
    obtain ⟨A₀, hA₀⟩ := intM_iff.1 hα.1
    have h0 := GlobalTheory.SplitHecke.finrank_range_reduction O K p hp n j _ _ hj hα hA₀
    obtain ⟨g, hg⟩ := GlobalTheory.SplitHecke.exists_gl_map_residue_eq O n (LinearMap.range (A₀.map (residue O)).mulVecLin) W (by omega)
    obtain ⟨γ, ⟨hγ, hG⟩, -⟩ := hR.2 _ 1 (gInt_map g) gInt_one
    rw [mul_one] at hG
    have hgA : (g.1 * A₀).map (algebraMap O K) =
        (Matrix.GeneralLinearGroup.map (algebraMap O K) g * α).1 := by
      rw [Matrix.map_mul, hA₀]
      rfl
    have hr : LinearMap.range ((A γ hγ).map (residue O)).mulVecLin = W := by
      rw [← hg, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul, ← Matrix.map_mul]
      refine le_antisymm (range_le_of_mul hgA (hA γ hγ) ?_) (range_le_of_mul (hA γ hγ) hgA hG.1)
      have := hG.2
      rwa [_root_.mul_inv_rev, inv_inv] at this
    exact ⟨⟨γ, hγ, (cond_iff hp z (hA γ hγ)).2 (hr ▸ hWz)⟩, Subtype.ext hr⟩

end GlobalTheory.SplitHecke.Cosets
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_cosets_eq_subspaces_kernel_residue : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (m n j : ℕ) (ι : Type) (α : GL (Fin n) K) (R : Finset ι) (ρ : ι → GL (Fin n) K) (z : Matrix (Fin m) (Fin n) O), j ≤ n → Hk O p j α → Reps O α R ρ → Nat.card {γ : ι // γ ∈ R ∧ IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * (ρ γ).1)} = Nat.card {W : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O) // Module.finrank (IsLocalRing.ResidueField O) W + j = n ∧ W ≤ LinearMap.ker (z.map (IsLocalRing.residue O)).mulVecLin} := by
  first | exact @GlobalTheory.SplitHecke.Cosets.card_cosets | exact GlobalTheory.SplitHecke.Cosets.card_cosets | (intros; apply GlobalTheory.SplitHecke.Cosets.card_cosets <;> assumption)
end

section
open Matrix

namespace GlobalTheory

def killersEquiv {k : Type} [Field k] {m n : ℕ} (A : Matrix (Fin n) (Fin n) k) :
    {w : Matrix (Fin m) (Fin n) k // w * A = 0} ≃ (Fin m → LinearMap.ker (Aᵀ).mulVecLin) where
  toFun w i := ⟨w.1 i, by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
    funext l
    have := congrFun (congrFun w.2 i) l
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this⟩
  invFun f := ⟨Matrix.of fun i => (f i).1, by
    ext i l
    have h := (f i).2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at h
    have := congrFun h l
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this⟩
  left_inv w := by ext i l; rfl
  right_inv f := by ext i l; rfl

theorem natCard_matrices_mul_eq_zero (k : Type) [Field k] [Finite k] (m n j : ℕ)
    (A : Matrix (Fin n) (Fin n) k)
    (h : Module.finrank k (LinearMap.range A.mulVecLin) + j = n) :
    Nat.card {w : Matrix (Fin m) (Fin n) k // w * A = 0} = Nat.card k ^ (j * m) := by
  have h1 : Module.finrank k (LinearMap.range (Aᵀ).mulVecLin)
      = Module.finrank k (LinearMap.range A.mulVecLin) := Matrix.rank_transpose A
  have h2 := LinearMap.finrank_range_add_finrank_ker (Aᵀ).mulVecLin
  rw [h1, Module.finrank_fin_fun] at h2
  have h3 : Module.finrank k (LinearMap.ker (Aᵀ).mulVecLin) = j := by omega
  rw [Nat.card_congr (killersEquiv A), Nat.card_fun, Module.natCard_eq_pow_finrank (K := k), h3,
    Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, pow_mul]

end GlobalTheory
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_left_kernel_matrices_eq_pow : ∀ (k : Type) [Field k] [Finite k] (m n j : ℕ) (A : Matrix (Fin n) (Fin n) k), Module.finrank k (LinearMap.range A.mulVecLin) + j = n → Nat.card {w : Matrix (Fin m) (Fin n) k // w * A = 0} = Nat.card k ^ (j * m) := by
  atlas_forward_decl GlobalTheory.natCard_matrices_mul_eq_zero
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem card_le_ker_transpose_eq_card_range_le :
    ∀ (k : Type) [Field k] (m n j : ℕ) (z : Matrix (Fin m) (Fin n) k), Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W + j = m ∧ W ≤ LinearMap.ker zᵀ.mulVecLin} = Nat.card {W' : Submodule k (Fin m → k) // Module.finrank k W' = j ∧ LinearMap.range z.mulVecLin ≤ W'} := by
  intro k _ m n j z
  set B : LinearMap.BilinForm k (Fin m → k) := Matrix.toBilin' (1 : Matrix (Fin m) (Fin m) k) with hBdef
  have hB : ∀ x y, B x y = x ⬝ᵥ y := by
    intro x y
    rw [hBdef, Matrix.toBilin'_apply', Matrix.one_mulVec]
  have hrefl : B.IsRefl := by
    intro x y h
    rw [hB] at h ⊢
    rw [dotProduct_comm]; exact h
  have hnd : B.Nondegenerate := by
    rw [hBdef]
    exact Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))
  have hinv : ∀ W : Submodule k (Fin m → k), B.orthogonal (B.orthogonal W) = W :=
    fun W => LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W
  have hdim : ∀ W : Submodule k (Fin m → k),
      Module.finrank k W + Module.finrank k (B.orthogonal W) = m := by
    intro W
    have h1 := LinearMap.BilinForm.finrank_orthogonal hnd W
    have h2 := Submodule.finrank_le W
    simp only [Module.finrank_fin_fun] at h1 h2
    omega
  have hker : LinearMap.ker zᵀ.mulVecLin = B.orthogonal (LinearMap.range z.mulVecLin) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff, Matrix.mulVecLin_apply]
    constructor
    · rintro h _ ⟨y, rfl⟩
      show B (z.mulVecLin y) x = 0
      rw [hB, Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, h, zero_dotProduct]
    · intro h
      ext i
      have h1 : B (z.mulVecLin (Pi.single i 1)) x = 0 := h _ ⟨_, rfl⟩
      rw [hB, Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, dotProduct_single, mul_one] at h1
      simpa using h1
  let e : Submodule k (Fin m → k) ≃ Submodule k (Fin m → k) :=
    ⟨B.orthogonal, B.orthogonal, hinv, hinv⟩
  refine Nat.card_congr (e.subtypeEquiv fun W => ?_)
  show _ ↔ Module.finrank k (B.orthogonal W) = j ∧ LinearMap.range z.mulVecLin ≤ B.orthogonal W
  have hd := hdim W
  refine and_congr ⟨fun h => by omega, fun h => by omega⟩ ?_
  rw [hker]
  constructor
  · intro h
    have := LinearMap.BilinForm.orthogonal_le (B := B) h
    rwa [hinv] at this
  · intro h
    have := LinearMap.BilinForm.orthogonal_le (B := B) h
    rwa [hinv] at this

end GlobalTheory.SplitHecke
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_subspaces_ker_transpose_eq_card_range : ∀ (k : Type) [Field k] (m n j : ℕ) (z : Matrix (Fin m) (Fin n) k), Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W + j = m ∧ W ≤ LinearMap.ker zᵀ.mulVecLin} = Nat.card {W' : Submodule k (Fin m → k) // Module.finrank k W' = j ∧ LinearMap.range z.mulVecLin ≤ W'} := by
  atlas_forward_decl GlobalTheory.SplitHecke.card_le_ker_transpose_eq_card_range_le
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum Formalism.IndefR.Mult IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

section Pure

open IsLocalRing

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {p : O}

def tr {n : ℕ} (g : GL (Fin n) K) : GL (Fin n) K :=
  ⟨g.1ᵀ, (g⁻¹).1ᵀ, by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]⟩

theorem tr_mul {n : ℕ} (g h : GL (Fin n) K) : tr (g * h) = tr h * tr g :=
  Units.ext (Matrix.transpose_mul _ _)

theorem tr_inv {n : ℕ} (g : GL (Fin n) K) : (tr g)⁻¹ = tr g⁻¹ := Units.ext rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem gInt_tr {n : ℕ} {g : GL (Fin n) K} : GInt O (tr g) ↔ GInt O g :=
  ⟨fun h => ⟨h.1.transpose, h.2.transpose⟩, fun h => ⟨h.1.transpose, h.2.transpose⟩⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem gInt_inv {n : ℕ} {g : GL (Fin n) K} : GInt O g⁻¹ ↔ GInt O g :=
  ⟨fun h => inv_inv g ▸ h.inv, fun h => h.inv⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem Hk.tr {n j : ℕ} {g : GL (Fin n) K} (h : Hk O p j g) : Hk O p j (tr g) :=
  ⟨h.1.transpose, h.2.1.transpose, by
    obtain ⟨u, hu⟩ := h.2.2
    exact ⟨u, (Matrix.det_transpose _).trans hu⟩⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem Reps.tr {n : ℕ} {ι : Type} {α : GL (Fin n) K} {R : Finset ι} {ρ : ι → GL (Fin n) K} (h : Reps O α⁻¹ R ρ) :
    Reps O (tr α) R fun γ => tr (ρ γ)⁻¹ := by
  refine ⟨fun γ hγ => ?_, fun k₁ k₂ h₁ h₂ => ?_⟩
  · obtain ⟨k₁, k₂, h₁, h₂, h⟩ := h.1 γ hγ
    refine ⟨_, _, gInt_tr.2 h₁.inv, gInt_tr.2 h₂.inv, ?_⟩
    beta_reduce
    rw [h, ← tr_mul, ← tr_mul]
    congr 1
  · have e : ∀ k : GL (Fin n) K, k = SplitHecke.tr (SplitHecke.tr k) := fun k => Units.ext rfl
    refine (existsUnique_congr fun γ => and_congr_right fun _ => ?_).1
      (h.2 _ _ (gInt_tr.2 h₁).inv (gInt_tr.2 h₂).inv)
    conv_rhs => rw [e k₁, e k₂, ← tr_mul, ← tr_mul, tr_inv, ← tr_mul, gInt_tr, ← gInt_inv]
    congr! 1

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem GInt.det {n : ℕ} {g : GL (Fin n) K} (h : GInt O g) : ∃ u : Oˣ, g.1.det = algebraMap O K u := by
  obtain ⟨A, hA⟩ := intM_iff.1 h.1
  obtain ⟨B, hB⟩ := intM_iff.1 h.2
  have e : ∀ C : Matrix (Fin n) (Fin n) O, (C.map (algebraMap O K)).det = algebraMap O K C.det :=
    fun C => (RingHom.map_det _ C).symm
  have h1 : A.det * B.det = 1 := by
    apply IsFractionRing.injective O K
    rw [map_mul, ← e, ← e, hA, hB, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      map_one]
  exact ⟨Units.mkOfMulEqOne _ _ h1, by rw [← hA, e]; rfl⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem Hk.mul {n j : ℕ} {g k₁ k₂ : GL (Fin n) K} (h : Hk O p j g) (h₁ : GInt O k₁) (h₂ : GInt O k₂) :
    Hk O p j (k₁ * g * k₂) := by
  refine ⟨(h₁.1.mul h.1).mul h₂.1, ?_, ?_⟩
  · have := (h₂.2.mul h.2.1).mul h₁.2
    rw [Matrix.mul_smul, Matrix.smul_mul] at this
    rwa [_root_.mul_inv_rev, _root_.mul_inv_rev, ← mul_assoc]
  · obtain ⟨u, hu⟩ := h.2.2
    obtain ⟨u₁, hu₁⟩ := h₁.det
    obtain ⟨u₂, hu₂⟩ := h₂.det
    refine ⟨u₁ * u * u₂, ?_⟩
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hu, hu₁, hu₂, ← map_mul, ← map_mul,
      Units.val_mul, Units.val_mul]
    congr 1
    ring

theorem intM_div_iff (hp : Irreducible p) {m n : ℕ} (z : Matrix (Fin m) (Fin n) O) :
    IntM O ((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) ↔ z.map (residue O) = 0 := by
  have h0 : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [Matrix.map_apply, Matrix.zero_apply, residue_eq_zero_iff, hp.maximalIdeal_eq, Ideal.mem_span_singleton',
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  refine exists_congr fun a => ?_
  rw [eq_inv_mul_iff_mul_eq₀ h0, ← map_mul, (IsFractionRing.injective O K).eq_iff, mul_comm]

variable (O) in

def sec (a : ResidueField O) : O := (residue_surjective a).choose

theorem residue_sec (a : ResidueField O) : residue O (sec O a) = a := (residue_surjective a).choose_spec

variable (K p) in

def yw {m n : ℕ} (w : Matrix (Fin m) (Fin n) (ResidueField O)) : Matrix (Fin m) (Fin n) K :=
  (algebraMap O K p)⁻¹ • (w.map (sec O)).map (algebraMap O K)

theorem map_sec {m n : ℕ} (w : Matrix (Fin m) (Fin n) (ResidueField O)) : (w.map (sec O)).map (residue O) = w :=
  Matrix.ext fun i j => residue_sec (w i j)

theorem existsUnique_yw (hp : Irreducible p) {m n : ℕ} {y : Matrix (Fin m) (Fin n) K}
    (hy : IntM O (algebraMap O K p • y)) : ∃! w, IntM O (y - yw K p w) := by
  have h0 : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  obtain ⟨z, hz⟩ := intM_iff.1 hy
  have e : ∀ w, IntM O (y - yw K p w) ↔ w = z.map (residue O) := fun w => by
    have : y - yw K p w = (algebraMap O K p)⁻¹ • (z - w.map (sec O)).map (algebraMap O K) := by
      rw [Matrix.map_sub _ (map_sub _), smul_sub, hz, smul_smul, inv_mul_cancel₀ h0, one_smul, yw]
    rw [this, intM_div_iff hp, Matrix.map_sub _ (map_sub _), map_sec, sub_eq_zero, eq_comm]
  simp only [e, existsUnique_eq]

theorem card_inversePrimeReps_integral_right_mul_hecke [Finite (ResidueField O)] (hp : Irreducible p) {m n j : ℕ} (hj : j ≤ n) {a : GL (Fin n) K}
    (ha : Hk O p j a) : Nat.card {w : Matrix (Fin m) (Fin n) (ResidueField O) // IntM O (yw K p w * a.1)} =
      Nat.card (ResidueField O) ^ (j * m) := by
  obtain ⟨A, hA⟩ := intM_iff.1 ha.1
  rw [← GlobalTheory.T.natCard_left_kernel_matrices_eq_pow _ m n j _ (GlobalTheory.T.finrank_reduction_range_add_corank O K p hp n j a A hj ha hA)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  rw [yw, ← hA, Matrix.smul_mul, ← Matrix.map_mul, intM_div_iff hp, Matrix.map_mul, map_sec]

theorem intM_tr {m n : ℕ} (w : Matrix (Fin m) (Fin n) (ResidueField O)) (a : GL (Fin m) K) :
    IntM O (a.1 * yw K p w) ↔ IntM O (yw K p wᵀ * (tr a).1) := by
  have : yw K p wᵀ * (tr a).1 = (a.1 * yw K p w)ᵀ := by
    rw [Matrix.transpose_mul]
    rfl
  rw [this]
  exact ⟨fun h => h.transpose, fun h => h.transpose⟩

theorem card_tgt [Finite (ResidueField O)] (hp : Irreducible p) {m n j : ℕ} (hj : j ≤ m) {a : GL (Fin m) K}
    (ha : Hk O p j a) : Nat.card {w : Matrix (Fin m) (Fin n) (ResidueField O) // IntM O (a.1 * yw K p w)} =
      Nat.card (ResidueField O) ^ (j * n) := by
  rw [← card_inversePrimeReps_integral_right_mul_hecke hp hj ha.tr]
  exact Nat.card_congr ((Matrix.transposeAddEquiv _ _ _).toEquiv.subtypeEquiv fun w => intM_tr w a)

def nKer {k : Type} [Field k] {m n : ℕ} (j : ℕ) (w : Matrix (Fin m) (Fin n) k) : ℕ :=
  Nat.card {W : Submodule k (Fin n → k) // Module.finrank k W + j = n ∧ W ≤ LinearMap.ker w.mulVecLin}

theorem card_heckeCosetReps_integral_right_inversePrime (hp : Irreducible p) {m n j : ℕ} (hj : j ≤ n) {ι : Type} {α : GL (Fin n) K} {R : Finset ι}
    {ρ : ι → GL (Fin n) K} (hα : Hk O p j α) (hR : Reps O α R ρ) (w : Matrix (Fin m) (Fin n) (ResidueField O)) :
    Nat.card {γ : ι // γ ∈ R ∧ IntM O (yw K p w * (ρ γ).1)} = nKer j w := by
  have := GlobalTheory.T.card_cosets_eq_subspaces_kernel_residue O K p hp m n j ι α R ρ (w.map (sec O)) hj hα hR
  rwa [map_sec] at this

theorem count_tgt (hp : Irreducible p) {m n j : ℕ} (hj : j ≤ m) {ι : Type} {α : GL (Fin m) K} {R : Finset ι}
    {ρ : ι → GL (Fin m) K} (hα : Hk O p j α) (hR : Reps O α⁻¹ R ρ) (w : Matrix (Fin m) (Fin n) (ResidueField O)) :
    Nat.card {γ : ι // γ ∈ R ∧ IntM O (((ρ γ)⁻¹).1 * yw K p w)} = nKer j wᵀ := by
  rw [← card_heckeCosetReps_integral_right_inversePrime hp hj hα.tr hR.tr wᵀ]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun γ => and_congr_right fun _ => intM_tr w _)

theorem nKer_eq_sum {k : Type} [Field k] [Finite k] {m n t d : ℕ} (h : n = m + t) (w : Matrix (Fin m) (Fin n) k) :
    nKer d w = ∑ j ∈ Finset.range (min d m + 1),
      Nat.card k ^ ((m - j) * (d - j)) * Formalism.L2.Col.gaussBin (Nat.card k) t (d - j) * nKer j wᵀ := by
  letI := Fintype.ofFinite k
  have h1 := GlobalTheory.T.card_ker_subspaces_and_heckePolyOf_convolution.1 k (Fin n → k) (Fin m → k) m t d w.mulVecLin (by rw [Module.finrank_fin_fun, h])
    (Module.finrank_fin_fun k)
  rw [← h] at h1
  rw [nKer, h1, Nat.card_eq_fintype_card (α := k)]
  symm
  simp only [← GlobalTheory.T.card_subspaces_ker_transpose_eq_card_range k m n]
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j hj hj' => ?_
  rw [Finset.mem_range] at hj hj'
  have : IsEmpty {W : Submodule k (Fin m → k) // Module.finrank k W + j = m ∧ W ≤ LinearMap.ker wᵀ.mulVecLin} :=
    ⟨fun W => by have := W.2.1; omega⟩
  rw [nKer, Nat.card_of_isEmpty, mul_zero]

end Pure

section Chart

open IsLocalRing GlobalTheory.SplitScalar GlobalTheory.AdelicLatMove

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem one_sub_mul_idem {A : Type} [CommRing A] {a : A} (ha : a * a = a) (d : A) :
    (1 - a) * (a * d + (1 - a)) = 1 - a := by
  linear_combination (1 - d) * ha

theorem idem_mul_inv {A : Type} [CommRing A] {a d d' : A} (ha : a * a = a) (h : d * d' = 1) :
    (a * d + (1 - a)) * (a * d' + (1 - a)) = 1 := by
  linear_combination a * a * h + (2 - d - d') * ha

theorem suppAt_of {V : HSp D} {g : GA D V}
    (h : (1 - (e + cA D e)) • mt V g = (1 - (e + cA D e)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) :
    SuppAt e V g := by
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, sub_eq_zero] at h
  exact fun i j => (congrFun (congrFun h i) j).symm

theorem suppAt_one (V : HSp D) : SuppAt e V 1 := suppAt_of (by rw [mt_one])

theorem suppAt_inv {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt e V g⁻¹ := suppAt_of (off_smul_mt_inv h)

theorem suppAt_mul {V : HSp D} {g g' : GA D V} (h : SuppAt e V g) (h' : SuppAt e V g') : SuppAt e V (g * g') :=
  suppAt_of (by rw [mt_mul, ← Matrix.smul_mul, off_smul_mt h, Matrix.smul_mul, Matrix.one_mul, off_smul_mt h'])

theorem reps_of (he : IsSplitIdem D e) (hπ : Chart e v π) {V : HSp D} {β : GL (Fin V.rank) (Fv D.host.F v)}
    (hβ : Frame V e π β) {α : GA D V} (hα : SuppAt e V α) {R : Finset (GA D V)} (hR : ∀ γ ∈ R, SuppAt e V γ)
    (h : IsCosetRep V (locPart V (KsphC V ∅) e) α R) : Reps (Ov D v) (rho V π β α) R (rho V π β) := by
  have st := GlobalTheory.T.mem_hyperspecial_iff_gInt_of_suppAt_split e v π he hπ V β hβ
  refine ⟨fun γ hγ => ?_, fun k₁ k₂ h₁ h₂ => ?_⟩
  · obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := h.1 γ hγ
    exact ⟨_, _, (st _ h₁.2).1 h₁.1, (st _ h₂.2).1 h₂.1, by rw [map_mul, map_mul]⟩
  · obtain ⟨g₁, s₁, rfl⟩ := GlobalTheory.T.exists_splitSupported_unitary_component e v π he hπ V β k₁
    obtain ⟨g₂, s₂, rfl⟩ := GlobalTheory.T.exists_splitSupported_unitary_component e v π he hπ V β k₂
    refine (existsUnique_congr fun γ => and_congr_right fun hγ => ?_).1
      (h.2 _ ⟨g₁, ⟨(st _ s₁).2 h₁, s₁⟩, g₂, ⟨(st _ s₂).2 h₂, s₂⟩, rfl⟩)
    have s := suppAt_mul (suppAt_inv (hR γ hγ)) (suppAt_mul (suppAt_mul s₁ hα) s₂)
    rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, ← st _ s]
    exact ⟨fun h => h.1, fun h => ⟨h, s⟩⟩

theorem det_mul_det_inv {V : HSp D} (g : GA D V) : (mt V g).det * (mt V g⁻¹).det = 1 := by
  rw [← Matrix.det_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.det_one]

def detU (he : e * e = e) (V : HSp D) (g : GA D V) : (AE D)ˣ :=
  ⟨e * (mt V g).det + (1 - e), e * (mt V g⁻¹).det + (1 - e),
    idem_mul_inv he (det_mul_det_inv g), (mul_comm _ _).trans (idem_mul_inv he (det_mul_det_inv g))⟩

theorem isDetAt_detU (he : e * e = e) (V : HSp D) (g : GA D V) : IsDetAt e V g (detU he V g) := rfl

theorem detU_inv (he : e * e = e) (V : HSp D) (g : GA D V) : detU he V g⁻¹ = (detU he V g)⁻¹ := Units.ext rfl

theorem Chart.map_e (hπ : Chart e v π) (he : e * e = e) : π e = 1 := by
  have := (hπ.2.1 (1 - e)).2 (by rw [mul_sub, mul_one, he, sub_self])
  rwa [map_sub, map_one, sub_eq_zero, eq_comm] at this

theorem chi_of_unit (hπ : Chart e v π) {x d : (AE D)ˣ} (hx1 : (1 - e) * (x : AE D) = 1 - e)
    (hd1 : (1 - e) * (d : AE D) = 1 - e) {χ : (AE D)ˣ →* Circle}
    (hχ : ∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D →
      finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) {u : (Ov D v)ˣ}
    (h1 : π (d : AE D) = π (x : AE D) * algebraMap (Ov D v) (Fv D.host.F v) u) : χ d = χ x := by
  have h3 : π ((x⁻¹ * d : (AE D)ˣ) : AE D) = algebraMap (Ov D v) (Fv D.host.F v) u := by
    rw [Units.val_mul, π.map_mul, h1, ← mul_assoc, ← π.map_mul, Units.inv_mul, π.map_one, one_mul]
  have h4 := hχ (x⁻¹ * d) ?_ ((hπ.2.2.2 _).2 ⟨u, h3.symm⟩) ((hπ.2.2.2 _).2 ⟨(u⁻¹ : (Ov D v)ˣ), ?_⟩)
  · rwa [χ.map_mul, χ.map_inv, inv_mul_eq_one, eq_comm] at h4
  · have h5 : (1 - e) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 - e := by
      conv_lhs => rw [← hx1, mul_assoc, Units.mul_inv, mul_one]
    rw [Units.val_mul, ← mul_assoc, h5, hd1]
  · rw [map_units_inv, map_units_inv, h3]

theorem chi_detU (he : e * e = e) (hπ : Chart e v π) {V : HSp D} (β : GL (Fin V.rank) (Fv D.host.F v))
    {p : Ov D v} {x : (AE D)ˣ} (hx1 : (1 - e) * (x : AE D) = 1 - e)
    (hx2 : π x = algebraMap (Ov D v) (Fv D.host.F v) p) {χ : (AE D)ˣ →* Circle}
    (hχ : ∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D →
      finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1)
    {g : GA D V} {j : ℕ} {u : (Ov D v)ˣ}
    (hu : (rho V π β g).1.det = algebraMap (Ov D v) (Fv D.host.F v) (p ^ j * u)) :
    χ (detU he V g) = χ x ^ j := by
  have h1 : π (detU he V g : AE D) = π (x ^ j : (AE D)ˣ) * algebraMap (Ov D v) (Fv D.host.F v) u := by
    rw [rho_val, Matrix.det_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul] at hu
    change π (e * (mt V g).det + (1 - e)) = _
    rw [π.map_add, π.map_mul, π.map_sub, π.map_one, hπ.map_e he, one_mul, sub_self, add_zero, RingHom.map_det,
      Units.val_pow_eq_pow_val, π.map_pow, hx2, ← RingHom.map_pow, ← RingHom.map_mul, ← hu]
    rfl
  have h2 : ∀ j : ℕ, (1 - e) * ((x ^ j : (AE D)ˣ) : AE D) = 1 - e := fun j => by
    induction j with
    | zero => rw [pow_zero, Units.val_one, mul_one]
    | succ j ih => rw [pow_succ, Units.val_mul, ← mul_assoc, ih, hx1]
  have h3 : (1 - e) * (e * (mt V g).det + (1 - e)) = 1 - e := one_sub_mul_idem he _
  exact (chi_of_unit (x := x ^ j) (d := detU he V g) hπ (h2 j) h3 hχ h1).trans (χ.map_pow x j)

variable {S T : HSp D}

def phi (π : AE D →+* Fv D.host.F v) (βS : GL (Fin S.rank) (Fv D.host.F v)) (βT : GL (Fin T.rank) (Fv D.host.F v))
    (c : Fv D.host.F v) (u : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) :=
  c • ((βT⁻¹).1 * Matrix.map u π * βS.1)

variable {βS : GL (Fin S.rank) (Fv D.host.F v)} {βT : GL (Fin T.rank) (Fv D.host.F v)} {c : Fv D.host.F v}

theorem phi_sub (u u' : WO S T) : phi π βS βT c (u - u') = phi π βS βT c u - phi π βS βT c u' := by
  rw [phi, phi, phi, Matrix.map_sub _ (map_sub _), Matrix.mul_sub, Matrix.sub_mul, smul_sub]

theorem phi_actO (g : GA D S) (h : GA D T) (u : WO S T) :
    phi π βS βT c (actO S T g⁻¹ h⁻¹ u) = ((rho T π βT h)⁻¹).1 * phi π βS βT c u * (rho S π βS g).1 := by
  rw [← map_inv, rho_val, rho_val, phi, phi, actO, inv_inv, Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βT.1, ← Matrix.mul_assoc βS.1, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel,
    mul_inv_cancel, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.one_mul]

theorem phi_onto (he : e * e = e) (hπ : Chart e v π) (hc : c ≠ 0)
    (y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) : ∃ u : WO S T, IsHalf e u ∧ phi π βS βT c u = y := by
  choose s hs using hπ.1
  refine ⟨e • (βT.1 * (c⁻¹ • y) * (βS⁻¹).1).map s, isHalf_smul he _, ?_⟩
  have : Matrix.map (e • (βT.1 * (c⁻¹ • y) * (βS⁻¹).1).map s) π = βT.1 * (c⁻¹ • y) * (βS⁻¹).1 := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hπ.map_e he, one_mul, Matrix.map_apply, hs]
  rw [phi, this]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (βT⁻¹).1, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel,
    inv_mul_cancel, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, smul_smul, mul_inv_cancel₀ hc,
    one_smul]

variable {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

open Classical in

theorem om_pair [Fintype (ResidueField (Ov D v))] (hW : IsWeilDatumO ψ S T χS χT om) (he : IsSplitIdem D e)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hfix : ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f)
    (hΛ : ∀ u : WO S T, IsHalf e u →
      (u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) ↔ IntM (Ov D v) (phi π βS βT c u)))
    {p : Ov D v} (hp : Irreducible p)
    {U : Matrix (Fin T.rank) (Fin S.rank) (ResidueField (Ov D v)) → WO S T} (hU1 : ∀ w, IsHalf e (U w))
    (hU2 : ∀ w, phi π βS βT c (U w) = yw (Fv D.host.F v) p w)
    {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h)
    (Q : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) → Prop)
    (hQ : ∀ y, IntM (Ov D v) (((rho T π βT h)⁻¹).1 * y * (rho S π βS g).1) ↔ Q y)
    (h1 : ∀ y, IntM (Ov D v) y → Q y)
    (h2 : ∀ y, Q y → IntM (Ov D v) (algebraMap (Ov D v) (Fv D.host.F v) p • y)) :
    om (g, h) f = ((splitFacO χS χT (detU he.1 S g) (detU he.1 T h) : ℂ) *
      ((Real.sqrt (Nat.card {w // Q (yw (Fv D.host.F v) p w)} : ℝ) : ℝ) : ℂ)⁻¹) •
        ∑ w, if Q (yw (Fv D.host.F v) p w) then heisO ψ S T (U w) f else 0 := by
  have hact : ∀ u, IsHalf e u → (actO S T g⁻¹ h⁻¹ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) ↔
      Q (phi π βS βT c u)) := fun u hu => by rw [hΛ _ (isHalf_actO _ _ hu), phi_actO, hQ]
  have hinj : Function.Injective U := fun w w' hw => by
    have e1 : IntM (Ov D v) (algebraMap (Ov D v) (Fv D.host.F v) p • yw (Fv D.host.F v) p w) := by
      rw [yw, smul_smul, mul_inv_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hp.ne_zero), one_smul]
      exact intM_iff.2 ⟨_, rfl⟩
    have e0 : IntM (Ov D v) (0 : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) := fun _ _ => ⟨0, map_zero _⟩
    exact (existsUnique_yw hp e1).unique (by rwa [sub_self]) (by rwa [← hU2, ← hU2, hw, sub_self])
  have := om_eq_sum hW he hf hfix hg hh (isDetAt_detU he.1 S g) (isDetAt_detU he.1 T h)
    (R := (Finset.univ.filter fun w => Q (yw (Fv D.host.F v) p w)).image U) (fun u hu => ?_) (fun u hu hue => ?_)
    fun u hu hue => (hact u hue).2 (h1 _ ((hΛ u hue).1 hu))
  · rw [this, Finset.card_image_of_injective _ hinj, Finset.sum_image fun _ _ _ _ h => hinj h, Finset.sum_filter,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hu
    exact ⟨(hact _ (hU1 w)).2 (by rw [hU2]; exact (Finset.mem_filter.1 hw).2), hU1 w⟩
  · have hq := (hact u hue).1 hu
    obtain ⟨w, hw, hwu⟩ := existsUnique_yw hp (h2 _ hq)
    refine ⟨U w, ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩), ?_⟩, ?_⟩
    · have := ((hQ _).2 hq).sub ((hQ _).2 (h1 _ hw))
      rwa [← Matrix.sub_mul, ← Matrix.mul_sub, sub_sub_cancel, hQ] at this
    · rwa [hΛ _ (isHalf_sub hue (hU1 w)), phi_sub, hU2]
    · rintro _ ⟨hu', hm⟩
      obtain ⟨w', -, rfl⟩ := Finset.mem_image.1 hu'
      rw [hΛ _ (isHalf_sub hue (hU1 w')), phi_sub, hU2] at hm
      rw [hwu w' hm]

end Chart

theorem sum_ite_eq {ι X M : Type} [Fintype X] [AddCommGroup M] [Module ℂ M] (R : Finset ι) (Q : ι → X → Prop)
    [∀ i x, Decidable (Q i x)] (F : X → M) (c : ℂ) :
    ∑ i ∈ R, c • ∑ x, (if Q i x then F x else 0) = c • ∑ x, (Nat.card {i // i ∈ R ∧ Q i x} : ℂ) • F x := by
  rw [← Finset.smul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.card_eq_finsetCard]
  congr 2
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i => Finset.mem_filter)

theorem sum_combine {X M : Type} [Fintype X] [AddCommGroup M] [Module ℂ M] (F : X → M) (A B : ℂ) (hB : B ≠ 0)
    (k : ℕ) (s : Finset ℕ) (N : X → ℕ) (N' : ℕ → X → ℕ) (a b : ℕ → ℕ) (G : ℕ → M)
    (hG : ∀ j ∈ s, G j = B⁻¹ ^ j • ∑ x, (N' j x : ℂ) • F x) (hN : ∀ x, N x = ∑ j ∈ s, a j * b j * N' j x) :
    A⁻¹ ^ k • ∑ x, (N x : ℂ) • F x = ∑ j ∈ s, ((a j : ℂ) * (b j : ℂ) * A⁻¹ ^ k * B ^ j) • G j := by
  conv_rhs => rw [Finset.sum_congr rfl fun j hj => congrArg _ (hG j hj)]
  simp only [hN, Finset.smul_sum, smul_smul, Nat.cast_sum, Nat.cast_mul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
  congr 1
  have : B ^ j * B⁻¹ ^ j = 1 := by rw [← mul_pow, mul_inv_cancel₀ hB, one_pow]
  linear_combination (-((a j : ℂ) * b j * A⁻¹ ^ k * N' j x)) * this

theorem const_eq (z : Circle) (q j m : ℕ) :
    (((z ^ j)⁻¹ : Circle) : ℂ) * ((Real.sqrt ((q ^ (j * m) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ =
      ((z : ℂ) * (Real.sqrt q : ℂ) ^ m)⁻¹ ^ j := by
  have : Real.sqrt ((q ^ (j * m) : ℕ) : ℝ) = Real.sqrt q ^ (j * m) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Nat.cast_nonneg _) (by positivity), ← mul_pow,
      Real.mul_self_sqrt (Nat.cast_nonneg _), Nat.cast_pow]
  rw [this, Circle.coe_inv, Circle.coe_pow, Complex.ofReal_pow, inv_pow, mul_pow, mul_inv, ← pow_mul, mul_comm m j]

set_option maxHeartbeats 1000000 in
open IsLocalRing MeasureTheory in

theorem hecke_identity_split : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (x : (Formalism.L2.Theta.AE D)ˣ) (f : Formalism.IndefR.Datum.WO S T → ℂ) (αS : ℕ → GA D S) (αT : ℕ → GA D T) (RS : ℕ → Finset (GA D S)) (RT : ℕ → Finset (GA D T)) (t : ℕ), Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT om → IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (x : Formalism.L2.Theta.AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → (∀ y : (Formalism.L2.Theta.AE D)ˣ, (1 - e) * (y : Formalism.L2.Theta.AE D) = 1 - e → finPart D (e * (y : Formalism.L2.Theta.AE D)) ∈ intAE D → finPart D (e * ((y⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D)) ∈ intAE D → χS y = 1 ∧ χT y = 1) → Formalism.IndefR.Datum.IsThetaFunO ψ S T f → (∀ u ∈ Formalism.IndefR.Datum.latO S T (L0c D S) (L0c D T) (fun _ => True), Formalism.IndefR.Datum.IsHalf e u ∨ Formalism.IndefR.Datum.IsHalf (cA D e) u → Formalism.IndefR.Datum.heisO ψ S T u f = f) → (∀ j, j ≤ S.rank → IsHeckeElt S e (ϖ : D.host.E) j (αS j) ∧ (∀ γ ∈ RS j, SuppAt e S γ) ∧ IsCosetRep S (locPart S (KsphC S ∅) e) (αS j) (RS j)) → (∀ j, j ≤ T.rank → IsHeckeElt T e (ϖ : D.host.E) j (αT j) ∧ (∀ γ ∈ RT j, SuppAt e T γ) ∧ IsCosetRep T (locPart T (KsphC T ∅) e) (αT j)⁻¹ (RT j)) → (∀ k ∈ locPart S (KsphC S ∅) e, ∀ k' ∈ locPart T (KsphC T ∅) e, om (k, k') f = f) ∧ (T.rank = S.rank + t → ∀ k, k ≤ T.rank → ∑ b ∈ RT k, om (1, b) f = ∑ j ∈ Finset.range (min k S.rank + 1), (((Ideal.absNorm P.asIdeal : ℂ)) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank)⁻¹ ^ k * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank) ^ j) • ∑ a ∈ RS j, om (a, 1) f) ∧ (S.rank = T.rank + t → ∀ k, k ≤ S.rank → ∑ a ∈ RS k, om (a, 1) f = ∑ j ∈ Finset.range (min k T.rank + 1), (((Ideal.absNorm P.asIdeal : ℂ)) ^ ((T.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank)⁻¹ ^ k * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank) ^ j) • ∑ b ∈ RT j, om (1, b) f) := by
  intro D ψ S T χS χT om P e ϖ x f αS αT RS RT t hW hP hϖ hϖ2 hx hχ hf hfix hS hT
  classical
  have he := hP.1
  obtain ⟨v, π, hπ⟩ := GlobalTheory.T.exists_place_chart_of_splitIdempotent e he
  obtain ⟨⟨p, hpϖ, hp⟩, hq⟩ := GlobalTheory.T.splitChart_uniformiser_and_residueCard e P v π hP hπ ϖ hϖ hϖ2
  obtain ⟨βS, hβS⟩ := GlobalTheory.T.exists_splitFrame_selfDualLattice_completion e v π he hπ S
  obtain ⟨βT, hβT⟩ := GlobalTheory.T.exists_splitFrame_selfDualLattice_completion e v π he hπ T
  obtain ⟨c, hc, hΛ⟩ := GlobalTheory.T.mem_homLattice_iff_integralMatrix_splitChart e v π he hπ S T βS βT hβS hβT
  have hq0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have : Finite (ResidueField (Ov D v)) := Nat.finite_of_card_ne_zero (hq ▸ hq0)
  let _ := Fintype.ofFinite (ResidueField (Ov D v))
  choose U hU1 hU2 using fun w : Matrix (Fin T.rank) (Fin S.rank) (ResidueField (Ov D v)) =>
    phi_onto (βS := βS) (βT := βT) he.1 hπ hc (yw (Fv D.host.F v) p w)
  have hx1 : (1 - e) * (x : AE D) = 1 - e := by
    rw [hx]
    exact one_sub_mul_idem he.1 _
  have hx2 : π x = algebraMap (Ov D v) (Fv D.host.F v) p := by
    rw [hx, π.map_add, π.map_mul, π.map_sub, π.map_one, hπ.map_e he.1, one_mul, sub_self, add_zero, hpϖ]
  have cS := fun {V : HSp D} (β : GL (Fin V.rank) (Fv D.host.F v)) {g : GA D V} {j : ℕ} {u : (Ov D v)ˣ} =>
    chi_detU (g := g) (j := j) (u := u) he.1 hπ β hx1 hx2 fun y h1 h2 h3 => (hχ y h1 h2 h3).1
  have cT := fun {V : HSp D} (β : GL (Fin V.rank) (Fv D.host.F v)) {g : GA D V} {j : ℕ} {u : (Ov D v)ˣ} =>
    chi_detU (g := g) (j := j) (u := u) he.1 hπ β hx1 hx2 fun y h1 h2 h3 => (hχ y h1 h2 h3).2
  have d0 : ∀ {n : ℕ} {a : GL (Fin n) (Fv D.host.F v)}, GInt (Ov D v) a →
      ∃ u : (Ov D v)ˣ, a.1.det = algebraMap (Ov D v) (Fv D.host.F v) (p ^ 0 * u) := fun h => by
    simpa only [pow_zero, one_mul] using h.det
  have d1 : ∀ V : HSp D, detU he.1 V 1 = 1 := fun V => Units.ext (by
    change e * (mt V 1).det + (1 - e) = 1
    rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one, mul_one, add_sub_cancel])
  have src : ∀ j, j ≤ S.rank → ∑ a ∈ RS j, om (a, 1) f =
      ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank)⁻¹ ^ j •
        ∑ w, (nKer j w : ℂ) • heisO ψ S T (U w) f := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := hS j hj
    have hα := GlobalTheory.T.heckeElement_component_mem_standardDoubleCoset e v π he hπ S βS hβS _ p j _ hpϖ h1
    have hR := reps_of he hπ hβS h1.2.1 h2 h3
    simp only [← card_heckeCosetReps_integral_right_inversePrime hp hj hα hR]
    rw [← sum_ite_eq]
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨k₁, k₂, g₁, g₂, h4⟩ := hR.1 a ha
    have hk : Hk (Ov D v) p j (rho S π βS a) := h4 ▸ hα.mul g₁ g₂
    obtain ⟨u, hu⟩ := hk.2.2
    rw [om_pair hW he hf hfix hΛ hp hU1 hU2 (h2 a ha) (suppAt_one T) (fun y => IntM (Ov D v) (y * (rho S π βS a).1))
      (fun y => by rw [MonoidHom.map_one, inv_one, Units.val_one, Matrix.one_mul]) (fun y hy => hy.mul hk.1) (fun y hy => ?_),
      card_inversePrimeReps_integral_right_mul_hecke hp hj hk, hq, splitFacO, d1, χS.map_one, mul_one, cT βS hu, const_eq]
    have := hy.mul hk.2.1
    rwa [Matrix.mul_smul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
  have tgt : ∀ j, j ≤ T.rank → ∑ b ∈ RT j, om (1, b) f =
      ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank)⁻¹ ^ j •
        ∑ w, (nKer j wᵀ : ℂ) • heisO ψ S T (U w) f := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := hT j hj
    have hα := GlobalTheory.T.heckeElement_component_mem_standardDoubleCoset e v π he hπ T βT hβT _ p j _ hpϖ h1
    have hR := reps_of he hπ hβT (suppAt_inv h1.2.1) h2 h3
    rw [MonoidHom.map_inv] at hR
    simp only [← count_tgt hp hj hα hR]
    rw [← sum_ite_eq]
    refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨k₁, k₂, g₁, g₂, h4⟩ := hR.1 b hb
    have hk : Hk (Ov D v) p j (rho T π βT b)⁻¹ := by
      rw [h4, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_assoc]
      exact hα.mul g₂.inv g₁.inv
    obtain ⟨u, hu⟩ := hk.2.2
    have h5 : χS (detU he.1 T b) = (χS x ^ j)⁻¹ := by
      rw [← cS βT (g := b⁻¹) (by rw [MonoidHom.map_inv]; exact hu), detU_inv, χS.map_inv, inv_inv]
    rw [om_pair hW he hf hfix hΛ hp hU1 hU2 (suppAt_one S) (h2 b hb)
      (fun y => IntM (Ov D v) (((rho T π βT b)⁻¹).1 * y))
      (fun y => by rw [MonoidHom.map_one, Units.val_one, Matrix.mul_one]) (fun y hy => hk.1.mul hy) (fun y hy => ?_),
      card_tgt hp hj hk, hq, splitFacO, d1, χT.map_one, inv_one, one_mul, h5, const_eq]
    have := hk.2.1.mul hy
    rwa [Matrix.smul_mul, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
  have hne : ∀ (z : Circle) (m : ℕ), (z : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ m ≠ 0 := fun z m =>
    mul_ne_zero z.coe_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2
      (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq0))).ne'))
  refine ⟨fun k hk k' hk' => ?_, fun hr k hk => ?_, fun hr k hk => ?_⟩
  · have g₁ := (GlobalTheory.T.mem_hyperspecial_iff_gInt_of_suppAt_split e v π he hπ S βS hβS k hk.2).1 hk.1
    have g₂ := (GlobalTheory.T.mem_hyperspecial_iff_gInt_of_suppAt_split e v π he hπ T βT hβT k' hk'.2).1 hk'.1
    have hact : ∀ u, IsHalf e u → (actO S T k⁻¹ k'⁻¹ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) ↔
        u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True)) := fun u hu => by
      rw [hΛ _ (isHalf_actO _ _ hu), hΛ _ hu]
      change IntM _ (phi π βS βT c _) ↔ IntM _ (phi π βS βT c _)
      rw [phi_actO]
      refine ⟨fun h => ?_, fun h => (g₂.2.mul h).mul g₁.1⟩
      have := (g₂.1.mul h).mul g₁.2
      rwa [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one,
        ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul] at this
    obtain ⟨u₁, hu₁⟩ := d0 g₁
    obtain ⟨u₂, hu₂⟩ := d0 g₂
    rw [om_eq_sum hW he hf hfix hk.2 hk'.2 (isDetAt_detU he.1 S k) (isDetAt_detU he.1 T k') (R := {0})
      (fun u hu => ?_) (fun u hu hue => ?_) fun u hu hue => (hact u hue).2 hu, splitFacO, cT βS hu₁, cS βT hu₂,
      Finset.sum_singleton, GlobalTheory.SplitScalar.heisO_zero]
    · simp
    · rw [Finset.mem_singleton.1 hu]
      exact ⟨(hact 0 (GlobalTheory.SplitScalar.isHalf_zero e)).2 (zero_mem _), GlobalTheory.SplitScalar.isHalf_zero e⟩
    · exact ⟨0, ⟨Finset.mem_singleton_self _, by rw [sub_zero]; exact (hact u hue).1 hu⟩,
        fun _ h => Finset.mem_singleton.1 h.1⟩
  · rw [tgt k hk, sum_combine _ _ _ (hne (χT x) T.rank) k _ _ (fun j w => nKer j w) _ _ (fun j => ∑ a ∈ RS j, om (a, 1) f)
      (fun j hj => src j (by rw [Finset.mem_range] at hj; omega)) fun w => nKer_eq_sum hr wᵀ]
    simp only [hq, Nat.cast_pow]
  · rw [src k hk, sum_combine _ _ _ (hne (χS x) S.rank) k _ _ (fun j w => nKer j wᵀ) _ _ (fun j => ∑ b ∈ RT j, om (1, b) f)
      (fun j hj => tgt j (by rw [Finset.mem_range] at hj; omega)) fun w => nKer_eq_sum hr w]
    simp only [hq, Nat.cast_pow]

end GlobalTheory.SplitHecke

end
end
