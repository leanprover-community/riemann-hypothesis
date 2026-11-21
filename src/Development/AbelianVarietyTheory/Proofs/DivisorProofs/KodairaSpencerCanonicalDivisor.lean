import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKSSymPairBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadGenericEigenFrameAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellOfIsFrameMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationPreservedByBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorIsCombinationEigenbasisFlagSpacePoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleBigCellCoordinatesFlagSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesLogVectorFieldsDeterminant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopFormFrameBaseCoordinatesAddVariablesEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerComparisonStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalTangentFrameJacobianDetOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFrameChangeBalancedTensorsCmType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section
open scoped Matrix
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LogPole.EigNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

set_option maxHeartbeats 1000000 in
open GlobalTheory.LogKSDiv.Spread GlobalTheory.ShFam.EigSpread GlobalTheory.ShFam.EigLoc GlobalTheory.LieLocBasis in

theorem exists_eigBasis_at (TF : TorFlag Xo c) (p : TF.Y.X) :
    ∃ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
      (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), p ∈ U.1 ∧ IsEigBasis TF U e v := by
  classical
  obtain ⟨U₁, hU₁, hp₁, x₁, hx₁, C, n, xc, hx⟩ := exists_affine_chart TF.Y.t (𝟙 TF.Y.X) p
  let L : Type := TF.Y.X.presheaf.stalk p
  letI : Algebra Γ(TF.Y.X, U₁) L := TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨p, hp₁⟩
  have hloc := hU₁.isLocalization_stalk ⟨p, hp₁⟩
  let ρ₁ : Γ(TF.Y.X, U₁) →+* L := algebraMap _ _
  have hK : spMap ρ₁ ≫ hU₁.fromSpec = TF.Y.X.fromSpecStalk p := by
    rw [← hU₁.fromSpecStalk_eq_fromSpecStalk hp₁]
    rfl
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  haveI : IsIso (spMap (RingHom.id c.F)) := by rw [hid]; infer_instance
  haveI : IsIso (GlobalTheory.Toroidal.genι TF.Y) := inferInstanceAs (IsIso (pullback.fst TF.Y.s (spMap (RingHom.id c.F))))
  have hs : inv (GlobalTheory.Toroidal.genι TF.Y) ≫ GlobalTheory.Toroidal.genStr TF.Y = TF.Y.s := by
    rw [IsIso.inv_comp_eq]
    calc GlobalTheory.Toroidal.genStr TF.Y = GlobalTheory.Toroidal.genStr TF.Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
      _ = GlobalTheory.Toroidal.genι TF.Y ≫ TF.Y.s := pullback.condition.symm
  let φ₀ : c.F →+* L := (Spec.preimage (TF.Y.X.fromSpecStalk p ≫ TF.Y.s)).hom
  have hφ₀ : spMap φ₀ = TF.Y.X.fromSpecStalk p ≫ TF.Y.s := Spec.map_preimage _
  obtain ⟨f₀'⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y L φ₀
    (TF.Y.X.fromSpecStalk p ≫ inv (GlobalTheory.Toroidal.genι TF.Y)) (by rw [Category.assoc, hs, hφ₀])
  have e0 : (TF.Y.X.fromSpecStalk p ≫ inv (GlobalTheory.Toroidal.genι TF.Y)) ≫ GlobalTheory.Toroidal.genι TF.Y =
      TF.Y.X.fromSpecStalk p := by simp
  obtain ⟨f₀⟩ : Nonempty (GlobalTheory.ShFam.EigFrame TF.Y φ₀ (TF.Y.X.fromSpecStalk p)) := e0 ▸ ⟨f₀'⟩
  let φ₁ := cst TF.Y.s U₁
  have hφ₁ : spMap φ₁ = hU₁.fromSpec ≫ TF.Y.s := spMap_cst _ hU₁
  have hρφ : ρ₁.comp φ₁ = φ₀ := spMap_inj (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hK, hφ₀])
  obtain ⟨xcK, hxK, hcK⟩ := vec_bc_of_chart C hx ρ₁ (x' := TF.Y.X.fromSpecStalk p)
    (by rw [hx₁, Category.comp_id, hK])
  obtain ⟨Pr, hPr⟩ := exists_projectors c φ₁ hx
  choose Bv hBv using fun τ i => vec_exists hxK _ (f₀.tan τ i)
  have hBe : ∀ τ i, Bv τ i ∈ eig c φ₀ hxK τ := fun τ i => (vec_eig_iff hxK _ _).1 (by rw [← hBv]; exact f₀.eig τ i)
  have hPK : ∀ τ i, (Pr τ).map ρ₁ *ᵥ Bv τ i = Bv τ i := fun τ i =>
    (hPr ρ₁ hxK hcK τ (Bv τ i)).2 (by rw [hρφ]; exact hBe τ i)
  letI : Algebra c.F L := φ₀.toAlgebra
  have hEig : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c z.1) (Bv z.1 z.2) :=
    fun z => (ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).1 (hBe z.1 z.2)
  have hblk : ∀ τ w, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c τ) w →
      ∃! a : Fin (Dw.mult τ) → L, ∑ i, a i • Bv τ i = w := fun τ w hw => by
    have := f₀.basis τ _ (vec_tan hxK w) ((vec_eig_iff hxK _ w).2 ((ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).2 hw))
    rw [show f₀.v τ = fun i => vec TF.Y.t _ xcK (Bv τ i) from funext (hBv τ)] at this
    simpa only [comb_iff hxK, eq_comm] using this
  have hglob := GlobalTheory.FlagEmb.EigSpread.global_basis (GlobalTheory.FlagEmb.EigSpread.splits c) (fun z => Bv z.1 z.2) hEig hblk
  obtain ⟨hli, hsp⟩ := (GlobalTheory.FlagEmb.EigSpread.existsUnique_iff _).1 hglob
  let bK := Module.Basis.mk hli hsp.ge
  have hcard : Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  have hdet : IsUnit (Matrix.of fun i j => Bv (e.symm j).1 (e.symm j).2 i).det := by
    have h1 : (Matrix.of fun i j => Bv (e.symm j).1 (e.symm j).2 i) =
        (Pi.basisFun L (Fin n)).toMatrix (bK.reindex e) := by
      ext i j
      simp [Module.Basis.toMatrix_apply, bK]
    rw [h1]
    exact Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  obtain ⟨g, hg, s0, B₀, -, hψB⟩ := spread_exact (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal
    (fun j => Bv (e.symm j).1 (e.symm j).2) hdet (fun j => Pr (e.symm j).1) (fun j => hPK _ _)
  have hU : IsAffineOpen (TF.Y.X.basicOpen g) := hU₁.basicOpen g
  have hU' : TF.Y.X.basicOpen g ∈ TF.Y.X.affineOpens := hU
  have hpU : p ∈ TF.Y.X.basicOpen g := by
    rw [Scheme.mem_basicOpen _ _ _ hp₁]
    exact IsLocalization.map_units L (⟨g, hg⟩ : (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal.primeCompl)
  let ψ : Γ(TF.Y.X, U₁) →+* Γ(TF.Y.X, TF.Y.X.basicOpen g) :=
    (TF.Y.X.presheaf.map (homOfLE (TF.Y.X.basicOpen_le g)).op).hom
  have hψg : IsUnit (ψ g) := TF.Y.X.toRingedSpace.isUnit_res_basicOpen g
  obtain ⟨hs0, hdet0, hQ0⟩ := hψB _ ψ hψg
  have hmap : spMap ψ ≫ hU₁.fromSpec = hU.fromSpec := hU₁.map_fromSpec hU _
  obtain ⟨xcU, hxU, hcU⟩ := vec_bc_of_chart C hx ψ (x' := LogKS.chart ⟨_, hU'⟩)
    (by rw [hx₁, Category.comp_id]; exact hmap.symm)
  have hψφ : ψ.comp φ₁ = cst TF.Y.s (TF.Y.X.basicOpen g) := spMap_inj (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hmap, spMap_cst _ hU])
  let u := hs0.unit
  let cU : Fin n → Fin n → Γ(TF.Y.X, TF.Y.X.basicOpen g) := fun j => (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • (ψ ∘ B₀ j)
  have hdetU : IsUnit (Matrix.of fun i j => cU j i).det := by
    have : (Matrix.of fun i j => cU j i) = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • Matrix.of fun i j => ψ (B₀ j i) := by
      ext i j; rfl
    rw [this, Matrix.det_smul]
    exact (u⁻¹.isUnit.pow _).mul hdet0
  have hcUd : ∀ j, cU j = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • (ψ ∘ B₀ j) := fun j => rfl
  clear_value cU
  refine ⟨⟨_, hU'⟩, n, e, fun j => vec TF.Y.t _ xcU (cU j), hpU, fun j => vec_tan hxU _, fun w' hw' => ?_,
    fun a τ i => ?_⟩
  · obtain ⟨cc, rfl⟩ := vec_exists hxU w' hw'
    simp only [comb_iff hxU]
    exact basis_of_det cU hdetU cc
  · have hq := hQ0 (e ⟨τ, i⟩)
    simp only [Equiv.symm_apply_apply] at hq
    have hfix : (Pr τ).map ψ *ᵥ cU (e ⟨τ, i⟩) = cU (e ⟨τ, i⟩) := by
      rw [hcUd, Matrix.mulVec_smul, hq]
    have hmem := (hPr ψ hxU hcU τ (cU (e ⟨τ, i⟩))).1
    rw [hfix, hψφ] at hmem
    have heig : vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU (e ⟨τ, i⟩)) ≫ (TF.Y.t.act.act a).left =
        spMap (epsMul (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a))) ≫
          vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU (e ⟨τ, i⟩)) :=
      (vec_eig_iff hxU (fun a => cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a)) (cU (e ⟨τ, i⟩))).2 hmem a
    have hc : IsCombAtG TF.Y.t (LogKS.chart ⟨_, hU'⟩) (fun j => vec TF.Y.t _ xcU (cU j))
        (Pi.single (e ⟨τ, i⟩) (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a)))
        (vec TF.Y.t _ xcU (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a) • cU (e ⟨τ, i⟩))) := by
      rw [comb_iff hxU, Finset.sum_eq_single (e ⟨τ, i⟩) (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun hk => absurd (Finset.mem_univ _) hk), Pi.single_eq_same]
    rw [vec_smul hxU, ← heig] at hc
    exact hc

end GlobalTheory.LogPole.EigNear

theorem GlobalTheory.LogPole.exists_eigBasis_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ y : Y₀ TF.X Z, ∃ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), toBase TF Z y ∈ U.1 ∧ IsEigBasis TF U e v := by
  intro E _ _ _ H Dw l Xo c TF Z _ y
  exact GlobalTheory.LogPole.EigNear.exists_eigBasis_at TF (toBase TF Z y)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenBasis_near_boundaryFlagSpace_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ y : Y₀ TF.X Z, ∃ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), toBase TF Z y ∈ U.1 ∧ IsEigBasis TF U e v := by
  atlas_forward_decl GlobalTheory.LogPole.exists_eigBasis_near
end

section
namespace GlobalTheory

open Matrix

theorem exists_isUnit_of_isUnit_sum_localRing {R : Type} [CommRing R] [IsLocalRing R]
    {ι : Type} (s : Finset ι) (f : ι → R) (h : IsUnit (∑ i ∈ s, f i)) :
    ∃ i ∈ s, IsUnit (f i) := by
  by_contra hne
  push_neg at hne
  apply (IsLocalRing.mem_maximalIdeal _).mp _ h
  exact Ideal.sum_mem _ fun i hi => (IsLocalRing.mem_maximalIdeal _).mpr (hne i hi)

theorem exists_perm_isUnit_leading_minors_localRing :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R),
      IsUnit M.det → ∃ w : Equiv.Perm (Fin m), ∀ (k : ℕ) (hk : k ≤ m),
        IsUnit ((M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
  intro R _ _ m
  induction m with
  | zero =>
    intro M _
    refine ⟨1, fun k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    simp
  | succ n ih =>
    intro M hM
    rw [Matrix.det_succ_row M (Fin.last n)] at hM
    obtain ⟨j, -, hj⟩ := exists_isUnit_of_isUnit_sum_localRing _ _ hM
    have hN := isUnit_of_mul_isUnit_right hj
    rw [Fin.succAbove_last] at hN
    obtain ⟨v, hv⟩ := ih _ hN
    let f : Fin (n + 1) → Fin (n + 1) := fun i =>
      if h : i = Fin.last n then j else j.succAbove (v (i.castPred h))
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      by_cases ha : a = Fin.last n <;> by_cases hb : b = Fin.last n
      · rw [ha, hb]
      · simp only [ha, hb, dite_true, dite_false] at hab
        exact absurd hab.symm (Fin.succAbove_ne _ _)
      · simp only [ha, hb, dite_true, dite_false] at hab
        exact absurd hab (Fin.succAbove_ne _ _)
      · simp only [ha, hb, dite_false] at hab
        have := v.injective (Fin.succAbove_right_injective hab)
        exact Fin.castPred_inj.mp this
    let w : Equiv.Perm (Fin (n + 1)) :=
      Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
    refine ⟨w, fun k hk => ?_⟩
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hk' : k ≤ n := Nat.lt_succ_iff.mp hlt
      have heq : (M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk) =
          ((M.submatrix Fin.castSucc j.succAbove).submatrix id v).submatrix
            (Fin.castLE hk') (Fin.castLE hk') := by
        ext a b
        have hb : Fin.castLE hk b ≠ Fin.last n := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp only [submatrix_apply, id, w, Equiv.ofBijective_apply, f, hb, dite_false]
        congr 2
        all_goals (ext; simp)
      rw [heq]
      exact hv k hk'
    · obtain rfl : k = n + 1 := le_antisymm hk hge
      have : Fin.castLE hk = id := Fin.castLE_rfl _
      rw [this, Matrix.submatrix_id_id, Matrix.det_permute']
      refine IsUnit.mul ?_ ?_
      · rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [h]
      · rw [Matrix.det_succ_row M (Fin.last n)]
        exact hM

end GlobalTheory
end

section
set_option autoImplicit false

namespace GlobalTheory.ShFam.Cell

open Matrix

variable {R : Type} [CommRing R]

theorem exists_lowInv_mul_upperUni_of_leadingMinors :
    ∀ (n : ℕ) (N : Matrix (Fin n) (Fin n) R),
      (∀ (k : ℕ) (hk : k ≤ n), IsUnit (N.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) →
      ∃ L U : Matrix (Fin n) (Fin n) R, IsLowInv L ∧ (∀ i j, j < i → U i j = 0) ∧ (∀ i, U i i = 1) ∧ N = L * U
  | 0, N, _ => ⟨1, 1, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      by ext i; exact Fin.elim0 i⟩
  | n + 1, N, hN => by
    set P : Matrix (Fin n) (Fin n) R := N.submatrix Fin.castSucc Fin.castSucc with hP
    have hPm : ∀ (k : ℕ) (hk : k ≤ n), IsUnit (P.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
      intro k hk
      have e : P.submatrix (Fin.castLE hk) (Fin.castLE hk)
          = N.submatrix (Fin.castLE (hk.trans (Nat.le_succ n))) (Fin.castLE (hk.trans (Nat.le_succ n))) := by
        ext i j; rfl
      rw [e]; exact hN k _
    obtain ⟨L₀, U₀, ⟨hL₀z, hL₀d⟩, hU₀z, hU₀d, hPLU⟩ := exists_lowInv_mul_upperUni_of_leadingMinors n P hPm
    have hdL₀ : IsUnit L₀.det := by
      rw [Matrix.det_of_lowerTriangular L₀ (fun i j h => hL₀z i j h)]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => hL₀d i)
    have hdU₀ : IsUnit U₀.det := by
      rw [Matrix.det_of_upperTriangular (fun i j h => hU₀z i j h)]
      simp [hU₀d]
    set q : Fin n → R := fun i => N (Fin.castSucc i) (Fin.last n)
    set r : Fin n → R := fun j => N (Fin.last n) (Fin.castSucc j)
    set u : Fin n → R := L₀⁻¹ *ᵥ q with hu
    set l : Fin n → R := r ᵥ* U₀⁻¹ with hl
    set d : R := N (Fin.last n) (Fin.last n) - l ⬝ᵥ u with hd
    have hq : L₀ *ᵥ u = q := by rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdL₀, Matrix.one_mulVec]
    have hr : l ᵥ* U₀ = r := by rw [hl, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdU₀, Matrix.vecMul_one]
    let L : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases d l j) (fun i' => Fin.lastCases 0 (fun j' => L₀ i' j') j) i
    let U : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i' => Fin.lastCases (u i') (fun j' => U₀ i' j') j) i
    have hLz : ∀ i j, i < j → L i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i' =>
        induction j using Fin.lastCases with
        | last => simp [L]
        | cast j' => simpa [L] using hL₀z i' j' (Fin.castSucc_lt_castSucc_iff.1 hij)
    have hLdiag : ∀ i, L i i = Fin.lastCases d (fun i' => L₀ i' i') i := by
      intro i
      induction i using Fin.lastCases with
      | last => simp [L]
      | cast i' => simp [L]
    have hUz : ∀ i j, j < i → U i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j' => simp [U]
      | cast i' =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast j' => simpa [U] using hU₀z i' j' (Fin.castSucc_lt_castSucc_iff.1 hij)
    have hUd : ∀ i, U i i = 1 := by
      intro i
      induction i using Fin.lastCases with
      | last => simp [U]
      | cast i' => simpa [U] using hU₀d i'
    have hNLU : N = L * U := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_one]
          rw [hd]; simp [dotProduct]
        | cast j' =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_zero, add_zero]
          have := congrFun hr j'
          simpa [vecMul, dotProduct, r] using this.symm
      | cast i' =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_one, zero_mul, add_zero]
          have := congrFun hq i'
          simpa [mulVec, dotProduct, q] using this.symm
        | cast j' =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, zero_mul, add_zero]
          have := congrFun (congrFun hPLU i') j'
          simpa [hP, Matrix.mul_apply] using this
    have hdet : IsUnit L.det := by
      have h1 : N.det = L.det * U.det := by rw [hNLU, Matrix.det_mul]
      have h2 : U.det = 1 := by
        rw [Matrix.det_of_upperTriangular (fun i j h => hUz i j h)]; simp [hUd]
      have h3 : N = N.submatrix (Fin.castLE (le_refl (n+1))) (Fin.castLE (le_refl (n+1))) := by
        ext i j; rfl
      have := hN (n+1) le_rfl
      rw [← h3, h1, h2, mul_one] at this
      exact this
    have hdu : IsUnit d := by
      rw [Matrix.det_of_lowerTriangular L (fun i j h => hLz i j h), Fin.prod_univ_castSucc] at hdet
      have := isUnit_of_mul_isUnit_right hdet
      simpa [hLdiag] using this
    refine ⟨L, U, ⟨hLz, fun i => ?_⟩, hUz, hUd, hNLU⟩
    rw [hLdiag i]
    induction i using Fin.lastCases with
    | last => simpa using hdu
    | cast i' => simpa using hL₀d i'

theorem exists_inCell_of_leadingMinors_isUnit {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (w : Equiv.Perm (Fin m))
    (h : ∀ (k : ℕ) (hk : k ≤ m), IsUnit ((M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det) :
    ∃ a, InCell M w a := by
  obtain ⟨L, U, hL, hUz, hUd, hLU⟩ := exists_lowInv_mul_upperUni_of_leadingMinors m (M.submatrix id w) h
  refine ⟨fun p => U p.1.1 p.1.2, L, hL, ?_⟩
  have hU : upMat (fun p : Above m => U p.1.1 p.1.2) = U := by
    ext i j
    unfold upMat
    by_cases hij : i < j
    · rw [dif_pos hij]
    · rw [dif_neg hij]
      by_cases e : i = j
      · subst e; rw [if_pos rfl, hUd]
      · rw [if_neg e, hUz i j (lt_of_le_of_ne (not_lt.1 hij) (Ne.symm e))]
  rw [hU]; exact hLU

end GlobalTheory.ShFam.Cell
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameVector_isCombination_eigenbasis_flagSpace_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z), ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left := by
  first | exact @GlobalTheory.LogPole.isCombAtG_block | exact GlobalTheory.LogPole.isCombAtG_block | (intros; apply GlobalTheory.LogPole.isCombAtG_block <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

open MonObj in

theorem isUnit_det_of_isCombAtG_vecAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z) (σ : E →+* ℂ) (C : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S), (∀ i : Fin (Dw.mult σ), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left) → IsUnit C.det := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv k S _ z hU hk hx σ C hC
  have hxU : spMap (ev (z ≫ toBase TF Z) U.1 hU) ≫ LogKS.chart U = z ≫ toBase TF Z :=
    FlagMod.spMap_ev (z ≫ toBase TF Z) U.2 hU
  have htan : ∀ j, IsTanAtG TF.Y.t (z ≫ toBase TF Z)
      (spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) := fun j => by
    have := GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev (z ≫ toBase TF Z) U.1 hU) (hv.1 (e ⟨σ, j⟩))
    rwa [hxU] at this
  choose B hB using fun j => GlobalTheory.FlagEmb.EigSpread.exists_lf (htan j)
  have hsum : ∀ i, ∑ j, C i j • B j = TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i := fun i => by
    have h := hC i
    simp only [← hB] at h
    exact (GlobalTheory.FlagEmb.EigSpread.comb_lf B (C i) _).1 h
  obtain ⟨Wm, hW⟩ := TF.X.F.uAt_split k (z ≫ inc₀ TF.X Z) hk σ
  let ρ := (Matrix.mulVecLin Wm).comp
    (FlagMod.vec (TF.X.F.M k).toMChart (z ≫ toBase TF Z) (TF.X.F.inM hk hx)).symm.toLinearMap
  have hρ : ∀ i, ρ (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i) = Pi.single i 1 := fun i => by
    funext l
    have h := congrFun (congrFun hW l) i
    rw [Matrix.mul_apply] at h
    simp only [ρ, FlagMod.Frames.vecAt, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    rw [h, Matrix.one_apply, Pi.single_apply]
  let B' : Fin (Dw.mult σ) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (z ≫ toBase TF Z) TF.Y.t.G := fun j => B j
  have hsum' : ∀ i, ∑ j, C i j • B' j = TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i := hsum
  let D : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S := Matrix.of fun j l => ρ (B' j) l
  have hCD : C * D = 1 := by
    ext i l
    have h : ρ (∑ j, C i j • B' j) = ρ (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i) := congrArg ρ (hsum' i)
    rw [hρ, map_sum] at h
    have h2 := congrFun h l
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    have h3 : (if i = l then (1 : S) else 0) = (Pi.single i (1 : S) : Fin (Dw.mult σ) → S) l := by
      rw [Pi.single_apply]
      exact if_congr eq_comm rfl rfl
    rw [Matrix.mul_apply, Matrix.one_apply, h3]
    exact h2
  exact IsUnit.of_mul_eq_one D.det (by rw [← Matrix.det_mul, hCD, Matrix.det_one])

end GlobalTheory.LogPole
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_frame_eigenbasis_block_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z) (σ : E →+* ℂ) (C : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S), (∀ i : Fin (Dw.mult σ), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left) → IsUnit C.det := by
  atlas_forward_decl GlobalTheory.LogPole.isUnit_det_of_isCombAtG_vecAt
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.LogPole.CellNear

theorem vecAt_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (k : TF.X.F.J) {S : Type}
    [CommRing S] {z₁ z₂ : Sp S ⟶ TF.X.YY} (h : z₁ = z₂) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ TF.X.F.U k) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ TF.X.F.U k)
    {x : Sp S ⟶ TF.Y.X} (hx₁ : z₁ ≫ TF.X.π = x) (hx₂ : z₂ ≫ TF.X.π = x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    TF.X.F.vecAt k z₁ h₁ hx₁ σ i = TF.X.F.vecAt k z₂ h₂ hx₂ σ i := by
  subst h; rfl

theorem exists_frameMat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c)
    (U : TF.Y.X.affineOpens) {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (hv : IsEigBasis TF U e v) (k : TF.X.F.J)
    {W₀ : (Y₀ TF.X Z).Opens} (hW₀ : IsAffineOpen W₀) (hW₀U : W₀ ≤ toBase TF Z ⁻¹ᵁ U.1)
    (hW₀k : W₀ ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k) :
    ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W₀),
      (∀ σ, IsUnit (C σ).det) ∧ IsFrameMat TF Z U e v W₀ k C := by
  have hU0 : ⊤ ≤ (FlagMod.tau hW₀ ≫ toBase TF Z) ⁻¹ᵁ U.1 := fun q hq => FlagMod.tau_le hW₀ hW₀U hq
  have hk0 : ⊤ ≤ (FlagMod.tau hW₀ ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun q hq => FlagMod.tau_le hW₀ hW₀k hq
  have hx0 : (FlagMod.tau hW₀ ≫ inc₀ TF.X Z) ≫ TF.X.π = FlagMod.tau hW₀ ≫ toBase TF Z := Category.assoc _ _ _
  obtain ⟨C, hC⟩ := GlobalTheory.T.frameVector_isCombination_eigenbasis_flagSpace_point E H Dw l Xo c TF Z U n e v hv k _ (FlagMod.tau hW₀) hU0 hk0 hx0
  refine ⟨C, fun σ => GlobalTheory.T.isUnit_det_frame_eigenbasis_block_at_point E H Dw l Xo c TF Z U n e v hv k _ (FlagMod.tau hW₀) hU0 hk0 hx0 σ (C σ)
    (hC σ), ?_⟩
  intro S _ z hz hU hk hx σ i
  have hzφ : spMap (ev z W₀ hz) ≫ FlagMod.tau hW₀ = z := FlagMod.spMap_ev z hW₀ hz
  have eb : spMap (ev z W₀ hz) ≫ FlagMod.tau hW₀ ≫ toBase TF Z = z ≫ toBase TF Z := by
    rw [← Category.assoc, hzφ]
  have hb := (GlobalTheory.TanBaseChange.tan_comb_baseChange E H TF.Y.X TF.Y.t _ S (ev z W₀ hz)
    (FlagMod.tau hW₀ ≫ toBase TF Z) (z ≫ toBase TF Z) eb).2 _
    (fun j => spMap (dualMap (ev (FlagMod.tau hW₀ ≫ toBase TF Z) U.1 hU0)) ≫ v (e ⟨σ, j⟩)) (C σ i) _ (hC σ i)
  have e1 : ∀ j, spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v j =
      spMap (dualMap (ev z W₀ hz)) ≫ spMap (dualMap (ev (FlagMod.tau hW₀ ≫ toBase TF Z) U.1 hU0)) ≫ v j := by
    intro j
    rw [← Category.assoc (spMap (dualMap (ev z W₀ hz))), TanBaseChange.spMap_comp_spMap', ← FlagMod.dualMap_comp,
      ← FlagMod.ev_spMap (ev z W₀ hz) (FlagMod.tau hW₀ ≫ toBase TF Z) U.1 hU0 (FlagMod.le_preimage_comp _ hU0),
      FlagMod.ev_congr eb U.1 (FlagMod.le_preimage_comp _ hU0) hU]
  have hz' : ⊤ ≤ (spMap (ev z W₀ hz) ≫ FlagMod.tau hW₀ ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k :=
    FlagMod.le_preimage_comp _ hk0
  have hx' : (spMap (ev z W₀ hz) ≫ FlagMod.tau hW₀ ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z := by
    rw [← eb]; simp only [toBase, Category.assoc]
  have e2 : (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left =
      spMap (dualMap (ev z W₀ hz)) ≫ (tv (TF.X.F.vecAt k (FlagMod.tau hW₀ ≫ inc₀ TF.X Z) hk0 hx0 σ i)).left := by
    rw [← FlagMod.tanPull_left (ev z W₀ hz) eb, FlagMod.Frames.tanPull_vecAt TF.X.F k (ev z W₀ hz) _ hk0 hz' hx0 hx' eb,
      vecAt_congr TF k (by rw [← Category.assoc, hzφ]) hz' hk hx' hx]
  rw [funext fun j => e1 (e ⟨σ, j⟩), e2]
  exact hb

theorem isUnit_prod_univ {R ι : Type} [CommRing R] [Fintype ι] (f : ι → R) (h : ∀ i, IsUnit (f i)) :
    IsUnit (∏ i, f i) :=
  Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => h i

theorem isUnit_of_isUnit_prod_univ {R ι : Type} [CommRing R] [Fintype ι] (f : ι → R) (h : IsUnit (∏ i, f i))
    (i : ι) : IsUnit (f i) :=
  isUnit_of_dvd_unit (Finset.dvd_prod_of_mem f (Finset.mem_univ i)) h

end GlobalTheory.LogPole.CellNear

open GlobalTheory.LogPole.CellNear in

theorem GlobalTheory.LogPole.exists_isCell_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (y : Y₀ TF.X Z), toBase TF Z y ∈ U.1 → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∃ (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsEigBasis TF U e' v ∧ y ∈ W ∧ W ≤ V ∧ IsCell TF Z U e' v W k L N := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv y hyU V hyV
  obtain ⟨k, hk⟩ : ∃ k, inc₀ TF.X Z y ∈ TF.X.F.U k := by
    have : inc₀ TF.X Z y ∈ ⨆ k, TF.X.F.U k := by rw [TF.X.F.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hyW₀, hW₀le⟩ := (Y₀ TF.X Z).isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((V ⊓ toBase TF Z ⁻¹ᵁ U.1 ⊓ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k : (Y₀ TF.X Z).Opens) : Set (Y₀ TF.X Z)) from
      ⟨⟨hyV, hyU⟩, hk⟩) (V ⊓ toBase TF Z ⁻¹ᵁ U.1 ⊓ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k).isOpen
  have hW₀V : W₀ ≤ V := fun q hq => (hW₀le hq).1.1
  have hW₀U : W₀ ≤ toBase TF Z ⁻¹ᵁ U.1 := fun q hq => (hW₀le hq).1.2
  have hW₀k : W₀ ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k := fun q hq => (hW₀le hq).2
  obtain ⟨C, hCu, hC⟩ := exists_frameMat TF Z U e v hv k hW₀ hW₀U hW₀k
  let g := ((Y₀ TF.X Z).presheaf.germ W₀ y hyW₀).hom
  have hperm : ∀ σ : E →+* ℂ, ∃ w : Equiv.Perm (Fin (Dw.mult σ)), ∀ (m : ℕ) (hm : m ≤ Dw.mult σ),
      IsUnit ((((C σ).map g).submatrix id w).submatrix (Fin.castLE hm) (Fin.castLE hm)).det := fun σ =>
    GlobalTheory.exists_perm_isUnit_leading_minors_localRing _ (by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (hCu σ).map g)
  choose p hp using hperm
  let mn : (σ : E →+* ℂ) → Fin (Dw.mult σ + 1) → Γ(Y₀ TF.X Z, W₀) := fun σ m =>
    (((C σ).submatrix id (p σ)).submatrix (Fin.castLE (Nat.lt_succ_iff.mp m.2))
      (Fin.castLE (Nat.lt_succ_iff.mp m.2))).det
  have hmap : ∀ {R' : Type} [CommRing R'] (φ : Γ(Y₀ TF.X Z, W₀) →+* R') (σ : E →+* ℂ) (m : Fin (Dw.mult σ + 1)),
      φ (mn σ m) = ((((C σ).map φ).submatrix id (p σ)).submatrix (Fin.castLE (Nat.lt_succ_iff.mp m.2))
        (Fin.castLE (Nat.lt_succ_iff.mp m.2))).det := by
    intro R' _ φ σ m
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, ← Matrix.submatrix_map]
  let f := ∏ σ, ∏ m, mn σ m
  have hyf : y ∈ (Y₀ TF.X Z).basicOpen f := by
    rw [Scheme.mem_basicOpen _ f y hyW₀]
    show IsUnit (g f)
    rw [map_prod]
    refine isUnit_prod_univ _ fun σ => ?_
    rw [map_prod]
    refine isUnit_prod_univ _ fun m => ?_
    rw [hmap]
    exact hp σ m (Nat.lt_succ_iff.mp m.2)
  have hWW₀ : (Y₀ TF.X Z).basicOpen f ≤ W₀ := (Y₀ TF.X Z).basicOpen_le f
  have hWa : IsAffineOpen ((Y₀ TF.X Z).basicOpen f) := hW₀.basicOpen f
  have hrf : IsUnit (resG (Y₀ TF.X Z) hWW₀ f) := (Y₀ TF.X Z).toRingedSpace.isUnit_res_basicOpen f
  have hrm : ∀ σ m, IsUnit (resG (Y₀ TF.X Z) hWW₀ (mn σ m)) := by
    intro σ m
    rw [map_prod] at hrf
    have h1 := isUnit_of_isUnit_prod_univ _ hrf σ
    rw [map_prod] at h1
    exact isUnit_of_isUnit_prod_univ _ h1 m
  have hLU : ∀ σ : E →+* ℂ, ∃ L N : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, (Y₀ TF.X Z).basicOpen f),
      GlobalTheory.ShFam.Cell.IsLowInv L ∧ (∀ i j, j < i → N i j = 0) ∧ (∀ i, N i i = 1) ∧
        ((C σ).map (resG (Y₀ TF.X Z) hWW₀)).submatrix id (p σ) = L * N := fun σ =>
    GlobalTheory.ShFam.Cell.exists_lowInv_mul_upperUni_of_leadingMinors _ _ fun m hm => by
      have := hrm σ ⟨m, Nat.lt_succ_of_le hm⟩
      rw [hmap] at this
      exact this
  choose L N hL hN hNd hLN using hLU
  refine ⟨permE e p, (Y₀ TF.X Z).basicOpen f, k, L, N, isEigBasis_permE p hv, hyf, hWW₀.trans hW₀V,
    isCell_of_isFrameMat hWa (hWW₀.trans hW₀U) (hWW₀.trans hW₀k) (fun σ => (hL σ).1) (fun σ => (hL σ).2) hN hNd ?_⟩
  have h1 := isFrameMat_mono hWW₀ (isFrameMat_permE p hC)
  have e1 : (fun σ => ((C σ).submatrix id (p σ)).map (resG (Y₀ TF.X Z) hWW₀)) = fun σ => L σ * N σ :=
    funext fun σ => (Matrix.submatrix_map _ _ _ _).symm.trans (hLN σ)
  rw [e1] at h1
  exact h1
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bigCell_chartFrame_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (y : Y₀ TF.X Z), toBase TF Z y ∈ U.1 → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∃ (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsEigBasis TF U e' v ∧ y ∈ W ∧ W ≤ V ∧ IsCell TF Z U e' v W k L N := by
  atlas_forward_decl GlobalTheory.LogPole.exists_isCell_near
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTopFormFrame_base_coordinates_add_variables_etale : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ X) (p' : Y ⟶ Sp k), q ≫ p = p' → ∀ (m D : ℕ), SmoothOfRelativeDimension m p → ∀ (ι : Type) (o : Fin D ≃ Fin m ⊕ ι) (U U' : X.Opens) (hU' : U' ≤ U), IsAffineOpen U → ∀ (W W' : Y.Opens) (hW' : W' ≤ W), IsAffineOpen W → IsAffineOpen W' → ∀ (hWU : W ≤ q ⁻¹ᵁ U), W' ≤ q ⁻¹ᵁ U' → ∀ (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N).Etale → ∀ (x : Fin m → Γ(X, U)), TopForm.IsFrame (TopForm.dOn p fun i => resG X hU' (x i)) → TopForm.IsFrame (TopForm.dOn p' fun a => resG Y hW' (Sum.elim (fun i => (q.appLE U W hWU).hom (x i)) N (o a))) := by
  first | exact @GlobalTheory.TopFrameEt.isFrame_etale | exact GlobalTheory.TopFrameEt.isFrame_etale | (intros; apply GlobalTheory.TopFrameEt.isFrame_etale <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedEquation_pullback_unitLocus_divides_vanishing : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) (ι : Type) [Finite ι] (Vo : X.Opens) (U U' : X.affineOpens) (hU' : U'.1 ≤ U.1) (W : Y.Opens), IsAffineOpen W → ∀ (hWU : W ≤ q ⁻¹ᵁ U.1) (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N).Etale → ∀ (δ : Γ(X, U.1)), (Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal U' = Ideal.span {resG X hU' δ} → (∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 → (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo)) ∧ ∀ (W' : Y.Opens) (hW' : W' ≤ W), W' ≤ q ⁻¹ᵁ U'.1 → ∀ f : Γ(Y, W'), (∀ (z : Y) (hz : z ∈ W'), q z ∉ Vo → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) → ∀ (z : Y) (hz : z ∈ W'), ger z (hW' hz) ((q.appLE U.1 W hWU).hom δ) ∣ ger z hz f := by
  first | exact @GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale | exact GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale | (intros; apply GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole.CellFrames

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

section Tri

variable {K : Type} [Field K] {m : ℕ}

theorem lowerTri_inv (A : Matrix (Fin m) (Fin m) K) (hA : ∀ i j, i < j → A i j = 0) (hd : ∀ i, A i i ≠ 0) :
    (∀ i j, i < j → A⁻¹ i j = 0) ∧ ∀ i, A⁻¹ i i * A i i = 1 := by
  have hB : A.BlockTriangular OrderDual.toDual := fun i j h => hA i j (OrderDual.toDual_lt_toDual.1 h)
  have hdet : IsUnit A.det := by
    rw [Matrix.det_of_lowerTriangular A hB]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have : Invertible A := Matrix.invertibleOfIsUnitDet A hdet
  have hB' := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨fun i j h => hB' (OrderDual.toDual_lt_toDual.2 h), fun i => ?_⟩
  have e := congrFun (congrFun (Matrix.nonsing_inv_mul A hdet) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at e
  · exact e
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA j i h, mul_zero]
    · rw [hB' (OrderDual.toDual_lt_toDual.2 h), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S : Type} [CommRing S] [Algebra c.F S]

theorem frVec_of_comb {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {P P' : FrPt Xo c S}
    (hx : frX P ≫ Y.j = x) (hx' : frX P' ≫ Y.j = x) (e : P'.x = P.x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ))
    (cf : Fin (Dw.mult σ) → S) (h3 : IsCombAt P.x (P.u σ) cf (P'.u σ i)) :
    frVec Y P' hx' σ i = ∑ j, cf j • frVec Y P hx σ j := by
  have eX : frX P' = frX P := xF_ext (frX_snd _) (frX_snd _) (hx'.trans hx.symm)
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev x M.U h) (frX P) (frX_snd P)
    (hx.trans (spMap_ev x M.hU h).symm)
  let Λ : M.Lift (ev x M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have h4 := (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _
      (fun j => (vec M x h).symm (frVec Y P hx σ j)) (P.u σ) _ _ fun j =>
        (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm).1 h3
  have h5 := (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (e ▸ P'.tan σ i)).1 h4
  rw [map_sum] at h5
  simp only [map_smul, LinearEquiv.apply_symm_apply] at h5
  rw [← h5]
  obtain ⟨u, hu⟩ := (toModel_eq_iff _ (frX_fst P') hx' (P'.tan σ i) _).1 rfl
  exact ((toModel_eq_iff _ _ _ _ _).2 ⟨u, eX ▸ hu⟩).symm

end GlobalTheory.LogPole.CellFrames

namespace GlobalTheory.LogPole

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_cellFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (Q : FrPt Xo c K), TF.X.F.ChartFr k (z ≫ inc₀ TF.X Z) hk Q → ∃ (P₀ P : FrPt Xo c K) (t : Ix Dw → Kˣ) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), FrBor t Q P ∧ (∀ σ i, (t (some ⟨σ, i⟩) : K) * ev z W hz (L σ i i) = 1) ∧ GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P ∧ IsBaseFrame TF U e v P₀ hU := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N hC K _ _ z hz hk Q hQ
  obtain ⟨-, hWU, -, hLz, hLu, hNz, hN1, hcomb⟩ := hC
  have hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1 := fun p hp => hWU (hz hp)
  have hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z := Category.assoc _ _ _
  have hQx : frX Q ≫ TF.Y.j = z ≫ toBase TF Z := hQ.over.trans hx
  have hvT : ∀ m, IsTanAtG TF.Y.t (z ≫ toBase TF Z) (spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v m) :=
    fun m => GlobalTheory.LieMet.isTan_map _ (spMap_ev _ U.2 hU) (hv.1 m)
  set Lz : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K := fun σ => (L σ).map (ev z W hz) with hLzd
  set Nz : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K := fun σ => (N σ).map (ev z W hz) with hNzd
  have hLd : ∀ σ i, Lz σ i i ≠ 0 := fun σ i => ((hLu σ i).map (ev z W hz)).ne_zero
  have hLt : ∀ σ i j, i < j → Lz σ i j = 0 := fun σ i j h => by
    show ev z W hz (L σ i j) = 0
    rw [hLz σ i j h, map_zero]
  have hLinv := fun σ => CellFrames.lowerTri_inv (Lz σ) (hLt σ) (hLd σ)
  have hNdet : ∀ σ, IsUnit (Nz σ).det := fun σ => by
    rw [Matrix.det_of_upperTriangular (M := Nz σ) (fun i j h => by
      show ev z W hz (N σ i j) = 0
      rw [hNz σ i j h, map_zero])]
    refine IsUnit.prod_univ_iff.2 fun i => ?_
    show IsUnit (ev z W hz (N σ i i))
    rw [hN1, map_one]; exact isUnit_one
  have hLdet : ∀ σ, IsUnit (Lz σ).det := fun σ => by
    rw [Matrix.det_of_lowerTriangular (Lz σ) (fun i j h => hLt σ i j (OrderDual.toDual_lt_toDual.1 h))]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hLd σ i)
  have hAdet : ∀ σ, IsUnit (Lz σ * Nz σ).det := fun σ => by
    rw [Matrix.det_mul]; exact (hLdet σ).mul (hNdet σ)
  have hA : ∀ σ, Lz σ * Nz σ = (L σ * N σ).map (ev z W hz) := fun σ => Matrix.map_mul.symm
  have hvec : ∀ σ i, frVec TF.Y Q hQx σ i =
      ∑ j, (Lz σ * Nz σ) i j • GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩)) := fun σ i => by
    rw [hQ.frVec_eq hx hQx σ]
    have h1 := hcomb K z hz hU hk hx σ i
    have h2 := (GlobalTheory.LieMet.isComb_iff (fun j => GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩))) _ _).1 h1
    rw [h2, hA]
    rfl
  obtain ⟨P₀, hP₀, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K Q (fun σ => (Lz σ * Nz σ)⁻¹) 1
    (fun σ => (Matrix.isUnit_nonsing_inv_det_iff).2 (hAdet σ))
  obtain ⟨P, hP, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K P₀ Nz 1 hNdet
  rw [Units.val_one] at hP₀ hP
  have hQP := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c K).1 _ _ _ _ _ _ _ hP₀).1 hP
  have hg : (fun σ => Nz σ * (Lz σ * Nz σ)⁻¹) = fun σ => (Lz σ)⁻¹ := funext fun σ => by
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hNdet σ), Matrix.one_mul]
  rw [hg, _root_.mul_one] at hQP
  let t : Ix Dw → Kˣ := fun ix => Option.elim ix 1 fun p => Units.mk0 ((Lz p.1 p.2 p.2)⁻¹) (inv_ne_zero (hLd _ _))
  have hP₀x : frX P₀ ≫ TF.Y.j = z ≫ toBase TF Z := by
    rw [eq_frX Q ((frX_fst P₀).trans hP₀.1) (frX_snd P₀)]; exact hQx
  have hU' : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1 := hP₀x ▸ hU
  refine ⟨P₀, P, t, hU', ?_, fun σ i => ?_, hP, fun σ i => ?_⟩
  · refine (GlobalTheory.Frames.frBor_iff_frChg Q P t).2 ⟨fun σ => (Lz σ)⁻¹, fun σ i j h => (hLinv σ).1 i j h,
      fun σ i => eq_inv_of_mul_eq_one_left ((hLinv σ).2 i), ?_⟩
    show GlobalTheory.Frames.FrChg _ ((1 : Kˣ) : K) Q P
    rw [Units.val_one]
    exact hQP
  · show (Lz σ i i)⁻¹ * Lz σ i i = 1
    exact inv_mul_cancel₀ (hLd σ i)
  · have h0 := CellFrames.frVec_of_comb (TF.X.F.inM hk hx) hQx hP₀x hP₀.1 σ i _ (hP₀.2.1 σ i)
    have hI := Matrix.nonsing_inv_mul _ (hAdet σ)
    have key : frVec TF.Y P₀ hP₀x σ i = GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, i⟩)) := by
      rw [h0]
      simp only [hvec, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      have e2 : ∀ l, (∑ j, (Lz σ * Nz σ)⁻¹ i j * (Lz σ * Nz σ) j l) = (1 : Matrix _ _ K) i l := fun l => by
        rw [← hI, Matrix.mul_apply]
      simp only [e2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e1 : (tv (frVec TF.Y P₀ rfl σ i)).left = (tv (frVec TF.Y P₀ hP₀x σ i)).left := rfl
    rw [e1, key, GlobalTheory.LieMet.left_tanOf, ev_congr hP₀x U.1 hU' hU]

end GlobalTheory.LogPole
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bigCell_framedPoints_triangular_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (Q : FrPt Xo c K), TF.X.F.ChartFr k (z ≫ inc₀ TF.X Z) hk Q → ∃ (P₀ P : FrPt Xo c K) (t : Ix Dw → Kˣ) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), FrBor t Q P ∧ (∀ σ i, (t (some ⟨σ, i⟩) : K) * ev z W hz (L σ i i) = 1) ∧ GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P ∧ IsBaseFrame TF U e v P₀ hU := by
  atlas_forward_decl GlobalTheory.LogPole.exists_cellFrames
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.LogPole

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sp_ext_ev {R S : Type} [CommRing R] [CommRing S] {z z' : Sp S ⟶ Sp R} (h : ⊤ ≤ z ⁻¹ᵁ ⊤)
    (h' : ⊤ ≤ z' ⁻¹ᵁ ⊤) (e : ∀ a, ev z ⊤ h a = ev z' ⊤ h' a) : z = z' := by
  rw [← FlagMod.spMap_ev z (isAffineOpen_top _) h, ← FlagMod.spMap_ev z' (isAffineOpen_top _) h']
  congr 2
  exact RingHom.ext e

theorem ev_spMap_top {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (h : ⊤ ≤ (spMap f) ⁻¹ᵁ ⊤)
    (h₀ : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ ⊤) (a : Γ(Sp R, ⊤)) : ev (spMap f) ⊤ h a = f (ev (𝟙 (Sp R)) ⊤ h₀ a) := by
  have e := FlagMod.ev_spMap f (𝟙 (Sp R)) ⊤ h₀ (by simpa using h)
  rw [FlagMod.ev_congr (Category.comp_id (spMap f)).symm ⊤ h (by simpa using h), e]
  rfl

end GlobalTheory.LogPole

open GlobalTheory.LogPole in

theorem GlobalTheory.LogPole.exists_tanPt_of_logDer : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (K : Type) [Field K] [Algebra c.F K] (P₀ : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), ∃ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) ∧ spMap (FlagTan.red c K).toRingHom ≫ y' = frX P₀ ∧ ∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P₀ ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P₀ ≫ TF.Y.j) U.1 hU (D.1 r)) := by
  intro E _ _ _ H Dw l Xo c TF U D K _ _ P₀ hU
  set φ := ev (frX P₀ ≫ TF.Y.j) U.1 hU with hφ
  let θ : Γ(TF.Y.X, U.1) →+* DualNumber K :=
    { toFun := fun r => TrivSqZeroExt.inl (φ r) + TrivSqZeroExt.inr (φ (D.1 r))
      map_one' := by ext <;> simp
      map_mul' := fun a b => by
        ext
        · simp
        · simp [Derivation.leibniz, smul_eq_mul]; ring
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp <;> ring }
  have hθ : ∀ r, θ r = TrivSqZeroExt.inl (φ r) + TrivSqZeroExt.inr (φ (D.1 r)) := fun _ => rfl
  let z : Sp (DualNumber K) ⟶ TF.Y.X := spMap θ ≫ U.2.fromSpec
  have hred : spMap (FlagTan.red c K).toRingHom ≫ z = frX P₀ ≫ TF.Y.j := by
    have e : (FlagTan.red c K).toRingHom.comp θ = φ := RingHom.ext fun r => by simp [hθ]
    rw [← Category.assoc, spMap_comp_spMap', e]
    exact FlagMod.spMap_ev _ U.2 hU
  have hint : Set.range z ⊆ Set.range TF.Y.j := by
    have h1 : ⊤ ≤ z ⁻¹ᵁ TF.Y.j.opensRange :=
      le_preimage_of_dualNumber _ z _ (by rw [hred]; rintro s -; exact ⟨frX P₀ s, rfl⟩)
    rintro _ ⟨s, rfl⟩
    exact h1 (Set.mem_univ s)
  let y' := IsOpenImmersion.lift TF.Y.j z hint
  have hy' : y' ≫ TF.Y.j = z := IsOpenImmersion.lift_fac _ _ _
  have hzU : ⊤ ≤ z ⁻¹ᵁ U.1 := FlagMod.le_preimage_comp (spMap θ) (FlagMod.tau_le U.2 le_rfl)
  have hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1 := by rw [hy']; exact hzU
  have hevz : ev z U.1 hzU = θ := FlagMod.ev_spMap_tau U.2 θ hzU

  have hjs : TF.Y.j ≫ TF.Y.s = pullback.snd _ _ := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, TF.Y.jQ_over]
    exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)
  have htop : ∀ {S : Type} [CommRing S] (w : Sp S ⟶ Sp c.F), ⊤ ≤ w ⁻¹ᵁ ⊤ := fun _ => fun _ _ => trivial
  have hUs : U.1 ≤ TF.Y.s ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine ⟨y', hU', ?_, ?_, fun r => ?_⟩
  ·
    have e1 : y' ≫ pullback.snd _ _ = z ≫ TF.Y.s := by rw [← hjs, ← Category.assoc, hy']
    rw [e1]
    refine sp_ext_ev (htop _) (htop _) fun a => ?_
    rw [← FlagMod.ev_appLE z TF.Y.s hUs hzU (htop _) a, hevz, hθ]
    have hc : (TF.Y.s.appLE ⊤ U.1 hUs).hom a =
        constFn TF.Y.s U.1 ((Scheme.ΓSpecIso (CommRingCat.of c.F)).hom.hom a) := by
      simp only [constFn]
      congr 1
      simp
    have hD : D.1 ((TF.Y.s.appLE ⊤ U.1 hUs).hom a) = 0 := by rw [hc]; exact D.2.1 _
    rw [hD, map_zero, TrivSqZeroExt.inr_zero, add_zero, hφ,
      FlagMod.ev_appLE (frX P₀ ≫ TF.Y.j) TF.Y.s hUs hU (htop _) a,
      FlagMod.ev_congr (show (frX P₀ ≫ TF.Y.j) ≫ TF.Y.s = spMap (algebraMap c.F K) by
        rw [Category.assoc, hjs, FlagMod.frX_snd]) ⊤ (htop _) (htop _),
      ev_spMap_top _ (htop _) (fun _ _ => trivial), ev_spMap_top _ (htop _) (fun _ _ => trivial), TrivSqZeroExt.algebraMap_eq_inl']
  · rw [← cancel_mono TF.Y.j, Category.assoc, hy', hred]
  · rw [FlagMod.ev_congr hy' U.1 hU' hzU, hevz]
    exact hθ r
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualNumberTangentPoint_of_logarithmicDerivation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (K : Type) [Field K] [Algebra c.F K] (P₀ : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), ∃ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) ∧ spMap (FlagTan.red c K).toRingHom ≫ y' = frX P₀ ∧ ∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P₀ ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P₀ ≫ TF.Y.j) U.1 hU (D.1 r)) := by
  atlas_forward_decl GlobalTheory.LogPole.exists_tanPt_of_logDer
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.LogPole

theorem exists_snd_ev_eq_sum_of_ksIso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (K : Type) [Field K] [Algebra c.F K] (P₀ : FrPt Xo c K), KSIso (psiSet H) P₀ → ∀ (U : TF.Y.X.Opens), ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U → ∃ δ : HIx Dw (psiSet H) → Γ(TF.Y.X, U) → K, ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hy : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → spMap (FlagTan.red c K).toRingHom ≫ y' = frX P₀ → ∀ (M : HIx Dw (psiSet H) → K), FlagTan.IsKS (psiSet H) P₀ (y' ≫ pullback.fst _ _) M → ∀ r, (ev (y' ≫ TF.Y.j) U hy r).snd = ∑ k, M k * δ k r := by
  intro E _ _ _ H Dw l Xo c TF K _ _ P₀ hKS U hU
  obtain ⟨X, hX, hP, hk⟩ := hKS
  let S := TrivSqZeroExt K (HIx Dw (psiSet H) → K)
  obtain ⟨XF, h1, h2⟩ : ∃ XF : Sp S ⟶ Xo.XF c, XF ≫ pullback.fst _ _ = X ∧
      XF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) :=
    ⟨pullback.lift X (spMap (algebraMap c.F S)) (hX.trans (GlobalTheory.DualEval.spMap_comp_ring _ _)),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hred : ∀ M : HIx Dw (psiSet H) → K, spMap (FlagTan.red c K).toRingHom ≫
      spMap (FlagTan.dir c M).toRingHom ≫ XF = frX P₀ := fun M => by
    have e : (FlagTan.red c K).toRingHom.comp (FlagTan.dir c M).toRingHom =
        (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom :=
      RingHom.ext fun a => FlagTan.fst_dir (c := c) M a
    rw [← Category.assoc, ← GlobalTheory.DualEval.spMap_comp_ring, e]
    refine GlobalTheory.FlagMod.eq_frX P₀ (by rw [Category.assoc, h1, hP]) ?_
    rw [Category.assoc, h2, ← GlobalTheory.DualEval.spMap_comp_ring]
    exact congrArg spMap (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).comp_algebraMap
  have hmem : ∀ M : HIx Dw (psiSet H) → K,
      ⊤ ≤ (spMap (FlagTan.dir c M).toRingHom ≫ XF ≫ TF.Y.j) ⁻¹ᵁ U := fun M =>
    le_preimage_of_dualNumber (FlagTan.red c K).toRingHom _ _ (by
      rw [← Category.assoc (spMap (FlagTan.dir c M).toRingHom), ← Category.assoc, hred]
      exact hU)
  refine ⟨fun k r => (ev _ U (hmem (Pi.single k 1)) r).snd, fun y' hy hs hr M hM r => ?_⟩
  have ht : FlagTan.IsTanX P₀ (y' ≫ pullback.fst _ _) := by
    refine ⟨?_, by rw [← Category.assoc, hr, GlobalTheory.FlagMod.frX_fst]⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs]
    exact (GlobalTheory.DualEval.spMap_comp_ring _ _).symm
  have e : y' = spMap (FlagTan.dir c M).toRingHom ≫ XF := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, h1]
      exact ((hk _ ht).2 M).1 hM
    · rw [Category.assoc, h2, hs, ← GlobalTheory.DualEval.spMap_comp_ring]
      exact congrArg spMap (FlagTan.dir c M).comp_algebraMap.symm
  subst e
  exact GlobalTheory.DualEval.evalPt_snd_sum (XF ≫ TF.Y.j) (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom
    (fun k => (FlagTan.dir c (Pi.single k (1 : K))).toRingHom) (FlagTan.dir c M).toRingHom M
    (fun k s => FlagTan.fst_dir (c := c) _ s) (fun s => FlagTan.fst_dir (c := c) _ s)
    (fun s => by
      refine (FlagTan.snd_dir (c := c) M s).trans (Finset.sum_congr rfl fun k _ => ?_)
      rw [mul_comm]
      refine congrArg (M k * ·) ((FlagTan.snd_dir (c := c) (Pi.single k (1 : K)) s).trans ?_).symm
      simp [Pi.single_apply]) U r (hmem M) fun k => hmem _

end GlobalTheory.LogPole
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentDerivative_linear_in_kodairaSpencerMatrix_of_iso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (K : Type) [Field K] [Algebra c.F K] (P₀ : FrPt Xo c K), KSIso (psiSet H) P₀ → ∀ (U : TF.Y.X.Opens), ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U → ∃ δ : HIx Dw (psiSet H) → Γ(TF.Y.X, U) → K, ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hy : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → spMap (FlagTan.red c K).toRingHom ≫ y' = frX P₀ → ∀ (M : HIx Dw (psiSet H) → K), FlagTan.IsKS (psiSet H) P₀ (y' ≫ pullback.fst _ _) M → ∀ r, (ev (y' ≫ TF.Y.j) U hy r).snd = ∑ k, M k * δ k r := by
  atlas_forward_decl GlobalTheory.LogPole.exists_snd_ev_eq_sum_of_ksIso
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogKSDiv.PairEntry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem mem_psiSet_iff (τ : E →+* ℂ) : τ ∈ psiSet H ↔ τ (H.rt : E) = H.rt0 := by
  simp [psiSet]

def pairToH : GlobalTheory.LogKSDiv.PairIx H Dw ≃ HIx Dw (psiSet H) where
  toFun P := ⟨⟨P.1.1, (mem_psiSet_iff _).2 P.1.2⟩, P.2.2, P.2.1⟩
  invFun k := ⟨⟨k.1.1, (mem_psiSet_iff _).1 k.1.2⟩, k.2.2, k.2.1⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem symPair_entry {R : Type} [CommRing R] {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (P : GlobalTheory.LogKSDiv.PairIx H Dw) (k : HIx Dw (psiSet H)) :
    GlobalTheory.LogKSDiv.symPair (R := R) e P (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩) =
      if pairToH P = k then 1 else 0 := by
  obtain ⟨⟨τ, hτ⟩, i, k'⟩ := P
  obtain ⟨⟨σ, hσ⟩, a, b⟩ := k
  have hσ' : σ (H.rt : E) = H.rt0 := (mem_psiSet_iff _).1 hσ
  have h2 : ¬ (e ⟨σ, b⟩ = e ⟨(starRingEnd ℂ).comp τ, k'⟩ ∧ e ⟨conjEmb σ, a⟩ = e ⟨τ, i⟩) := by
    rintro ⟨h, -⟩
    have h5 : σ = (starRingEnd ℂ).comp τ := congrArg Sigma.fst (e.injective h)
    exact GlobalTheory.LogKSDiv.DetChange.conj_off H τ hτ (h5 ▸ hσ')
  simp only [GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
  rw [if_neg h2, add_zero]
  by_cases h : τ = σ
  · subst h
    have key : (e ⟨τ, b⟩ = e ⟨τ, i⟩ ∧ e ⟨conjEmb τ, a⟩ = e ⟨(starRingEnd ℂ).comp τ, k'⟩) ↔
        pairToH (Dw := Dw) ⟨⟨τ, hτ⟩, (i, k')⟩ = ⟨⟨τ, hσ⟩, (a, b)⟩ := by
      simp only [e.apply_eq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩
        have hb : b = i := eq_of_heq (Sigma.mk.inj_iff.1 h1).2
        have ha : a = k' := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
        subst hb ha
        rfl
      · intro h4
        have h5 := (Sigma.mk.inj_iff.1 h4).2
        simp only [heq_iff_eq, Prod.mk.injEq] at h5
        obtain ⟨rfl, rfl⟩ := h5
        exact ⟨rfl, rfl⟩
    exact if_congr key rfl rfl
  · have h3 : ¬ (e ⟨σ, b⟩ = e ⟨τ, i⟩ ∧ e ⟨conjEmb σ, a⟩ = e ⟨(starRingEnd ℂ).comp τ, k'⟩) := by
      rintro ⟨h4, -⟩
      exact h (congrArg Sigma.fst (e.injective h4)).symm
    rw [if_neg h3, if_neg]
    intro h4
    exact h (congrArg (fun x : HIx Dw (psiSet H) => x.1.1) h4)

end GlobalTheory.LogKSDiv.PairEntry

namespace GlobalTheory.LogKSDiv.PairEntry

theorem symPair_horizontal_single : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw), ∃ κ : Fin Dw.dim ≃ HIx Dw (psiSet H), ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (j : Fin Dw.dim) (k : HIx Dw (psiSet H)), f (GlobalTheory.LogKSDiv.symPair (R := R) e (ε j) (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩)) = (Pi.single (κ j) (1 : S) : HIx Dw (psiSet H) → S) k := by
  intro E _ _ _ H Dw ε
  refine ⟨ε.trans pairToH, fun f n e j k => ?_⟩
  rw [symPair_entry, Pi.single_apply, Equiv.trans_apply]
  by_cases h : pairToH (ε j) = k
  · rw [if_pos h, if_pos h.symm, map_one]
  · rw [if_neg h, if_neg (Ne.symm h), map_zero]

end GlobalTheory.LogKSDiv.PairEntry
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedSymmetricPairMatrix_horizontal_single : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw), ∃ κ : Fin Dw.dim ≃ HIx Dw (psiSet H), ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (j : Fin Dw.dim) (k : HIx Dw (psiSet H)), f (GlobalTheory.LogKSDiv.symPair (R := R) e (ε j) (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩)) = (Pi.single (κ j) (1 : S) : HIx Dw (psiSet H) → S) k := by
  atlas_forward_decl GlobalTheory.LogKSDiv.PairEntry.symPair_horizontal_single
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.KSChgDet

theorem ksChg_single_eq_blockDiagonal' {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (K : Type) [Field K] (Φ : Finset (E →+* ℂ))
    (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K) (k l : HIx Dw Φ) :
    FlagTan.ksChg Φ g ((Pi.single l 1 : HIx Dw Φ → K)) k =
      Matrix.blockDiagonal' (fun τ : Φ => Matrix.kroneckerMap (· * ·)
        (g (conjEmb τ.1)).transpose (g τ.1).transpose) k l := by
  obtain ⟨τ, a, b⟩ := k
  obtain ⟨τ', a', b'⟩ := l
  rw [FlagTan.ksChg_apply]
  by_cases h : τ = τ'
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq]
    simp [Matrix.kroneckerMap_apply, Pi.single_apply, Sigma.mk.inj_iff, ite_and]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    simp [Pi.single_apply, Sigma.mk.inj_iff, h]

theorem det_ksChg_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (K : Type) [Field K] (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K),
    (∀ σ, (g σ).det = 1) → ∀ (o : Fin Dw.dim ≃ HIx Dw (psiSet H)),
    (Matrix.of fun i j => FlagTan.ksChg (psiSet H) g ((Pi.single (o j) 1 : HIx Dw (psiSet H) → K)) (o i)).det = 1 := by
  intro E _ _ _ H Dw K _ g hg o
  have hM : (Matrix.of fun i j => FlagTan.ksChg (psiSet H) g ((Pi.single (o j) 1 : HIx Dw (psiSet H) → K)) (o i)) =
      (Matrix.blockDiagonal' (fun τ : psiSet H => Matrix.kroneckerMap (· * ·)
        (g (conjEmb τ.1)).transpose (g τ.1).transpose)).submatrix o o := by
    ext i j
    exact ksChg_single_eq_blockDiagonal' K (psiSet H) g (o i) (o j)
  rw [hM, Matrix.det_submatrix_equiv_self, GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod]
  simp [Matrix.det_kronecker, Matrix.det_transpose, hg]

end GlobalTheory.KSChgDet
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_flagTangentConjugateMatrixChange_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (K : Type) [Field K] (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), (∀ σ, (g σ).det = 1) → ∀ (o : Fin Dw.dim ≃ HIx Dw (psiSet H)), (Matrix.of fun i j => FlagTan.ksChg (psiSet H) g ((Pi.single (o j) 1 : HIx Dw (psiSet H) → K)) (o i)).det = 1 := by
  atlas_forward_decl GlobalTheory.KSChgDet.det_ksChg_eq_one
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogPole

theorem logDet_eq_hor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (s : ℚ), s ≠ 0 → KSCompare TF s → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (b : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), (∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (b j).1 (GlobalTheory.LogKSDiv.symPair e (ε j))) → ∀ (o : Fin Dw.dim ≃ HIx Dw (psiSet H)), ∃ a : ℚ, a ≠ 0 ∧ ∀ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1) (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), (∀ σ, (g σ).det = 1) → GlobalTheory.Frames.FrChg g 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (w : HIx Dw (psiSet H) → FrPt Xo c (DualNumber K)) (hw : ∀ b, ⊤ ≤ (frX (w b) ≫ TF.Y.j) ⁻¹ᵁ U.1), (∀ b, IsDef P (w b) ∧ FlagTan.IsKS (psiSet H) P (w b).x (Pi.single b 1)) → ev (frX P₀ ≫ TF.Y.j) U.1 hU (logDet (fun j => (b j).1) x) = (a : K) * (Matrix.of fun i j => (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd).det := by
  intro E _ _ _ H Dw l Xo c TF s hs hcmp hKS U n e v hv ε b hb o
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.balancedSymmetricPairMatrix_horizontal_single ε
  refine ⟨s ^ Dw.dim * ((Equiv.Perm.sign (κ.trans o.symm) : ℤ) : ℚ), ?_, ?_⟩
  · have : ((Equiv.Perm.sign (κ.trans o.symm) : ℤ) : ℚ) ≠ 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (κ.trans o.symm)) with h | h <;> simp [h]
    exact mul_ne_zero (pow_ne_zero _ hs) this
  intro x K _ _ P₀ P hU g hg hP hB w hw hwk
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.tangentDerivative_linear_in_kodairaSpencerMatrix_of_iso TF K P₀ (hKS K P₀) U.1 hU
  choose y' hy' hsnd hred hev using fun j => GlobalTheory.T.exists_dualNumberTangentPoint_of_logarithmicDerivation TF U (b j) K P₀ hU
  have hKSj : ∀ j, FlagTan.IsKS (psiSet H) P₀ (y' j ≫ pullback.fst _ _)
      (fun k => (s : K) * (Pi.single (κ j) (1 : K) : HIx Dw (psiSet H) → K) k) := by
    intro j
    have := hcmp U n e v hv (b j) _ (hb j) K P₀ hU hB (y' j) (hy' j) (hsnd j) (hev j)
    convert this using 3 with k
    rw [hκ (ev (frX P₀ ≫ TF.Y.j) U.1 hU) n e j k]
  have hL : ∀ i j, ev (frX P₀ ≫ TF.Y.j) U.1 hU ((b j).1 (x i)) = (s : K) * δ (κ j) (x i) := by
    intro i j
    have h1 := hδ (y' j) (hy' j) (hsnd j) (hred j) _ (hKSj j) (x i)
    rw [hev j] at h1
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h1
    rw [h1]
    simp [Pi.single_apply, mul_comm, mul_left_comm]
  have hx : P.x = P₀.x := hP.1
  have hR : ∀ i j, (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd =
      ∑ k, FlagTan.ksChg (psiSet H) g (Pi.single (o j) 1 : HIx Dw (psiSet H) → K) k * δ k (x i) := by
    intro i j
    have hk := (FlagTan.isKS_frChg_iff (psiSet H) g 1 P₀ P hP _ _).1 (hwk (o j)).2
    refine hδ (frX (w (o j))) (hw _) (GlobalTheory.FlagMod.frX_snd _) ?_ _ ?_ (x i)
    · rw [GlobalTheory.FlagMod.frX_frMap (hwk (o j)).1]
      exact GlobalTheory.FlagMod.eq_frX P₀ (by rw [GlobalTheory.FlagMod.frX_fst, hx]) (GlobalTheory.FlagMod.frX_snd P)
    · rw [GlobalTheory.FlagMod.frX_fst]; exact hk
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin Dw.dim) (Fin Dw.dim) K, A = Matrix.of fun i j => δ (o j) (x i) := ⟨_, rfl⟩
  have eL : (ev (frX P₀ ≫ TF.Y.j) U.1 hU).mapMatrix (Matrix.of fun i j => (b j).1 (x i)) =
      (s : K) • A.submatrix id (κ.trans o.symm) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hL, hA]
    simp
  have eR : (Matrix.of fun i j => (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd) =
      A * Matrix.of fun i j => FlagTan.ksChg (psiSet H) g (Pi.single (o j) 1 : HIx Dw (psiSet H) → K) (o i) := by
    ext i j
    rw [Matrix.of_apply, hR, Matrix.mul_apply, ← Equiv.sum_comp o, hA]
    simp only [Matrix.of_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [logDet, RingHom.map_det, eR, Matrix.det_mul, GlobalTheory.T.det_flagTangentConjugateMatrixChange_eq_one K g hg o, mul_one, eL, Matrix.det_smul,
    Matrix.det_permute', Fintype.card_fin]
  push_cast
  ring

end GlobalTheory.LogPole
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logKodairaSpencer_det_eq_const_mul_horizontal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (s : ℚ), s ≠ 0 → KSCompare TF s → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (b : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), (∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (b j).1 (GlobalTheory.LogKSDiv.symPair e (ε j))) → ∀ (o : Fin Dw.dim ≃ HIx Dw (psiSet H)), ∃ a : ℚ, a ≠ 0 ∧ ∀ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1) (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), (∀ σ, (g σ).det = 1) → GlobalTheory.Frames.FrChg g 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (w : HIx Dw (psiSet H) → FrPt Xo c (DualNumber K)) (hw : ∀ b, ⊤ ≤ (frX (w b) ≫ TF.Y.j) ⁻¹ᵁ U.1), (∀ b, IsDef P (w b) ∧ FlagTan.IsKS (psiSet H) P (w b).x (Pi.single b 1)) → ev (frX P₀ ≫ TF.Y.j) U.1 hU (logDet (fun j => (b j).1) x) = (a : K) * (Matrix.of fun i j => (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd).det := by
  atlas_forward_decl GlobalTheory.LogPole.logDet_eq_hor
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

theorem exists_unit_mul {Y : Scheme.{0}} {V : Y.Opens} (y : Y) (hy : y ∈ V) [IsDomain (Y.presheaf.stalk y)]
    (t d : Γ(Y, V)) (h0 : ger y hy t ≠ 0) (h1 : ger y hy t ∣ ger y hy d) (h2 : ger y hy d ∣ ger y hy t) :
    ∃ (V' : Y.Opens) (_ : y ∈ V') (h : V' ≤ V) (b : Γ(Y, V')), (∀ z hz, IsUnit (ger z hz b)) ∧
      resG Y h t = b * resG Y h d := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hu : IsUnit b := by
    refine IsUnit.of_mul_eq_one a (mul_left_cancel₀ h0 ?_)
    calc ger y hy t * (b * a) = (ger y hy t * a) * b := by ring
      _ = ger y hy t * 1 := by rw [← ha, ← hb, mul_one]
  obtain ⟨O, hO, s, rfl⟩ := Y.presheaf.exists_germ_eq b
  have hm : y ∈ V ⊓ O := ⟨hy, hO⟩
  have e : ger y hm (resG Y inf_le_left t) = ger y hm (resG Y inf_le_right s * resG Y inf_le_left d) := by
    rw [map_mul, ger_resG, ger_resG, ger_resG, hb, mul_comm]
  obtain ⟨O', hO', i₁, i₂, e'⟩ := Y.presheaf.germ_eq y _ _ _ _ e
  have l₁ : O' ⊓ Y.basicOpen s ≤ V ⊓ O := inf_le_left.trans i₁.le
  refine ⟨O' ⊓ Y.basicOpen s, ⟨hO', (Y.mem_basicOpen s y hO).2 hu⟩, l₁.trans inf_le_left,
    resG Y (l₁.trans inf_le_right) s, fun z hz => ?_, fun_ext_ger fun z hz => ?_⟩
  · rw [ger_resG]
    exact (Y.mem_basicOpen s z _).1 hz.2
  · have e₂ := congrArg (ger z hz.1) e'
    have a₁ := ger_resG i₁.le z hz.1 (resG Y (inf_le_left : V ⊓ O ≤ V) t)
    have a₂ := ger_resG i₂.le z hz.1 (resG Y (inf_le_right : V ⊓ O ≤ O) s * resG Y (inf_le_left : V ⊓ O ≤ V) d)
    have e₃ := a₁.symm.trans (e₂.trans a₂)
    simp only [map_mul, ger_resG] at e₃ ⊢
    exact e₃

theorem ger_ne_zero {Y : Scheme.{0}} {V O : Y.Opens} (hO : Dense (O : Set Y)) (t : Γ(Y, V))
    (h : ∀ z (hz : z ∈ V), z ∈ O → IsUnit (ger z hz t)) (y : Y) (hy : y ∈ V) : ger y hy t ≠ 0 := by
  intro h0
  obtain ⟨O', hO', i₁, i₂, e'⟩ := Y.presheaf.germ_eq y hy hy t 0 (h0.trans (map_zero _).symm)
  obtain ⟨z, hz, hzO⟩ := hO.inter_open_nonempty O' O'.isOpen ⟨y, hO'⟩
  have e₂ := congrArg (ger z hz) e'
  have a₁ := ger_resG i₁.le z hz t
  have a₂ := ger_resG i₂.le z hz (0 : Γ(Y, V))
  have e₃ := a₁.symm.trans (e₂.trans a₂)
  rw [map_zero] at e₃
  exact (h z _ hzO).ne_zero e₃

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem chartFr_congr {TF : TorFlag Xo c} {K : Type} [Field K] [Algebra c.F K] {k : TF.X.F.J} {z z' : Sp K ⟶ TF.X.YY}
    (e : z = z') {hz : ⊤ ≤ z ⁻¹ᵁ TF.X.F.U k} (hz' : ⊤ ≤ z' ⁻¹ᵁ TF.X.F.U k) {Q : FrPt Xo c K}
    (h : TF.X.F.ChartFr k z hz Q) : TF.X.F.ChartFr k z' hz' Q := by
  subst e; exact h

theorem det_block {K : Type} [Field K] {m : ℕ} (o : Fin m ≃ HIx Dw (psiSet H))
    (G : (Fin m ⊕ VIx Dw) → TIx Dw (psiSet H) → K) (h0 : ∀ i b, G (.inl i) (.inr b) = 0)
    (h1 : (Matrix.of fun a b : VIx Dw => G (.inr a) (.inr b)).det = 1) :
    (Matrix.of fun a b => G (((tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl _))) a) (tanOrd Dw b)).det =
      (Matrix.of fun i j => G (.inl i) (.inl (o j))).det := by
  let e := (tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl (VIx Dw)))
  let A : Matrix (Fin m ⊕ VIx Dw) (Fin m ⊕ VIx Dw) K := Matrix.fromBlocks
    (Matrix.of fun i j => G (.inl i) (.inl (o j))) 0 (Matrix.of fun a j => G (.inr a) (.inl (o j)))
    (Matrix.of fun a b : VIx Dw => G (.inr a) (.inr b))
  have : (Matrix.of fun a b => G (e a) (tanOrd Dw b)) = A.submatrix e e := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply]
    have hb : tanOrd Dw b = Equiv.sumCongr o (Equiv.refl (VIx Dw)) (e b) := by
      simp only [e, Equiv.trans_apply]
      rcases tanOrd Dw b with k | k <;> simp
    rw [hb]
    rcases e a with i | i <;> rcases e b with j | j <;> simp [A, h0]
  rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂, h1, mul_one]

def diagUnit {R : Type} [CommRing R] (L : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) R)
    (h : ∀ σ i, IsUnit (L σ i i)) : Rˣ :=
  ∏ q : Σ σ : E →+* ℂ, Fin (Dw.mult σ), (h q.1 q.2).unit⁻¹ ^ AllWt.exOf Dw (FlagTan.kap Dw) 0 (some q)

theorem map_diagUnit {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (L : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) R) (h : ∀ σ i, IsUnit (L σ i i)) (t : Ix Dw → Kˣ)
    (ht : ∀ σ i, (t (some ⟨σ, i⟩) : K) * φ (L σ i i) = 1) :
    (∏ ix, t ix ^ AllWt.exOf Dw (FlagTan.kap Dw) 0 ix).val = φ (diagUnit L h).val := by
  change _ = (Units.map (φ : R →* K) (diagUnit L h)).val
  congr 1
  rw [diagUnit, map_prod, Fintype.prod_option, FlagMod.exOf_none, zpow_zero, one_mul]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [map_zpow, map_inv]
  congr 1
  exact eq_inv_of_mul_eq_one_left (Units.ext (ht q.1 q.2))

set_option maxHeartbeats 1600000 in

theorem exists_pole (hP : GlobalTheory.CovTop.Hypotheses₂) (TF : TorFlag Xo c) (Z : Comp Xo c) (hF : FnAlgClosed Xo c)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z)
    (V : (Y₀ TF.X Z).Opens) (hy : y ∈ V) :
    ∃ (W : (Y₀ TF.X Z).Opens) (_ : y ∈ W) (_ : W ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι)
      (k : TF.X.F.J) (δ u : Γ(Y₀ TF.X Z, W)),
      W ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k ∧ IsUnit u ∧
      (∀ z (hz : z ∈ W), IsUnit (ger z hz δ) ↔ z ∈ U₀ TF.X Z) ∧
      (∀ (W' : (Y₀ TF.X Z).Opens) (hW' : W' ≤ W) (f : Γ(Y₀ TF.X Z, W')), (∀ z (hz : z ∈ W'), z ∉ U₀ TF.X Z →
        ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) →
        ∀ z (hz : z ∈ W'), ger z (hW' hz) δ ∣ ger z hz f) ∧
      ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) ho hi,
        ev z W hz δ * H0.val (B := LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle
          ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) z
          (i, flagIdx (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) _ k) ho hi ω₀.ω = ev z W hz u := by
  obtain ⟨i, hi⟩ := exists_chart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB y
  obtain ⟨U, n, e₀, v, hyU, hv₀⟩ := GlobalTheory.T.exists_lieEigenBasis_near_boundaryFlagSpace_point E H Dw l Xo c TF Z hF y
  obtain ⟨e, W, k, L, N, hv, hyW, hWV, hc⟩ := GlobalTheory.T.exists_bigCell_chartFrame_eigenbasis E H Dw l Xo c TF Z U n e₀ v hv₀ y hyU V hy
  obtain ⟨ε, b, hb⟩ := GlobalTheory.T.exists_logKS_symPair_basis_alt E H Dw l Xo c TF U n e v _ hv.1 hv.2.1 hv.2.2
  obtain ⟨x, U', hU', hyU', hx, hbd⟩ := GlobalTheory.T.exists_coordinates_logVectorFields_determinant E H Dw l Xo c TF U b _ hyU
  have het := GlobalTheory.T.etale_bigCellCoordinates_flagSpace E H Dw l Xo c TF Z hF U n e v hv W k L N hc
  obtain ⟨s, hs, hcmp⟩ := GlobalTheory.T.kodaira_spencer_comparison hP E H Dw l Xo c TF
  let o : Fin Dw.dim ≃ HIx Dw (psiSet H) :=
    (Fintype.equivFinOfCardEq (FlagTan.card_HIx (FlagTan.isHalf_psiSet H))).symm
  obtain ⟨a, ha, hhor⟩ := GlobalTheory.T.logKodairaSpencer_det_eq_const_mul_horizontal E H Dw l Xo c TF s hs hcmp hKS U n e v hv ε b hb o
  obtain ⟨W', hW'a, hyW', hW'⟩ := Opens.isBasis_iff_nbhd.1 (Y₀ TF.X Z).isBasis_affineOpens
    (show y ∈ W ⊓ (toBase TF Z ⁻¹ᵁ U'.1 ⊓ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i) from ⟨hyW, hyU', hi⟩)
  have hW'W : W' ≤ W := hW'.trans inf_le_left
  have hW'U : W' ≤ toBase TF Z ⁻¹ᵁ U'.1 := hW'.trans (inf_le_right.trans inf_le_left)
  have hW'i : W' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i := hW'.trans (inf_le_right.trans inf_le_right)
  let O := (tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl (VIx Dw)))
  let G : Fin Dw.dim ⊕ VIx Dw → Γ(Y₀ TF.X Z, W) :=
    Sum.elim (fun i => ((toBase TF Z).appLE U.1 W hc.2.1).hom (x i)) (cellCoord N)
  let g : Fin (FlagTan.dimFlag Dw) → Γ(Y₀ TF.X Z, W') := fun a => resG _ hW'W (G (O a))
  have hfr := GlobalTheory.T.isTopFormFrame_base_coordinates_add_variables_etale c.F TF.Y.X (Y₀ TF.X Z) TF.Y.s (toBase TF Z) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str
    ((Category.assoc _ _ _).trans (Category.id_comp _).symm) Dw.dim (FlagTan.dimFlag Dw) TF.smooth (VIx Dw) O U.1 U'.1 hU'
    U.2 W W' hW'W hc.1 hW'a hc.2.1 hW'U (cellCoord N) het x hx
  have hJ : IsUnit ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.jacobian i hW'i g) :=
    ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isUnit_jacobian_iff i hW'a hW'i g).2 hfr
  haveI := TF.smooth
  haveI : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim TF.Y.s
  haveI : IsLocallyNoetherian TF.Y.X := LocallyOfFiniteType.isLocallyNoetherian TF.Y.s
  obtain ⟨r₁, r₂⟩ := GlobalTheory.T.reducedEquation_pullback_unitLocus_divides_vanishing TF.Y.X (Y₀ TF.X Z) (toBase TF Z) (VIx Dw) (LogKS.interior TF.Y) U U' hU' W hc.1 hc.2.1
    (cellCoord N) het _ hbd
  let ac : Γ(Y₀ TF.X Z, W') := algX (str₀ TF.X Z) W' (a : c.F)
  have hac : IsUnit ac := (Ne.isUnit (Rat.cast_ne_zero.2 ha)).map _
  refine ⟨W', hyW', hW'W.trans hWV, i, k,
    resG _ hW'W (((toBase TF Z).appLE U.1 W hc.2.1).hom (logDet (fun j => (b j).1) x)),
    ac * resG _ hW'W (diagUnit L hc.2.2.2.2.1).val * (show Γ(Y₀ TF.X Z, W') from
      (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.jacobian i hW'i g), hW'i, hW'W.trans hc.2.2.1,
    (hac.mul ((Units.isUnit _).map _)).mul hJ, fun z hz => ?_, fun W'' hW'' f hf z hz => ?_, fun K _ z hz ho hi => ?_⟩
  · rw [ger_resG]
    exact r₁ z (hW'W hz) (hW'U hz)
  · rw [ger_resG]
    exact r₂ W'' (hW''.trans hW'W) (hW''.trans hW'U) f hf z hz
  have eM : toFlag (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) = inc₀ TF.X Z := Category.id_comp _
  have hzW := FlagMod.le_preimage_mono hW'W hz
  have hU₀ : ⊤ ≤ z ⁻¹ᵁ U₀ TF.X Z := fun p hp => by
    have := ho hp
    rw [Modif.off_eq] at this
    exact this
  have hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := FlagMod.le_preimage_map _ hc.2.2.1 hzW
  obtain ⟨_, hch⟩ := exists_chartFr (z ≫ inc₀ TF.X Z) hU₀
  obtain ⟨Q, hQ⟩ := hch k hk
  obtain ⟨P₀, P, t, hU, hQP, ht, hP₀, hB⟩ := GlobalTheory.T.exists_bigCell_framedPoints_triangular_frameChange E H Dw l Xo c TF Z U n e v hv W k L N hc K z hzW hk Q hQ
  have ez : z ≫ inc₀ TF.X Z = TF.X.ptY P := FlagMod.FlagCover.eq_ptY (hQ.lies.frBor hQP)
  obtain ⟨w, hw⟩ := (hKS K P).exists_isTanFrame
  have ezM : z ≫ toFlag (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) = z ≫ inc₀ TF.X Z := by rw [eM]
  choose zw hzw hzO using fun b => exists_tanLift (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) (hw.isDef b)
    (ezM.trans ez) ho
  have hzw' : ∀ b, (show Sp (DualNumber K) ⟶ Y₀ TF.X Z from zw b) ≫ inc₀ TF.X Z = TF.X.ptY (w b) := fun b => by
    exact (congrArg (zw b ≫ ·) eM).symm.trans (hzw b)
  have hkM := ezM ▸ hk
  have key := ω₀.isKS K P Q t w z zw i k W' hW'i g hz (fun b => hzO b W' hz) hkM ho hi (chartFr_congr ezM.symm hkM hQ)
    hQP hw hzw
  obtain ⟨v₁, v₂⟩ := GlobalTheory.T.vertical_tangentFrame_jacobian_det_one E H Dw l Xo c TF Z U n e v hv W k L N hc K z hzW P₀ P hU ez hP₀ hB (fun b => w (.inr b))
    (fun b => zw (.inr b)) (fun b => hzO _ W hzW) hw.2 (fun b => hzw' _)
  have eb : ∀ b, (show Sp (DualNumber K) ⟶ Y₀ TF.X Z from zw b) ≫ toBase TF Z = frX (w b) ≫ TF.Y.j := fun b => by
    rw [← Category.assoc, hzw', (TF.X.lies_ptY _).1]
  have hwU : ∀ b, ⊤ ≤ (frX (w b) ≫ TF.Y.j) ⁻¹ᵁ U.1 := fun b =>
    eb b ▸ FlagMod.le_preimage_map _ hc.2.1 (hzO b W hzW)
  have hdet : ∀ σ, ((N σ).map (ev z W hzW)).det = 1 := fun σ => by
    rw [Matrix.det_of_upperTriangular fun i j hij => by rw [Matrix.map_apply, hc.2.2.2.2.2.1 σ i j hij, map_zero]]
    simp [hc.2.2.2.2.2.2.1]
  have hh := hhor x K P₀ P hU _ hdet hP₀ hB (fun b => w (.inl b)) (fun b => hwU _) hw.1
  have eP : z ≫ toBase TF Z = frX P₀ ≫ TF.Y.j := by
    rw [← Category.assoc, ez, (TF.X.lies_ptY _).1,
      FlagMod.eq_frX P₀ ((FlagMod.frX_fst P).trans hP₀.1) (FlagMod.frX_snd P)]
  have hblock := det_block o (fun a b => (ev (zw b) W (hzO b W hzW) (G a)).snd) (fun i b => v₂ b _) v₁
  have e₁ : (Matrix.of fun a b => (TangentOrigin.evalPt (zw (tanOrd Dw b)) W' (hzO _ W' hz) (g a)).snd) =
      Matrix.of fun a b => (ev (zw (tanOrd Dw b)) W (hzO _ W hzW) (G (O a))).snd := by
    ext a b
    exact congrArg TrivSqZeroExt.snd (FlagMod.ev_res _ hW'W _ _ _)
  have e₂ : (Matrix.of fun i j => (ev (zw (.inl (o j))) W (hzO _ W hzW) (G (.inl i))).snd) =
      Matrix.of fun i j => (ev (frX (w (.inl (o j))) ≫ TF.Y.j) U.1 (hwU _) (x i)).snd := by
    ext i j
    exact congrArg TrivSqZeroExt.snd ((FlagMod.ev_appLE _ _ hc.2.1 _ (eb _ ▸ hwU _) _).trans
      (congrArg (· (x i)) (FlagMod.ev_congr (eb _) _ _ _)))
  rw [e₁, hblock, e₂, map_diagUnit (ev z W hzW) L hc.2.2.2.2.1 t ht] at key
  have hca : ev z W' hz ac = (a : K) := by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
    exact map_ratCast ((ev z W' hz).comp (algX (str₀ TF.X Z) W')) a
  rw [FlagMod.ev_res _ hW'W hz hzW, FlagMod.ev_appLE _ _ hc.2.1 _ (eP ▸ hU), FlagMod.ev_congr eP _ _ hU, hh,
    map_mul, map_mul, hca, FlagMod.ev_res _ hW'W hz hzW, mul_assoc, mul_assoc]
  exact congrArg _ ((mul_comm _ _).trans key)

section Main

open ReciprocityTheory.GeometryOfNumbersTheory Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CovTop
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 800000 in

theorem simple_pole : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z), y ∉ U₀ TF.X Z → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∀ (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) → (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) → ∃ (V' : (Y₀ TF.X Z).Opens) (_ : y ∈ V') (hle : V' ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι) (j : (common₀ TF.X Z).J) (u : Γ(Y₀ TF.X Z, V')), V' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ V' ≤ (common₀ TF.X Z).U j ∧ (∀ z (hz : z ∈ V'), IsUnit (ger z hz u)) ∧ ∀ z (hz : z ∈ V') (ho : z ∈ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off) (hc : z ∈ (LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)).U (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j)), ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z (hle hz) t * H0.germ (p := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str) (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j) z ho hc ω₀.ω = ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z hz u := by
  intro hP _ E _ _ _ H Dw l Xo c TF Z hF hKS hV ω₀ y _ V hy t ht₁ ht₂
  obtain ⟨W, hyW, hWV, i, k, δ, u, hi, hk, hu, h₁, h₂, h₃⟩ := exists_pole hP TF Z hF hKS hV ω₀ y V hy
  haveI : IsDomain ((Y₀ TF.X Z).presheaf.stalk y) :=
    haveI := (TF.X.normal (inc₀ TF.X Z y)).1
    MulEquiv.isDomain _ (asIso ((inc₀ TF.X Z).stalkMap y)).commRingCatIsoToRingEquiv.symm.toMulEquiv
  obtain ⟨V', hyV', hV', b, hb, e⟩ := exists_unit_mul y hyW (resG _ hWV t) δ
    (by rw [ger_resG]; exact ger_ne_zero (dense_U₀ TF.X Z) t (fun z hz h => (ht₁ z hz).2 h) y _)
    (by rw [ger_resG]; exact ht₂ W hWV δ (fun z hz h hu => h ((h₁ z hz).1 hu)) y hyW)
    (h₂ W le_rfl _ (fun z hz h hu => h ((ht₁ z (hWV hz)).1 (by rwa [ger_resG] at hu))) y hyW)
  refine ⟨V', hyV', hV'.trans hWV, i, k, b * resG _ hV' u, hV'.trans hi, hV'.trans hk, fun z hz => ?_,
    fun z hz ho hc => ?_⟩
  · rw [map_mul]
    exact (hb z hz).mul ((hu.map _).map _)
  let O : (Y₀ TF.X Z).Opens := ksOpen (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) i k
  let ω : Γ(Y₀ TF.X Z, O) := ω₀.ω.loc (i, flagIdx (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) _ k)
  have e₁ : resG _ (inf_le_left : W ⊓ O ≤ W) δ * resG _ inf_le_right ω = resG _ inf_le_left u := by
    refine FlagMod.ext_ev_field fun K _ p hp => ?_
    have a₁ := FlagMod.le_preimage_mono inf_le_left hp
    have a₂ := FlagMod.le_preimage_mono inf_le_right hp
    rw [map_mul, FlagMod.ev_res p _ hp a₁, FlagMod.ev_res p _ hp a₁, FlagMod.ev_res p _ hp a₂]
    exact h₃ K p a₁ (FlagMod.le_preimage_mono inf_le_left a₂) (FlagMod.le_preimage_mono inf_le_right a₂)
  have hzO : z ∈ O := ⟨ho, hc⟩
  have hm : z ∈ W ⊓ O := ⟨hV' hz, hzO⟩
  have e₂ := congrArg (ger z hm) e₁
  have e₃ := congrArg (ger z hz) e
  simp only [map_mul, ger_resG] at e₂ e₃
  change ger (Y := Y₀ TF.X Z) z _ t * ger (Y := Y₀ TF.X Z) z hzO ω = ger (Y := Y₀ TF.X Z) z hz _
  rw [map_mul, ger_resG, e₃, mul_assoc, e₂]

end Main

end GlobalTheory.LogPole
end
end
