import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CocycleTrivialOnProjectiveCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageIUnionOpensEqRangeFlagCells
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellsFramesTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseFlagBundlePreimageModuli
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointsEqOfSameStepsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnitriangularMulUpperTriangularOfIsUnitLead
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRowPermLeadingMinorsNotMem
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointImageAndFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesFramedPointOfUnitTriangularChart

section
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open Matrix

section Alg

theorem exists_factor_idem {L : Type} [Field L] {n m : ℕ} (e : Matrix (Fin n) (Fin n) L) (he : e * e = e)
    (N : Submodule L (Fin n → L)) (hN : ∀ v, v ∈ N ↔ e.mulVec v = v) (hr : Module.finrank L N = m) :
    ∃ (U : Matrix (Fin n) (Fin m) L) (V : Matrix (Fin m) (Fin n) L), U * V = e ∧ V * U = 1 := by
  classical
  let b : Module.Basis (Fin m) L N := Module.finBasisOfFinrankEq L N hr
  have hmem : ∀ v, e.mulVec v ∈ N := fun v => (hN _).2 (by rw [Matrix.mulVec_mulVec, he])
  let P : (Fin n → L) →ₗ[L] N := e.mulVecLin.codRestrict N hmem
  refine ⟨LinearMap.toMatrix' (N.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ P), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    have : (N.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ P) = e.mulVecLin := by
      apply LinearMap.ext
      intro v
      simp [P, LinearMap.codRestrict_apply]
      rfl
    rw [this]
    exact LinearMap.toMatrix'_toLin' e
  · rw [← LinearMap.toMatrix'_comp]
    have : (b.equivFun.toLinearMap ∘ₗ P) ∘ₗ (N.subtype ∘ₗ b.equivFun.symm.toLinearMap) = LinearMap.id := by
      apply LinearMap.ext
      intro a
      have h1 : P (b.equivFun.symm a : N) = b.equivFun.symm a :=
        Subtype.ext ((hN _).1 (b.equivFun.symm a).2)
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Submodule.coe_subtype, h1,
        LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq]
    rw [this, LinearMap.toMatrix'_id]

theorem sum_minors_of_factor {T : Type} [CommRing T] {n m : ℕ} (U : Matrix (Fin n) (Fin m) T)
    (V : Matrix (Fin m) (Fin n) T) (h : V * U = 1) :
    ∑ S : Set.powersetCard (Fin n) m,
      ((U * V).submatrix (GlobalTheory.subsetEnum S) (GlobalTheory.subsetEnum S)).det = 1 := by
  have h0 := GlobalTheory.det_mul_eq_sum_minors V U
  rw [h, det_one] at h0
  rw [h0]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, det_mul, mul_comm]

theorem det_smul_of_factor {T : Type} [CommRing T] {n m : ℕ} (U : Matrix (Fin n) (Fin m) T)
    (V : Matrix (Fin m) (Fin n) T) (s : Fin m → Fin n) :
    ((U * V).submatrix s s).det • (U * V) =
      (U * V).submatrix id s * ((U * V).submatrix s s).adjugate * (U * V).submatrix s id := by
  rw [Matrix.submatrix_mul _ _ s id s Function.bijective_id, Matrix.submatrix_mul _ _ id id s Function.bijective_id,
    Matrix.submatrix_mul _ _ s id id Function.bijective_id, adjugate_mul_distrib, det_mul]
  simp only [Matrix.submatrix_id_id]
  have e1 : U * V.submatrix id s * ((V.submatrix id s).adjugate * (U.submatrix s id).adjugate) *
      (U.submatrix s id * V) = U * (V.submatrix id s * (V.submatrix id s).adjugate) *
        ((U.submatrix s id).adjugate * U.submatrix s id) * V := by
    simp only [Matrix.mul_assoc]
  rw [e1, mul_adjugate, adjugate_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, mul_comm]

theorem idem_minors {R L : Type} [CommRing R] [Field L] (φ : R →+* L) (hφ : Function.Injective φ) {n m : ℕ}
    (e : Matrix (Fin n) (Fin n) R) (he : e * e = e) (N : Submodule L (Fin n → L))
    (hN : ∀ v, v ∈ N ↔ (e.map φ).mulVec v = v) (hr : Module.finrank L N = m) :
    (∑ S : Set.powersetCard (Fin n) m, (e.submatrix (GlobalTheory.subsetEnum S) (GlobalTheory.subsetEnum S)).det = 1) ∧
      ∀ s : Fin m → Fin n, (e.submatrix s s).det • e = e.submatrix id s * (e.submatrix s s).adjugate *
        e.submatrix s id := by
  obtain ⟨U, V, hUV, hVU⟩ := exists_factor_idem (e.map φ) (by rw [← Matrix.map_mul, he]) N hN hr
  have hdet : ∀ s : Fin m → Fin n, φ (e.submatrix s s).det = ((e.map φ).submatrix s s).det := fun s => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]
  refine ⟨hφ ?_, fun s => Matrix.map_injective hφ ?_⟩
  · rw [map_sum, map_one]
    simp only [hdet, ← hUV]
    exact sum_minors_of_factor U V hVU
  · dsimp only
    have h2 := det_smul_of_factor U V s
    rw [hUV] at h2
    have hs : ((e.submatrix s s).det • e).map φ = φ (e.submatrix s s).det • e.map φ := by
      ext i j; simp
    have ha : (e.submatrix s s).adjugate.map φ = ((e.map φ).submatrix s s).adjugate := by
      rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, Matrix.submatrix_map]
    rw [hs, hdet, h2, Matrix.map_mul, Matrix.map_mul, ← Matrix.submatrix_map, ← Matrix.submatrix_map, ha]

theorem exists_split {R S : Type} [CommRing R] [CommRing S] {n m : ℕ} (e : Matrix (Fin n) (Fin n) R)
    (he : e * e = e) (s : Fin m → Fin n)
    (hid : (e.submatrix s s).det • e = e.submatrix id s * (e.submatrix s s).adjugate * e.submatrix s id)
    (φ : R →+* S) (hu : IsUnit (φ (e.submatrix s s).det)) :
    ∃ (u : Matrix (Fin n) (Fin m) S) (w : Matrix (Fin m) (Fin n) S), w * u = 1 ∧ u * w = e.map φ := by
  refine ⟨(e.submatrix id s).map φ,
    (hu.unit⁻¹ : Sˣ).val • ((e.submatrix s s).adjugate * e.submatrix s id).map φ, ?_, ?_⟩
  · have h1 : e.submatrix s id * e.submatrix id s = e.submatrix s s := by
      rw [← Matrix.submatrix_mul _ _ s id s Function.bijective_id, he]
    rw [Matrix.smul_mul, ← Matrix.map_mul, Matrix.mul_assoc, h1, adjugate_mul]
    have hs : ((e.submatrix s s).det • (1 : Matrix (Fin m) (Fin m) R)).map φ =
        φ (e.submatrix s s).det • (1 : Matrix (Fin m) (Fin m) S) := by
      ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [hs, smul_smul, IsUnit.val_inv_mul, one_smul]
  · rw [Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.mul_assoc, ← hid]
    have hs : ((e.submatrix s s).det • e).map φ = φ (e.submatrix s s).det • e.map φ := by
      ext i j; simp
    rw [hs, smul_smul, IsUnit.val_inv_mul, one_smul]

end Alg

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pm_minors (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (M : MChart Y) (σ : E →+* ℂ) :
    LowRank.pm p M σ * LowRank.pm p M σ = LowRank.pm p M σ ∧
    (∑ S : Set.powersetCard (Fin M.n) (Dw.mult σ),
      ((LowRank.pm p M σ).submatrix (GlobalTheory.subsetEnum S) (GlobalTheory.subsetEnum S)).det = 1) ∧
      ∀ s : Fin (Dw.mult σ) → Fin M.n, ((LowRank.pm p M σ).submatrix s s).det • LowRank.pm p M σ =
        (LowRank.pm p M σ).submatrix id s * ((LowRank.pm p M σ).submatrix s s).adjugate *
          (LowRank.pm p M σ).submatrix s id := by
  obtain ⟨L, _, _, y, h, hy, hi⟩ := LowRank.genIn_id Y M
  obtain ⟨h1, h2⟩ := LowRank.pm_gen p M σ hy h
  have he : LowRank.pm p M σ * LowRank.pm p M σ = LowRank.pm p M σ :=
    Matrix.map_injective hi (Matrix.map_mul.trans h2)
  obtain ⟨Λ⟩ := MChart.nonempty_lift E H Dw l Xo c c.F (RingHom.id c.F) Y M L (ev _ M.U h) y hy
    (spMap_ev _ M.hU h).symm
  let N : Submodule L (Fin M.n → L) := Module.End.eigenspace ((LowRank.pm p M σ).map (ev _ M.U h)).mulVecLin 1
  have hN : ∀ v, v ∈ N ↔ ((LowRank.pm p M σ).map (ev _ M.U h)).mulVec v = v := fun v =>
    Module.End.mem_eigenspace_iff.trans (by rw [one_smul]; rfl)
  exact ⟨he, idem_minors _ hi _ he N hN
    (finrank_chart_eig E H Dw l Xo c c.F (RingHom.id c.F) Y M L _ _ Λ σ N fun v => (hN v).trans (h1 v).symm)⟩

theorem exists_eCh_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (M : GChart Y)
    (x : Y.X), x ∈ M.U → ∀ W : Y.X.Opens, x ∈ W → ∃ k : ECh Y p, k.M = M ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ W := by
  intro E _ _ _ H Dw l Xo c Y p M x hx W hW
  classical
  have ex : ∀ σ : E →+* ℂ, ∃ s : Fin (Dw.mult σ) → Fin M.n,
      Y.X.evaluation M.U x hx ((LowRank.pm p M.toMChart σ).submatrix s s).det ≠ 0 := fun σ => by
    by_contra h
    push_neg at h
    have := congrArg (Y.X.evaluation M.U x hx) (pm_minors Y p M.toMChart σ).2.1
    rw [map_sum, map_one, Finset.sum_eq_zero fun S _ => h _] at this
    exact zero_ne_one this
  choose s hs using ex
  let d := fun σ => ((LowRank.pm p M.toMChart σ).submatrix (s σ) (s σ)).det
  have hxf : x ∈ Y.X.basicOpen (∏ σ, d σ) := by
    refine (Y.X.evaluation_ne_zero_iff_mem_basicOpen x hx _).1 ?_
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun σ _ => hs σ
  obtain ⟨g, hg, hxg⟩ := M.hU.exists_basicOpen_le (V := W ⊓ Y.X.basicOpen (∏ σ, d σ)) ⟨x, hW, hxf⟩ hx
  have hle : Y.X.basicOpen g ≤ M.U := Y.X.basicOpen_le g
  have hVf : Y.X.basicOpen g ≤ Y.X.basicOpen (∏ σ, d σ) := hg.trans inf_le_right
  have hf : IsUnit (resG Y.X hle (∏ σ, d σ)) := by
    have h1 : IsUnit (resG Y.X (Y.X.basicOpen_le (∏ σ, d σ)) (∏ σ, d σ)) :=
      RingedSpace.isUnit_res_basicOpen Y.X.toRingedSpace _
    have h2 : resG Y.X hle (∏ σ, d σ) = resG Y.X hVf (resG Y.X (Y.X.basicOpen_le (∏ σ, d σ)) (∏ σ, d σ)) := by
      simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    rw [h2]
    exact h1.map _
  have hu : ∀ σ, IsUnit (resG Y.X hle (d σ)) := fun σ =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem d (Finset.mem_univ σ))) hf
  choose u w hwu huw using fun σ => exists_split _ (pm_minors Y p M.toMChart σ).1 (s σ)
    ((pm_minors Y p M.toMChart σ).2.2 (s σ)) (resG Y.X hle) (hu σ)
  exact ⟨⟨M, Y.X.basicOpen g, hle, u, w, hwu, huw⟩, rfl, hxg, M.hU.basicOpen g, hg.trans inf_le_left⟩

end Geo

end GlobalTheory.FlagMod.FieldFlag
end
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenChart_affineOpen_within : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (M : GChart Y) (x : Y.X), x ∈ M.U → ∀ W : Y.X.Opens, x ∈ W → ∃ k : ECh Y p, k.M = M ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ W := by
  atlas_forward_decl GlobalTheory.FlagMod.FieldFlag.exists_eCh_le
end

section
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem valF_eq_ev {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) (V : X.Opens) (hV : ⊤ ≤ w ⁻¹ᵁ V)
    (f : Γ(X, V)) : valF w V f = ev w V hV f :=
  GlobalTheory.Points.valR_eq w V hV f

theorem map_valF_eq_ev {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) (V : X.Opens) (hV : ⊤ ≤ w ⁻¹ᵁ V)
    {m n : Type} (A : Matrix m n Γ(X, V)) : A.map (valF w V) = A.map (ev w V hV) := by
  ext i j
  exact valF_eq_ev w V hV _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)}

def trA {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) : Matrix (Fin (N + 1)) (Fin k.M.n) Γ(Y.X, k.V) :=
  (A₀.map (resG Y.X hV)).submatrix id (finCongr (congrArg (fun M : GChart Y => M.n) hk))

def trC {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (C₀ : Matrix (Fin M₀.n) (Fin (N + 1)) Γ(Y.X, U)) : Matrix (Fin k.M.n) (Fin (N + 1)) Γ(Y.X, k.V) :=
  (C₀.map (resG Y.X hV)).submatrix (finCongr (congrArg (fun M : GChart Y => M.n) hk)) id

theorem trC_mul_trA {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) (C₀ : Matrix (Fin M₀.n) (Fin (N + 1)) Γ(Y.X, U))
    (h : C₀ * A₀ = 1) : trC hk hV C₀ * trA hk hV A₀ = 1 := by
  subst hk
  ext i j
  have := congrArg (fun A => resG Y.X hV (A i j)) h
  simp only [Matrix.mul_apply, map_sum, map_mul] at this
  simp only [trC, trA, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply, Fin.cast_eq_self, id]
  rw [this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem tw_tr [IsReduced Y.X] {k k' : ECh Y p} {M₀ M₀' : GChart Y} (hk : k.M = M₀) (hk' : k'.M = M₀')
    {U U' : Y.X.Opens} (hV : k.V ≤ U) (hV' : k'.V ≤ U') (hUM : U ⊓ U' ≤ M₀'.U ⊓ M₀.U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) (A₀' : Matrix (Fin (N + 1)) (Fin M₀'.n) Γ(Y.X, U'))
    (g : Γ(Y.X, U ⊓ U')ˣ)
    (H : ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ⊤ ≤ w ⁻¹ᵁ U → ⊤ ≤ w ⁻¹ᵁ U' →
      A₀.map (valF w _) = valF w _ g.val • (A₀'.map (valF w _) * (chg M₀'.toMChart M₀.toMChart).map (valF w _)))
    (S : Type) [CommRing S] (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ k.V) (h' : ⊤ ≤ x ⁻¹ᵁ k'.V)
    (hM : ⊤ ≤ x ⁻¹ᵁ (k'.M.U ⊓ k.M.U)) :
    ∃ a : Sˣ, (trA hk hV A₀).map (ev x _ h) =
      (a : S) • ((trA hk' hV' A₀').map (ev x _ h') * (chg k'.M.toMChart k.M.toMChart).map (ev x _ hM)) := by
  subst hk hk'
  have key : ∀ r j, resG Y.X (inf_le_left : U ⊓ U' ≤ U) (A₀ r j) =
      g.val * ∑ t, resG Y.X inf_le_right (A₀' r t) * resG Y.X hUM (chg k'.M.toMChart k.M.toMChart t j) := by
    intro r j
    refine GlobalTheory.TwistEmb.eq_of_valR fun K _ w hw => ?_
    have hw1 := le_preimage_mono inf_le_left hw
    have hw2 := le_preimage_mono inf_le_right hw
    have hw3 := le_preimage_mono hUM hw
    have e := congrFun (congrFun (H K w hw1 hw2) r) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, valF_eq_ev w U hw1,
      valF_eq_ev w U' hw2, valF_eq_ev w _ hw, valF_eq_ev w _ hw3] at e
    show valF w _ _ = valF w _ _
    rw [valF_eq_ev w _ hw, valF_eq_ev w _ hw, ev_res w _ hw hw1, e, map_mul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, ev_res w _ hw hw2, ev_res w _ hw hw3]
  have hx : ⊤ ≤ x ⁻¹ᵁ (U ⊓ U') := GlobalTheory.TwistEmb.le_inf' x (le_preimage_mono hV h) (le_preimage_mono hV' h')
  refine ⟨Units.map (ev x _ hx).toMonoidHom g, ?_⟩
  ext r j
  simp only [trA, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.submatrix_apply, finCongr_apply,
    Fin.cast_eq_self, id, smul_eq_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [ev_res x hV h (le_preimage_mono hV h), ← ev_res x inf_le_left hx (le_preimage_mono hV h), key, map_mul,
    map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, ev_res x inf_le_right hx (le_preimage_mono hV' h'), ev_res x hV' h' (le_preimage_mono hV' h'),
    ev_res x hUM hx hM]

theorem exists_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)),
    PushInvertible Y.t.G Y.t.PP.L → Nonempty (Atlas Y p) := by
  intro E _ _ _ H Dw l Xo c Y p hP
  classical
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsReduced Y.X := by
    have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
      have := (Y.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨L, N, σ, A, C, haff, hle, hCA, htw⟩ := GlobalTheory.TwistEmb.exists_twist_embedding c.F Y.X Y.s (GChart Y)
    (fun j => j.U) (fun j => j.n) (fun j j' => chg j.toMChart j'.toMChart) Y.proj
    (fun x => exists_gChart hP x)
    (fun K _ w j hw => by
      have hh : ⊤ ≤ w ⁻¹ᵁ (j.U ⊓ j.U) := GlobalTheory.TwistEmb.le_inf' w hw hw
      show (chg j.toMChart j.toMChart).map (valF w (j.U ⊓ j.U)) = 1
      rw [map_valF_eq_ev w _ hh, chg_map _ _ w hw hw hh, Module.Basis.toMatrix_self])
    (fun K _ w j j' j'' h1 h2 h3 => by
      show (chg j.toMChart j'.toMChart).map (valF w (j.U ⊓ j'.U)) *
        (chg j'.toMChart j''.toMChart).map (valF w (j'.U ⊓ j''.U)) =
        (chg j.toMChart j''.toMChart).map (valF w (j.U ⊓ j''.U))
      rw [map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h2), map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h2 h3),
        map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h3), chg_map _ _ w h1 h2, chg_map _ _ w h2 h3,
        chg_map _ _ w h1 h3, Module.Basis.toMatrix_mul_toMatrix])
  have hcovL : ∀ x : Y.X, ∃ i, x ∈ L.U i := fun x => exists_chart L.isLB x
  have hk : ∀ x : Y.X, ∃ i, ∃ k : ECh Y p, k.M = σ i ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ L.U i := fun x => by
    obtain ⟨i, hi⟩ := hcovL x
    obtain ⟨k, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_eigenChart_affineOpen_within E H Dw l Xo c Y p (σ i) x (hle i hi) (L.U i) hi
    exact ⟨i, k, h1, h2, h3, h4⟩
  choose ix kx hkM hxk haffk hlek using hk
  have hc : IsCompact (Set.univ : Set Y.X) := by
    have e : (Set.univ : Set Y.X) = ⋃ i, ((L.U i : Y.X.Opens) : Set Y.X) :=
      (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (hcovL x)).symm
    rw [e]
    exact isCompact_iUnion fun i => (haff i).isCompact
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x => ((kx x).V : Set Y.X)) (fun x => (kx x).V.isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxk x⟩)
  have hUM : ∀ i i', L.U i ⊓ L.U i' ≤ (σ i').U ⊓ (σ i).U := fun i i' =>
    le_inf (inf_le_right.trans (hle i')) (inf_le_left.trans (hle i))
  exact ⟨{
    B := t
    fin := inferInstance
    k := fun b => kx b.1
    aff := fun b => haffk b.1
    cov := fun x => by
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
      exact ⟨⟨z, hz⟩, hxz⟩
    N := N
    A := fun b => trA (hkM b.1) (hlek b.1) (A (ix b.1))
    C := fun b => trC (hkM b.1) (hlek b.1) (C (ix b.1))
    CA := fun b => trC_mul_trA _ _ _ _ (hCA _)
    tw := fun S _ x b b' h h' hM => tw_tr (hkM b.1) (hkM b'.1) (hlek b.1) (hlek b'.1) (hUM _ _) (A (ix b.1))
      (A (ix b'.1)) (L.g (ix b.1) (ix b'.1)) (fun K _ w hw hw' => htw K w _ _ hw hw') S x h h' hM }⟩

end GlobalTheory.FlagMod.FieldFlag
end
end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenbundleFrameAffineAtlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)), PushInvertible Y.t.G Y.t.PP.L → Nonempty (Atlas Y p) := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.exists_atlas | exact GlobalTheory.FlagMod.FieldFlag.exists_atlas | (intros; apply GlobalTheory.FlagMod.FieldFlag.exists_atlas <;> assumption)
end

section
section
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_embK_ne {σ σ' : E →+* ℂ} (h : σ ≠ σ') : ∃ a : 𝓞 E, embK c σ a ≠ embK c σ' a := by
  by_contra hc
  push_neg at hc
  refine h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_))
  have := congrArg Subtype.val (hc a)
  simpa [embK, embF] using this

theorem pm_mul_pm {Y : Model Xo c (RingHom.id c.F)} (p : Proj (RingHom.id c.F)) (M : MChart Y) {σ σ' : E →+* ℂ}
    (h : σ ≠ σ') : LowRank.pm p M σ * LowRank.pm p M σ' = 0 := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.Reg.MChart.exists_ringHom_rho E H Dw l Xo c c.F (RingHom.id c.F) Y M
  letI : Algebra c.F Γ(Y.X, M.U) := (str (tau M.hU)).toAlgebra
  have hP : ∀ τ, LowRank.pm p M τ =
      ∑ k, algebraMap c.F Γ(Y.X, M.U) (RingHom.id c.F (p.κ τ k)) • ρ (p.a τ k) :=
    fun τ => by simp only [LowRank.pm, hρ]; rfl
  obtain ⟨a, ha⟩ := exists_embK_ne (c := c) h
  have h1 := (p.spec σ Γ(Y.X, M.U) M.n ρ).1 a
  have h1' := (p.spec σ' Γ(Y.X, M.U) M.n ρ).1 a
  rw [← hP] at h1 h1'
  have hc : ρ a * LowRank.pm p M σ = LowRank.pm p M σ * ρ a := by
    rw [hP, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, mul_comm]
  have e1 : ρ a * (LowRank.pm p M σ * LowRank.pm p M σ') =
      algebraMap c.F Γ(Y.X, M.U) (embK c σ a) • (LowRank.pm p M σ * LowRank.pm p M σ') := by
    rw [← Matrix.mul_assoc, h1, Matrix.smul_mul]
  have e2 : ρ a * (LowRank.pm p M σ * LowRank.pm p M σ') =
      algebraMap c.F Γ(Y.X, M.U) (embK c σ' a) • (LowRank.pm p M σ * LowRank.pm p M σ') := by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, h1', Matrix.mul_smul]
  have hd : embK c σ a - embK c σ' a ≠ 0 := sub_ne_zero.2 ha
  have e3 : algebraMap c.F Γ(Y.X, M.U) (embK c σ a - embK c σ' a) •
      (LowRank.pm p M σ * LowRank.pm p M σ') = 0 := by
    rw [map_sub, sub_smul, ← e1, ← e2, sub_self]
  calc LowRank.pm p M σ * LowRank.pm p M σ'
      = algebraMap c.F Γ(Y.X, M.U) ((embK c σ a - embK c σ' a)⁻¹ * (embK c σ a - embK c σ' a)) •
        (LowRank.pm p M σ * LowRank.pm p M σ') := by
        rw [inv_mul_cancel₀ hd, map_one, one_smul]
    _ = 0 := by rw [map_mul, mul_smul, e3, smul_zero]

theorem eCh_w_mul_u {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} (k : ECh Y p) {σ σ' : E →+* ℂ}
    (h : σ ≠ σ') : k.w σ * k.u σ' = 0 := by
  calc k.w σ * k.u σ' = (k.w σ * k.u σ) * k.w σ * (k.u σ' * (k.w σ' * k.u σ')) := by
        rw [k.wu, k.wu, Matrix.one_mul, Matrix.mul_one]
    _ = k.w σ * ((k.u σ * k.w σ) * (k.u σ' * k.w σ')) * k.u σ' := by simp only [Matrix.mul_assoc]
    _ = 0 := by
        rw [k.uw, k.uw, ← Matrix.map_mul, pm_mul_pm p _ h, Matrix.map_zero _ (map_zero _), Matrix.mul_zero,
          Matrix.zero_mul]

end GlobalTheory.FlagMod.FieldFlag

open GlobalTheory.FlagMod.FieldFlag MonoidalCategory CartesianMonoidalCategory MonObj in

theorem GlobalTheory.FlagMod.FieldFlag.atlas_isCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p), IsCover (RingHom.id c.F) Y.s A.V A.alpha A.cv A.Dv := by
  intro E _ _ _ H Dw l Xo c Y p A
  classical
  refine ⟨fun b => ?_, fun b => ?_, fun k _ b b' φ φ' hx => ?_⟩
  · rw [RingHom.comp_id]
    exact (spMap_ev_top (tau (A.aff b) ≫ Y.s)).symm
  · rintro ⟨σ, i⟩ ⟨σ', j⟩
    have e : ∑ r, A.Dv b ⟨σ, i⟩ r * A.cv b ⟨σ', j⟩ r = ((A.k b).w σ * (A.k b).u σ') i j := by
      have : (A.k b).w σ * (A.k b).u σ' = ((A.k b).w σ * A.C b) * (A.A b * (A.k b).u σ') := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.C b), A.CA, Matrix.one_mul]
      rw [this, Matrix.mul_apply]
      rfl
    rw [e]
    by_cases hs : σ = σ'
    · subst hs
      rw [(A.k b).wu]
      by_cases hij : i = j
      · subst hij; simp
      · rw [Matrix.one_apply_ne hij, if_neg]
        intro h'
        exact hij (eq_of_heq (Sigma.mk.inj_iff.1 h').2)
    · rw [eCh_w_mul_u _ hs, Matrix.zero_apply, if_neg]
      intro h'
      exact hs (congrArg Sigma.fst h')
  · have h0 : ⊤ ≤ (spMap φ ≫ (A.V b).2.fromSpec) ⁻¹ᵁ (A.k b).V := le_preimage_comp _ (tau_le (A.aff b) le_rfl)
    have h0' : ⊤ ≤ (spMap φ' ≫ (A.V b').2.fromSpec) ⁻¹ᵁ (A.k b').V :=
      le_preimage_comp _ (tau_le (A.aff b') le_rfl)
    set x := spMap φ ≫ (A.V b).2.fromSpec with hxdef
    have h : ⊤ ≤ x ⁻¹ᵁ (A.k b).V := h0
    have h' : ⊤ ≤ x ⁻¹ᵁ (A.k b').V := hx ▸ h0'
    have hφ : ev x _ h = φ := ev_spMap_tau (A.aff b) φ h
    have hφ' : ev x _ h' = φ' := (ev_congr hx _ h' h0').trans (ev_spMap_tau (A.aff b') φ' h0')
    have hM : ⊤ ≤ x ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h
    have hM' : ⊤ ≤ x ⁻¹ᵁ (A.k b').M.U := le_preimage_mono (A.k b').le h'
    have hMM : ⊤ ≤ x ⁻¹ᵁ ((A.k b).M.U ⊓ (A.k b').M.U) := le_preimage_inf hM hM'
    obtain ⟨a, ha⟩ := A.tw k x b' b h' h hMM
    rintro ⟨σ, j⟩
    set v : Fin (A.k b').M.n → k := (((A.k b').u σ).map (ev x _ h')).mulVec (Pi.single j 1) with hvdef
    set y := ((chg (A.k b).M.toMChart (A.k b').M.toMChart).map (ev x _ hMM)).mulVec v with hydef
    have hv : ((LowRank.pm p (A.k b').M.toMChart σ).map (ev x _ hM')).mulVec v = v :=
      ((A.k b').fix_iff σ x h' hM' v).2 ⟨_, rfl⟩
    have hy : ((LowRank.pm p (A.k b).M.toMChart σ).map (ev x _ hM)).mulVec y = y := by
      have h2 := congrArg (vec (A.k b').M.toMChart x hM') hv
      rw [LowRank.vec_pm, ← vec_chg (A.k b).M.toMChart (A.k b').M.toMChart x hM hM' hMM, ← LowRank.vec_pm] at h2
      exact (vec _ _ _).injective h2
    obtain ⟨t, ht⟩ := ((A.k b).fix_iff σ x h hM y).1 hy
    have key : φ' ∘ A.cv b' ⟨σ, j⟩ = ((a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ)).mulVec t := by
      calc φ' ∘ A.cv b' ⟨σ, j⟩
          = ((A.A b').map (ev x _ h') * ((A.k b').u σ).map (ev x _ h')).mulVec (Pi.single j 1) := by
            rw [hφ']
            funext r
            rw [Matrix.mulVec_single_one, ← Matrix.map_mul]
            rfl
        _ = (a : k) • ((A.A b).map (ev x _ h)).mulVec y := by
            rw [← Matrix.mulVec_mulVec, ha, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
        _ = (a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ).mulVec t := by
            rw [← ht, Matrix.mulVec_mulVec, hφ]
        _ = _ := (Matrix.smul_mulVec _ _ _).symm
    have col : ∀ i, φ ∘ A.cv b ⟨σ, i⟩ = fun r => ((A.A b).map φ * ((A.k b).u σ).map φ) r i := fun i => by
      funext r
      rw [← Matrix.map_mul]
      rfl
    have hsum : ((a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ)).mulVec t =
        ∑ i, ((a : k) * t i) • fun r => ((A.A b).map φ * ((A.k b).u σ).map φ) r i := by
      funext r
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    show φ' ∘ A.cv b' ⟨σ, j⟩ ∈ Submodule.span k (Set.range fun i => φ ∘ A.cv b ⟨σ, i⟩)
    rw [key, hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, col i⟩)
end
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenbundleFrameAffineAtlas_isFlagFrameCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p), IsCover (RingHom.id c.F) Y.s A.V A.alpha A.cv A.Dv := by
  atlas_forward_decl GlobalTheory.FlagMod.FieldFlag.atlas_isCover
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

theorem exists_properFlag : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (RingHom.id K) s V α c D → (∀ x : X, ∃ b, x ∈ (V b).1) → ∃ (Z : Scheme.{0}) (π : Z ⟶ X) (g : ∀ en : En m, Z ⟶ PSpace K (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ Z)), IsProper π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ HasPlk (RingHom.id K) V α c π g κ ∧ (∀ b w, IsOpenImmersion (κ b w)) ∧ (∀ z : Z, ∃ b w, z ∈ Set.range (κ b w)) ∧ ∀ (W : Scheme.{0}) (a a' : W ⟶ Z), a ≫ π = a' ≫ π → (∀ en, a ≫ g en = a' ≫ g en) → a = a' := by
  intro K _ X s T _ m M B _ V α c D hP hN hC hV
  obtain ⟨P, p0, p, h, hPlk⟩ := GlobalTheory.T.exists_pluckerFlagEmbedding_of_projective_base K K (RingHom.id K) X s T m M B V α c D hP hC
  obtain ⟨F, f, i, hf, hi, hif, hcov⟩ := GlobalTheory.T.flagCells_glue_locallyClosed_pluckerProduct K K (RingHom.id K) X s T m M B V α c D P p0 p h hP hN hC hPlk
  have hXn : IsLocallyNoetherian X := by
    obtain ⟨N, ι, _, rfl⟩ := hP
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str K N)
  obtain ⟨hFc, hFn, hFnoe⟩ := GlobalTheory.T.compact_normal_noetherian_of_flagCell_cover X T m B V F i hN hi hcov
  have hPp : IsProper (p0 ≫ s) := by
    obtain ⟨N, ι, hι, e⟩ := hPlk.proj
    have := isProper_str K N
    rw [← e]
    infer_instance
  have hsp : IsProper s := by
    obtain ⟨N, ι, hι, rfl⟩ := hP
    have := isProper_str K N
    infer_instance
  have hp0 : IsProper p0 := IsProper.of_comp p0 s
  have : LocallyOfFiniteType (f ≫ p0 ≫ s) := inferInstance
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian (f ≫ p0 ≫ s)
  have : IsNoetherian F := {}
  have hqc : QuasiCompact f := inferInstance
  have hsep : IsSeparated (f.imageι ≫ p0) := inferInstance
  have hpre := GlobalTheory.T.preimage_iUnion_opens_eq_range_flagCells K K (RingHom.id K) X s T m M B V α c D P p0 p h hC hPlk F f.image f i f.toImage f.imageι
    hf hi hif hcov inferInstance f.toImage_imageι f.toImage.denseRange hFnoe hsep
  have huniv : (⋃ b, ((V b).1 : Set X)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨b, hb⟩ := hV x
    exact Set.mem_iUnion.2 ⟨b, hb⟩
  have hsurj : Function.Surjective f.toImage := by
    rw [← Set.range_eq_univ, ← hpre, huniv, Set.preimage_univ]
  have : Surjective f.toImage := ⟨hsurj⟩
  have : IsIso f.toImage := IsOpenImmersion.isIso f.toImage
  have hfc : IsClosedImmersion f := by
    rw [← f.toImage_imageι]
    infer_instance
  refine ⟨F, f ≫ p0, fun en => f ≫ p en, i, inferInstance, hFn, ⟨?_, ?_⟩, hi, hcov, ?_⟩
  · intro b w
    rw [← Category.assoc, hif, hPlk.base]
  · intro b w en
    obtain ⟨hu, e⟩ := hPlk.plk b w en
    exact ⟨hu, by rw [← Category.assoc, hif, e]⟩
  · intro W a a' e1 e2
    have key : a ≫ f = a' ≫ f := by
      refine hPlk.ext _ _ _ ?_ fun en => ?_
      · simpa only [Category.assoc] using e1
      · simpa only [Category.assoc] using e2 en
    exact (cancel_mono f).1 key

end GlobalTheory.FlagMod.FieldFlag
end
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_proper_normal_flagScheme_of_affine_cover : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (RingHom.id K) s V α c D → (∀ x : X, ∃ b, x ∈ (V b).1) → ∃ (Z : Scheme.{0}) (π : Z ⟶ X) (g : ∀ en : En m, Z ⟶ PSpace K (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ Z)), IsProper π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ HasPlk (RingHom.id K) V α c π g κ ∧ (∀ b w, IsOpenImmersion (κ b w)) ∧ (∀ z : Z, ∃ b w, z ∈ Set.range (κ b w)) ∧ ∀ (W : Scheme.{0}) (a a' : W ⟶ Z), a ≫ π = a' ≫ π → (∀ en, a ≫ g en = a' ≫ g en) → a = a' := by
  atlas_forward_decl GlobalTheory.FlagMod.FieldFlag.exists_properFlag
end

section
section
namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem hom_ext_of_localization_atPrime : ∀ (S : Type) [CommRing S] (W : Scheme.{0}) (z z' : Sp S ⟶ W),
    (∀ q : PrimeSpectrum S, spMap (algebraMap S (Localization.AtPrime q.asIdeal)) ≫ z =
      spMap (algebraMap S (Localization.AtPrime q.asIdeal)) ≫ z') → z = z' := by
  intro S _ W z z' h
  refine GlobalTheory.hom_ext_of_fromSpecStalk fun x => ?_
  let q : PrimeSpectrum S := x
  have e : (Sp S).fromSpecStalk q =
      Spec.map (Spec.stalkIso (CommRingCat.of S) q).inv ≫
        spMap (algebraMap S (Localization.AtPrime q.asIdeal)) := by
    rw [Spec.fromSpecStalk_eq, spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of S) (x := q)).symm
  change (Sp S).fromSpecStalk q ≫ z = (Sp S).fromSpecStalk q ≫ z'
  rw [e, Category.assoc, Category.assoc, h q]

end GlobalTheory.FlagMod.FieldFlag
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_hom_ext_of_localizations_at_all_primes : ∀ (S : Type) [CommRing S] (W : Scheme.{0}) (z z' : Sp S ⟶ W), (∀ q : PrimeSpectrum S, spMap (algebraMap S (Localization.AtPrime q.asIdeal)) ≫ z = spMap (algebraMap S (Localization.AtPrime q.asIdeal)) ≫ z') → z = z' := by
  atlas_forward_decl GlobalTheory.FlagMod.FieldFlag.hom_ext_of_localization_atPrime
end

section
section
namespace GlobalTheory

open IsLocalization

theorem exists_basicOpen_isUnit_of_notMem_map :
    ∀ (S : Type) [CommRing S] (f₀ : S) (q : Ideal S), q.IsPrime → f₀ ∉ q →
      ∀ (J : Type) [Finite J] (m : J → Localization.Away f₀),
        (∀ i, m i ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q) →
        ∃ f : S, f ∉ q ∧ ∃ φ : Localization.Away f₀ →ₐ[S] Localization.Away f,
          ∀ i, IsUnit (φ (m i)) := by
  intro S _ f₀ q hq hf₀ J _ m hm
  classical
  haveI := Fintype.ofFinite J
  have hdisj : Disjoint (↑(Submonoid.powers f₀) : Set S) ↑q :=
    (Ideal.disjoint_powers_iff_notMem f₀ hq.isRadical).2 hf₀
  haveI hq' : (Ideal.map (algebraMap S (Localization.Away f₀)) q).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) (Localization.Away f₀) q hq hdisj
  set d : (Localization.Away f₀) := ∏ i, m i with hd
  have hdq : d ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q := by
    intro h
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (p := Ideal.map (algebraMap S (Localization.Away f₀)) q)).1 h
    exact hm i hi
  obtain ⟨⟨a, y⟩, hay⟩ := IsLocalization.mk'_surjective (Submonoid.powers f₀) d
  simp only at hay
  have hspec : d * algebraMap S (Localization.Away f₀) y = algebraMap S (Localization.Away f₀) a := by
    rw [← hay]; exact IsLocalization.mk'_spec (Localization.Away f₀) a y
  have hyu : IsUnit (algebraMap S (Localization.Away f₀) y) := IsLocalization.map_units (Localization.Away f₀) y
  have ha : a ∉ q := by
    intro haq
    have h1 : algebraMap S (Localization.Away f₀) a ∈ Ideal.map (algebraMap S (Localization.Away f₀)) q := Ideal.mem_map_of_mem _ haq
    rw [← hspec] at h1
    rcases hq'.mem_or_mem h1 with h2 | h2
    · exact hdq h2
    · exact hq'.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hyu)
  refine ⟨f₀ * a, fun h => (hq.mem_or_mem h).elim hf₀ ha, ?_⟩
  let ψ : (Localization.Away f₀) →+* Localization.Away (f₀ * a) := IsLocalization.Away.awayToAwayRight f₀ a
  let φ : (Localization.Away f₀) →ₐ[S] Localization.Away (f₀ * a) :=
    { ψ with commutes' := fun r => IsLocalization.Away.awayToAwayRight_eq f₀ a r }
  refine ⟨φ, fun i => ?_⟩
  have hφ : ∀ x, φ x = ψ x := fun _ => rfl

  have hau : IsUnit (algebraMap S (Localization.Away (f₀ * a)) a) := by
    have hu : IsUnit (algebraMap S (Localization.Away (f₀ * a)) (f₀ * a)) :=
      IsLocalization.Away.algebraMap_isUnit (f₀ * a)
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  have hyu' : IsUnit (φ (algebraMap S (Localization.Away f₀) y)) := hyu.map φ
  have hdu : IsUnit (φ d) := by
    have h3 : φ d * φ (algebraMap S (Localization.Away f₀) y) = algebraMap S _ a := by
      rw [← map_mul, hspec, AlgHom.commutes]
    exact isUnit_of_mul_isUnit_left (h3 ▸ hau)
  have hdvd : m i ∣ d := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  exact isUnit_of_dvd_unit (map_dvd φ hdvd) hdu

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_isUnit_of_notMem_map' : ∀ (S : Type) [CommRing S] (f₀ : S) (q : Ideal S), q.IsPrime → f₀ ∉ q → ∀ (J : Type) [Finite J] (m : J → Localization.Away f₀), (∀ i, m i ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q) → ∃ f : S, f ∉ q ∧ ∃ φ : Localization.Away f₀ →ₐ[S] Localization.Away f, ∀ i, IsUnit (φ (m i)) := by
  atlas_forward_decl GlobalTheory.exists_basicOpen_isUnit_of_notMem_map
end

section
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
theorem nbhd_basicOpen_of_mem : ∀ (S : Type) [CommRing S] (X : Scheme.{0}) (x : Sp S ⟶ X) (V : X.Opens) (q : PrimeSpectrum S), x q ∈ V → ∃ f₀ : S, f₀ ∉ q.asIdeal ∧ ⊤ ≤ (spMap (algebraMap S (Localization.Away f₀)) ≫ x) ⁻¹ᵁ V := by
  intro S _ X x V q hq
  obtain ⟨_, ⟨f₀, rfl⟩, hqf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := q) (u := (show Set (PrimeSpectrum S) from (x ⁻¹ᵁ V).1)) hq (x ⁻¹ᵁ V).2
  refine ⟨f₀, hqf, ?_⟩
  intro y _
  show x ((Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away f₀)))).base y) ∈ V
  apply hsub
  show f₀ ∉ (PrimeSpectrum.comap (algebraMap S (Localization.Away f₀)) y).asIdeal
  intro h
  exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit f₀))
end GlobalTheory
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_nbhd_point_mem_open : ∀ (S : Type) [CommRing S] (X : Scheme.{0}) (x : Sp S ⟶ X) (V : X.Opens) (q : PrimeSpectrum S), x q ∈ V → ∃ f₀ : S, f₀ ∉ q.asIdeal ∧ ⊤ ≤ (spMap (algebraMap S (Localization.Away f₀)) ≫ x) ⁻¹ᵁ V := by
  atlas_forward_decl GlobalTheory.nbhd_basicOpen_of_mem
end

section
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open Matrix

theorem frVec_eq_eigFrame_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (b : A.B) (S₀ : Type) [CommRing S₀] [Algebra c.F S₀] (P₀ : FrPt Xo c S₀), ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).V → ∀ σ : E →+* ℂ, ∃ T : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S₀, IsUnit T.det ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ψ : S₀ →ₐ[c.F] S') (P' : FrPt Xo c S'), FrMap ψ P₀ P' → ∀ (h' : ⊤ ≤ (frX P' ≫ Y.j) ⁻¹ᵁ (A.k b).V) (hM' : ⊤ ≤ (frX P' ≫ Y.j) ⁻¹ᵁ (A.k b).M.U) (j : Fin (Dw.mult σ)), frVec Y P' rfl σ j = vec (A.k b).M.toMChart _ hM' (fun r => ((((A.k b).u σ).map (ev _ _ h')) * T.map ψ) r j) := by
  intro E _ _ _ H Dw l Xo c Y p A b S₀ _ _ P₀ h σ
  have hM : ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h
  set U := ((A.k b).u σ).map (ev (frX P₀ ≫ Y.j) _ h) with hUdef
  set W := ((A.k b).w σ).map (ev (frX P₀ ≫ Y.j) _ h) with hWdef
  have hWU : W * U = 1 := by
    rw [hUdef, hWdef, ← Matrix.map_mul, (A.k b).wu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hfix : ∀ v : Fin (A.k b).M.n → S₀, vec (A.k b).M.toMChart _ hM v ∈ eigLie c (frX P₀ ≫ Y.j) σ →
      U *ᵥ (W *ᵥ v) = v := by
    intro v hv
    obtain ⟨a, ha⟩ := ((A.k b).fix_iff σ _ h hM v).1
      (((LowRank.pm_gen p (A.k b).M.toMChart σ (frX_snd P₀) hM).1 v).1 ((vec_mem_eigLie _ _ hM σ v).1 hv))
    rw [← ha, Matrix.mulVec_mulVec (M := W) (N := U), hWU, Matrix.one_mulVec]
  have hspan := LowRank.initSpan_frVec_top P₀ (A.k b).M.toMChart hM σ
  have hmem : ∀ j, frVec Y P₀ rfl σ j ∈ eigLie c (frX P₀ ≫ Y.j) σ := fun j => by
    rw [← hspan]
    exact Submodule.subset_span ⟨j, j.isLt, rfl⟩
  let cv : Fin (Dw.mult σ) → Fin (A.k b).M.n → S₀ := fun j => (vec (A.k b).M.toMChart _ hM).symm (frVec Y P₀ rfl σ j)
  have hcvv : ∀ j, vec (A.k b).M.toMChart _ hM (cv j) = frVec Y P₀ rfl σ j := fun j =>
    LinearEquiv.apply_symm_apply _ _
  have hcv : ∀ j, U *ᵥ (W *ᵥ cv j) = cv j := fun j => hfix _ (by rw [hcvv]; exact hmem j)
  let C : Matrix (Fin (A.k b).M.n) (Fin (Dw.mult σ)) S₀ := Matrix.of fun i j => cv j i
  have hUT : U * (W * C) = C := by
    ext i j
    have := congrFun (hcv j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, C, Matrix.of_apply]
    exact this
  refine ⟨W * C, ?_, ?_⟩
  · have hcol : ∀ r, vec (A.k b).M.toMChart _ hM (U *ᵥ Pi.single r 1) ∈ eigLie c (frX P₀ ≫ Y.j) σ := fun r =>
      (vec_mem_eigLie _ _ hM σ _).2 (((LowRank.pm_gen p (A.k b).M.toMChart σ (frX_snd P₀) hM).1 _).2
        (((A.k b).fix_iff σ _ h hM _).2 ⟨_, rfl⟩))
    have hc : ∀ r, ∃ a : Fin (Dw.mult σ) → S₀, ∑ j, a j • cv j = U *ᵥ Pi.single r 1 := fun r => by
      have := hcol r
      rw [← hspan, mem_initSpan] at this
      obtain ⟨a, -, ha⟩ := this
      refine ⟨a, (vec (A.k b).M.toMChart _ hM).injective ?_⟩
      rw [map_sum, ← ha]
      simp only [map_smul, hcvv]
    choose a ha using hc
    have hCT : C * Matrix.of (fun j r => a r j) = U := by
      ext i r
      have := congrFun (ha r) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one] at this
      simp only [Matrix.mul_apply, C, Matrix.of_apply]
      rw [Matrix.col_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have h1 : W * C * Matrix.of (fun j r => a r j) = 1 := by rw [Matrix.mul_assoc, hCT, hWU]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact IsUnit.of_mul_eq_one _ h2
  · intro S' _ _ ψ P' hP h' hM' j
    have e : spMap ψ.toRingHom ≫ (frX P₀ ≫ Y.j) = frX P' ≫ Y.j := by rw [← Category.assoc, frX_frMap hP]
    rw [← tanPull_frVec hP rfl rfl e σ j, ← hcvv j, tanPull_vec (A.k b).M.toMChart ψ.toRingHom e hM hM']
    congr 1
    funext i
    have hev : ((A.k b).u σ).map (ev (frX P' ≫ Y.j) _ h') = U.map ψ := by
      ext r s
      simp only [Matrix.map_apply, hUdef]
      rw [ev_congr e.symm _ h' (e ▸ h'), ev_spMap ψ.toRingHom _ _ h]
      rfl
    have hm : U.map ψ * (W * C).map ψ = (U * (W * C)).map ψ := (Matrix.map_mul (f := (ψ : S₀ →+* S'))).symm
    rw [hev, hm, hUT]
    rfl

end GlobalTheory.FlagMod.FieldFlag
end
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameVectors_eq_eigenFrame_mul_invertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (b : A.B) (S₀ : Type) [CommRing S₀] [Algebra c.F S₀] (P₀ : FrPt Xo c S₀), ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).V → ∀ σ : E →+* ℂ, ∃ T : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S₀, IsUnit T.det ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ψ : S₀ →ₐ[c.F] S') (P' : FrPt Xo c S'), FrMap ψ P₀ P' → ∀ (h' : ⊤ ≤ (frX P' ≫ Y.j) ⁻¹ᵁ (A.k b).V) (hM' : ⊤ ≤ (frX P' ≫ Y.j) ⁻¹ᵁ (A.k b).M.U) (j : Fin (Dw.mult σ)), frVec Y P' rfl σ j = vec (A.k b).M.toMChart _ hM' (fun r => ((((A.k b).u σ).map (ev _ _ h')) * T.map ψ) r j) := by
  atlas_forward_decl GlobalTheory.FlagMod.FieldFlag.frVec_eq_eigFrame_mul
end

section
section
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_cell_lies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (q : PrimeSpectrum S), ∃ f : S, f ∉ q.asIdeal ∧ ∃ z : Sp (Localization.Away f) ⟶ Z, ∀ P' : FrPt Xo c (Localization.Away f), FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P' → (cellFrames hZ ht).Lies z P' := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht S _ _ P q
  classical
  obtain ⟨b, hb⟩ := A.cov ((frX P ≫ Y.j) q)
  obtain ⟨f₀, hf₀, hV⟩ := GlobalTheory.T.exists_basicOpen_nbhd_point_mem_open S Y.X (frX P ≫ Y.j) (A.k b).V q hb
  let ι₀ : S →ₐ[c.F] Localization.Away f₀ := IsScalarTower.toAlgHom c.F S (Localization.Away f₀)
  obtain ⟨P₀, hP₀⟩ := exists_frMap ι₀ P
  have hx₀ : frX P₀ ≫ Y.j = spMap (algebraMap S (Localization.Away f₀)) ≫ frX P ≫ Y.j := by
    rw [← frX_frMap hP₀, Category.assoc]; rfl
  have h₀ : ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).V := by rw [hx₀]; exact hV
  choose T hTu hT using GlobalTheory.T.frameVectors_eq_eigenFrame_mul_invertible E H Dw l Xo c Y p A b _ P₀ h₀
  have hq₀ : (Ideal.map (algebraMap S (Localization.Away f₀)) q.asIdeal).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) _ q.asIdeal q.2
      ((Ideal.disjoint_powers_iff_notMem _ q.2.isRadical).2 hf₀)
  have hdet : ∀ σ, (T σ).det ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q.asIdeal :=
    fun σ h => hq₀.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hTu σ))
  choose w hw using fun σ => GlobalTheory.T.exists_perm_leadingMinors_not_mem _ _ (T σ) _ hq₀ (hdet σ)
  obtain ⟨f, hf, φ, hφ⟩ := GlobalTheory.T.exists_basicOpen_isUnit_of_notMem_map' S f₀ q.asIdeal q.2 hf₀ (Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1))
    (fun i => (((T i.1).submatrix (w i.1) id).submatrix (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))
      (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))).det) (fun i => hw i.1 _ _)
  refine ⟨f, hf, ?_⟩
  let φ' : Localization.Away f₀ →ₐ[c.F] Localization.Away f := φ.restrictScalars c.F
  have hcomp : φ'.comp ι₀ = IsScalarTower.toAlgHom c.F S (Localization.Away f) :=
    AlgHom.ext fun s => φ.commutes s
  obtain ⟨P₁, hP₁⟩ := exists_frMap φ' P₀
  have hP₁' : FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P₁ :=
    hcomp ▸ PullbackSections.frMap_trans ι₀ φ' hP₀ hP₁
  have hx₁ : frX P₁ ≫ Y.j = spMap φ'.toRingHom ≫ frX P₀ ≫ Y.j := by rw [← frX_frMap hP₁, Category.assoc]
  have h₁ : ⊤ ≤ (frX P₁ ≫ Y.j) ⁻¹ᵁ (A.k b).V := by rw [hx₁]; exact le_preimage_comp _ h₀
  have hM₁ : ⊤ ≤ (frX P₁ ≫ Y.j) ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h₁
  have hminor : ∀ σ (k : ℕ) (hk : k ≤ Dw.mult σ), IsUnit ((((T σ).map φ').submatrix (w σ) id).submatrix
      (Fin.castLE hk) (Fin.castLE hk)).det := by
    intro σ k hk
    have h := hφ ⟨σ, ⟨k, Nat.lt_succ_of_le hk⟩⟩
    have e : (((T σ).map φ').submatrix (w σ) id).submatrix (Fin.castLE hk) (Fin.castLE hk) =
        (φ : Localization.Away f₀ →+* Localization.Away f).mapMatrix
          (((T σ).submatrix (w σ) id).submatrix (Fin.castLE hk) (Fin.castLE hk)) := rfl
    rw [e, ← RingHom.map_det]
    exact h
  choose L U hL0 hL1 hU hUu hLU using fun σ => GlobalTheory.T.exists_lu_of_isUnit_leading_minors (Localization.Away f) (Dw.mult σ)
    (((T σ).map φ').submatrix (w σ) id) (hminor σ)
  let ψ₀ : Γ(Y.X, (A.V b).1) →+* Localization.Away f := ev (frX P₁ ≫ Y.j) _ h₁
  let xc : CellVar Dw.mult → Localization.Away f := fun v => L v.1 v.2.1.1 v.2.1.2
  obtain ⟨hzπ, hz, huAt⟩ := GlobalTheory.T.flagCellPoint_image_and_frame E H Dw l Xo c Y p A Z π g κ hZ ht b w _ ψ₀ xc _ rfl
  refine ⟨spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w, fun P' hP' => ?_⟩
  obtain rfl := frMap_unique hP₁' hP'
  have hx : (spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w) ≫ π = frX P₁ ≫ Y.j :=
    hzπ.trans (spMap_ev _ (A.V b).2 h₁)
  refine GlobalTheory.T.carries_framedPoint_of_unitTriangular_chart E H Dw l Xo c c.F (RingHom.id c.F) Y Z π (cellFrames hZ ht)
    (GlobalTheory.T.flagCellFrames_lastStep_eigenmodules E H Dw l Xo c Y p A Z π g κ hZ ht) _ P₁ _ ((b, w) : A.B × Pm Dw.mult) hz hx U hU hUu ?_
  intro σ i
  rw [hT σ _ φ' P₁ hP₁ h₁ hM₁ i]
  have hcell : Matrix.of (cell xc σ) = L σ := by
    ext i j
    simp only [Matrix.of_apply, cell, xc]
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (hL1 σ i).symm
    · exact (hL0 σ i j (lt_of_le_of_ne (not_lt.1 h1) h2)).symm
  have key : ((A.k b).u σ).map ψ₀ * (T σ).map φ' =
      ((((A.k b).u σ).map ψ₀).submatrix id (w σ) * L σ) * U σ := by
    rw [Matrix.mul_assoc, ← hLU σ, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  simp only [Frames.vecAt, huAt σ, hcell, ← map_smul, ← map_sum]
  congr 1
  funext r
  change (((A.k b).u σ).map ψ₀ * (T σ).map φ') r i = _
  rw [key, Matrix.mul_apply]
  erw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact _root_.mul_comm _ _

end GlobalTheory.FlagMod.FieldFlag
end
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagCell_containing_framed_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (q : PrimeSpectrum S), ∃ f : S, f ∉ q.asIdeal ∧ ∃ z : Sp (Localization.Away f) ⟶ Z, ∀ P' : FrPt Xo c (Localization.Away f), FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P' → (cellFrames hZ ht).Lies z P' := by
  atlas_forward_decl GlobalTheory.FlagMod.FieldFlag.exists_cell_lies
end

section
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

noncomputable section
namespace GlobalTheory.FlagMod.FieldFlag.Glue

private theorem exists_pow_smul_mem_of_mem_span_away' {R : Type} [CommRing R] (r : R) {n : ℕ} (N : Submodule R (Fin n → R))
    (x : Fin n → R)
    (hx : (fun t => algebraMap R (Localization.Away r) (x t)) ∈
      Submodule.span (Localization.Away r)
        ((fun (y : Fin n → R) t => algebraMap R (Localization.Away r) (y t)) '' (N : Set (Fin n → R)))) :
    ∃ k : ℕ, r ^ k • x ∈ N := by
  have key : ∀ y ∈ Submodule.span (Localization.Away r)
      ((fun (y : Fin n → R) t => algebraMap R (Localization.Away r) (y t)) '' (N : Set (Fin n → R))),
      ∃ m ∈ N, ∃ k : ℕ, (algebraMap R (Localization.Away r) r) ^ k • y =
        fun t => algebraMap R (Localization.Away r) (m t) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      exact ⟨m, hm, 0, by simp⟩
    | zero => exact ⟨0, N.zero_mem, 0, by funext t; simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨m₁, hm₁, k₁, e₁⟩ := h₁
      obtain ⟨m₂, hm₂, k₂, e₂⟩ := h₂
      refine ⟨r ^ k₂ • m₁ + r ^ k₁ • m₂, N.add_mem (N.smul_mem _ hm₁) (N.smul_mem _ hm₂), k₁ + k₂, ?_⟩
      funext t
      have e₁t := congrFun e₁ t
      have e₂t := congrFun e₂ t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, map_add, map_mul, map_pow] at e₁t e₂t ⊢
      rw [← e₁t, ← e₂t]
      ring
    | smul a y _ h =>
      obtain ⟨m, hm, k, e⟩ := h
      obtain ⟨⟨b, d⟩, hab⟩ := IsLocalization.surj (Submonoid.powers r) a
      obtain ⟨q, hq⟩ := (Submonoid.mem_powers_iff _ _).mp d.2
      refine ⟨b • m, N.smul_mem _ hm, k + q, ?_⟩
      funext t
      have et := congrFun e t
      simp only [Pi.smul_apply, smul_eq_mul, map_mul] at et hab ⊢
      rw [← hq, map_pow] at hab
      rw [← et, ← hab]
      ring
  obtain ⟨m, hm, k, e⟩ := key _ hx
  have ht : ∀ t, ∃ q : ℕ, r ^ q * (r ^ k * x t) = r ^ q * m t := by
    intro t
    have et := congrFun e t
    simp only [Pi.smul_apply, smul_eq_mul] at et
    rw [← map_pow, ← map_mul] at et
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers r) et
    obtain ⟨q, hq⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
    exact ⟨q, by rw [hq]; exact hc⟩
  choose q hq using ht
  refine ⟨(∑ t, q t) + k, ?_⟩
  have hx' : r ^ ((∑ t, q t) + k) • x = r ^ (∑ t, q t) • m := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (f := q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
    rw [hd]
    calc r ^ (q t + d + k) * x t = r ^ d * (r ^ q t * (r ^ k * x t)) := by ring
      _ = r ^ d * (r ^ q t * m t) := by rw [hq t]
      _ = r ^ (q t + d) * m t := by ring
  rw [hx']
  exact N.smul_mem _ hm

theorem initSpan_le_of_away {R : Type} [CommRing R] {ι : Type} (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    {m n : ℕ} (u v : Fin m → Fin n → R) (j : ℕ)
    (h : ∀ i, initSpan (Localization.Away (s i)) (fun a t => algebraMap R (Localization.Away (s i)) (u a t)) j ≤
      initSpan (Localization.Away (s i)) (fun a t => algebraMap R (Localization.Away (s i)) (v a t)) j) :
    initSpan R u j ≤ initSpan R v j := by
  unfold initSpan at *
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range s) hs
  rintro ⟨_, ⟨i, rfl⟩⟩
  apply exists_pow_smul_mem_of_mem_span_away' (s i)
  have hmem : (fun t => algebraMap R (Localization.Away (s i)) (u a t)) ∈
      Submodule.span (Localization.Away (s i))
        ((fun a t => algebraMap R (Localization.Away (s i)) (v a t)) '' {b : Fin m | (b : ℕ) < j}) :=
    h i (Submodule.subset_span ⟨a, ha, rfl⟩)
  refine Submodule.span_mono ?_ hmem
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨v b, Submodule.subset_span ⟨b, hb, rfl⟩, rfl⟩

theorem initSpan_eq_of_away {R : Type} [CommRing R] {ι : Type} (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    {m n : ℕ} (u v : Fin m → Fin n → R) (j : ℕ)
    (h : ∀ i, initSpan (Localization.Away (s i)) (fun a t => algebraMap R (Localization.Away (s i)) (u a t)) j =
      initSpan (Localization.Away (s i)) (fun a t => algebraMap R (Localization.Away (s i)) (v a t)) j) :
    initSpan R u j = initSpan R v j :=
  le_antisymm (initSpan_le_of_away s hs u v j fun i => (h i).le)
    (initSpan_le_of_away s hs v u j fun i => (h i).ge)

theorem ext_away {S : Type} [CommRing S] {X : Scheme.{0}} {ι : Type} (f : ι → S)
    (hf : Ideal.span (Set.range f) = ⊤) {w w' : Sp S ⟶ X}
    (h : ∀ i, spMap (algebraMap S (Localization.Away (f i))) ≫ w = spMap (algebraMap S (Localization.Away (f i))) ≫ w') :
    w = w' :=
  Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) f hf).openCover w w'
    fun i => h i

theorem glue_away {S : Type} [CommRing S] {X : Scheme.{0}} {ι : Type} (f : ι → S)
    (hf : Ideal.span (Set.range f) = ⊤) (z : ∀ i, Sp (Localization.Away (f i)) ⟶ X)
    (h : ∀ i j (T : Type) [CommRing T] (a : Localization.Away (f i) →+* T) (b : Localization.Away (f j) →+* T),
      a.comp (algebraMap S _) = b.comp (algebraMap S _) → spMap a ≫ z i = spMap b ≫ z j) :
    ∃ w : Sp S ⟶ X, ∀ i, spMap (algebraMap S (Localization.Away (f i))) ≫ w = z i := by
  let U := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) f hf).openCover
  refine ⟨Scheme.Cover.glueMorphisms U (fun i => z i) ?_, fun i => Scheme.Cover.ι_glueMorphisms U (fun i => z i) _ i⟩
  intro i j
  show pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f i)))))
      (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f j))))) ≫ z i =
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f i)))))
      (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f j))))) ≫ z j
  rw [← cancel_epi (pullbackSpecIso S (Localization.Away (f i)) (Localization.Away (f j))).inv,
    pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  exact h i j _ _ _ Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

end GlobalTheory.FlagMod.FieldFlag.Glue

noncomputable section
namespace GlobalTheory.FlagMod.FieldFlag.Glue

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem initSpan_comp_equiv {R N N' : Type} [CommRing R] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    {m : ℕ} (V : N ≃ₗ[R] N') (w : Fin m → N) (j : ℕ) :
    initSpan R (fun a => V (w a)) j = (initSpan R w j).map (V : N →ₗ[R] N') := by
  unfold initSpan
  rw [Submodule.map_span, ← Set.image_comp]
  rfl

theorem compat_of_uniq {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X}
    (F : Frames Y π) {S : Type} [CommRing S] [Algebra c.F S] (P : FrPt Xo c S)
    (huniq : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z),
      F.Lies z₁ P₁ → F.Lies z₂ P₁ → z₁ = z₂) (f g : S)
    (Pf : FrPt Xo c (Localization.Away f)) (hPf : FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P Pf)
    (Pg : FrPt Xo c (Localization.Away g)) (hPg : FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away g)) P Pg)
    (zf : Sp (Localization.Away f) ⟶ Z) (zg : Sp (Localization.Away g) ⟶ Z) (hf : F.Lies zf Pf) (hg : F.Lies zg Pg)
    (T : Type) [CommRing T] (a : Localization.Away f →+* T) (b : Localization.Away g →+* T)
    (hab : a.comp (algebraMap S _) = b.comp (algebraMap S _)) : spMap a ≫ zf = spMap b ≫ zg := by
  letI : Algebra c.F T := ((a.comp (algebraMap S _)).comp (algebraMap c.F S)).toAlgebra
  have hca : ∀ r : c.F, a (algebraMap c.F (Localization.Away f) r) = algebraMap c.F T r := fun r => by
    rw [IsScalarTower.algebraMap_apply c.F S (Localization.Away f)]
    rfl
  have hcb : ∀ r : c.F, b (algebraMap c.F (Localization.Away g) r) = algebraMap c.F T r := fun r => by
    rw [IsScalarTower.algebraMap_apply c.F S (Localization.Away g)]
    exact (RingHom.congr_fun hab (algebraMap c.F S r)).symm
  let a' : Localization.Away f →ₐ[c.F] T := AlgHom.mk a hca
  let b' : Localization.Away g →ₐ[c.F] T := AlgHom.mk b hcb
  have ha : a'.toRingHom = a := rfl
  have hb : b'.toRingHom = b := rfl
  obtain ⟨Q, hQ⟩ := exists_frMap a' Pf
  have h1 : FrMap (a'.comp (IsScalarTower.toAlgHom c.F S (Localization.Away f))) P Q :=
    GlobalTheory.FlagTan.frMap_comp hPf hQ (fun _ => rfl)
  have h2 : FrMap b' Pg Q :=
    GlobalTheory.FlagTan.frMap_of_comp hPg h1 (fun s => (RingHom.congr_fun hab s).symm)
  have e := huniq T Q _ _ (hf.frMap hQ) (hg.frMap h2)
  rw [ha, hb] at e
  exact e

theorem lies_of_local {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X}
    (F : Frames Y π) {S : Type} [CommRing S] [Algebra c.F S] (P : FrPt Xo c S)
    (huniq : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z),
      F.Lies z₁ P₁ → F.Lies z₂ P₁ → z₁ = z₂)
    (hloc : ∀ q : PrimeSpectrum S, ∃ f : S, f ∉ q.asIdeal ∧ ∃ z : Sp (Localization.Away f) ⟶ Z,
      ∀ P' : FrPt Xo c (Localization.Away f), FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P' →
        F.Lies z P') :
    ∃ z : Sp S ⟶ Z, F.Lies z P := by
  choose f hfq z hz using hloc
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hfq ⟨M, hM.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  have hP : ∀ q, ∃ Pq : FrPt Xo c (Localization.Away (f q)),
      FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away (f q))) P Pq := fun q => exists_frMap _ P
  choose Pq hPq using hP
  obtain ⟨w, hw⟩ := glue_away f hspan z (fun i j T _ a b hab =>
    compat_of_uniq F P huniq (f i) (f j) (Pq i) (hPq i) (Pq j) (hPq j) (z i) (z j)
      (hz i _ (hPq i)) (hz j _ (hPq j)) T a b hab)
  refine ⟨w, ?_⟩
  unfold Frames.Lies
  refine ⟨?_, ?_⟩
  · apply ext_away f hspan
    intro q
    have hLq := hz q _ (hPq q)
    unfold Frames.Lies at hLq
    rw [← Category.assoc, hw q, hLq.1, ← frX_frMap (hPq q), Category.assoc]
    rfl
  · intro S' _ _ ψ P' hP' k z' hz'w hzk hx σ i
    subst hz'w
    have hM := F.inM hzk hx
    have e1 := fun (w' : Fin (Dw.mult σ) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (frX P' ≫ Y.j) Y.t.G) =>
      initSpan_comp_equiv (vec (F.M k).toMChart _ hM) (fun a => (vec (F.M k).toMChart _ hM).symm (w' a)) i
    simp only [LinearEquiv.apply_symm_apply] at e1
    rw [e1 (frVec Y P' rfl σ), e1 (F.vecAt k _ hzk hx σ)]
    congr 1
    have hspan' : Ideal.span (Set.range fun q => ψ (f q)) = ⊤ := by
      have h2 : Ideal.map ψ (Ideal.span (Set.range f)) = ⊤ := by rw [hspan, Ideal.map_top]
      rw [Ideal.map_span, ← Set.range_comp] at h2
      exact h2
    apply initSpan_eq_of_away (fun q => ψ (f q)) hspan'
    intro q
    try dsimp only
    obtain ⟨P'', hP''⟩ := exists_frMap (IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))) P'
    have hmap : ∀ s : S, Localization.awayMapₐ ψ (f q) (algebraMap S (Localization.Away (f q)) s) =
        algebraMap S' (Localization.Away (ψ (f q))) (ψ s) := fun s => by
      first
        | exact IsLocalization.map_eq _ _
        | simp [IsLocalization.Away.mapₐ, IsLocalization.Away.map, IsLocalization.map_eq]
    have e3 : (Localization.awayMapₐ ψ (f q)).comp (IsScalarTower.toAlgHom c.F S (Localization.Away (f q))) =
        (IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).comp ψ := AlgHom.ext fun s => hmap s
    have hPP'' : FrMap ((IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).comp ψ) P P'' :=
      GlobalTheory.FlagTan.frMap_comp hP' hP'' (fun _ => rfl)
    have hqP'' : FrMap (Localization.awayMapₐ ψ (f q)) (Pq q) P'' :=
      GlobalTheory.FlagTan.frMap_of_comp (hPq q) hPP'' (fun s => hmap s)
    have ez : spMap (Localization.awayMapₐ ψ (f q)).toRingHom ≫ z q =
        spMap (IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).toRingHom ≫
          spMap ψ.toRingHom ≫ w := by
      calc spMap (Localization.awayMapₐ ψ (f q)).toRingHom ≫ z q
            = spMap (Localization.awayMapₐ ψ (f q)).toRingHom ≫
                spMap (IsScalarTower.toAlgHom c.F S (Localization.Away (f q))).toRingHom ≫ w := by
              rw [← hw q]
              rfl
          _ = spMap ((Localization.awayMapₐ ψ (f q)).comp
                (IsScalarTower.toAlgHom c.F S (Localization.Away (f q)))).toRingHom ≫ w :=
              (spMap_algComp _ _ w).symm
          _ = spMap ((IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).comp ψ).toRingHom ≫ w := by
              rw [e3]
          _ = _ := spMap_algComp _ _ w
    have hzk'' : ⊤ ≤ (spMap (IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).toRingHom ≫
        spMap ψ.toRingHom ≫ w) ⁻¹ᵁ F.U k := le_preimage_comp _ hzk
    have hx'' : (spMap (IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).toRingHom ≫
        spMap ψ.toRingHom ≫ w) ≫ π = frX P'' ≫ Y.j := by
      rw [Category.assoc, hx, ← Category.assoc, frX_frMap hP'']
    have hLq := hz q _ (hPq q)
    unfold Frames.Lies at hLq
    have LA := hLq.2 (Localization.Away (ψ (f q))) (Localization.awayMapₐ ψ (f q)) P'' hqP'' k _ ez hzk'' hx'' σ i
    have hM'' := F.inM hzk'' hx''
    have et : spMap (IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).toRingHom ≫ (frX P' ≫ Y.j) =
        frX P'' ≫ Y.j := by
      rw [← Category.assoc, frX_frMap hP'']
    have cA : ∀ a, (vec (F.M k).toMChart _ hM'').symm (frVec Y P'' rfl σ a) =
        fun t => algebraMap S' (Localization.Away (ψ (f q))) ((vec (F.M k).toMChart _ hM).symm (frVec Y P' rfl σ a) t) := by
      intro a
      rw [LinearEquiv.symm_apply_eq, ← tanPull_frVec hP'' rfl rfl et σ a]
      conv_lhs => rw [← LinearEquiv.apply_symm_apply (vec (F.M k).toMChart _ hM) (frVec Y P' rfl σ a)]
      exact tanPull_vec _ _ _ _ _ _
    have cB : ∀ a, (vec (F.M k).toMChart _ hM'').symm (F.vecAt k _ hzk'' hx'' σ a) =
        fun t => algebraMap S' (Localization.Away (ψ (f q))) ((vec (F.M k).toMChart _ hM).symm (F.vecAt k _ hzk hx σ a) t) := by
      intro a
      unfold Frames.vecAt
      simp only [LinearEquiv.symm_apply_apply]
      funext t
      unfold Frames.uAt
      try simp only [Matrix.map_apply]
      rw [ev_spMap _ (spMap ψ.toRingHom ≫ w) (F.U k) hzk]
      rfl
    have L2 : initSpan (Localization.Away (ψ (f q))) (fun a => (vec (F.M k).toMChart _ hM'').symm (frVec Y P'' rfl σ a)) i =
        initSpan (Localization.Away (ψ (f q))) (fun a => (vec (F.M k).toMChart _ hM'').symm (F.vecAt k _ hzk'' hx'' σ a)) i := by
      rw [initSpan_comp_equiv (vec (F.M k).toMChart _ hM'').symm (frVec Y P'' rfl σ),
        initSpan_comp_equiv (vec (F.M k).toMChart _ hM'').symm (F.vecAt k _ hzk'' hx'' σ), LA]
    simpa only [cA, cB] using L2
end GlobalTheory.FlagMod.FieldFlag.Glue

namespace GlobalTheory.FlagMod.FieldFlag

theorem exists_lies_of_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S), (∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z), (cellFrames hZ ht).Lies z₁ P₁ → (cellFrames hZ ht).Lies z₂ P₁ → z₁ = z₂) → (∀ q : PrimeSpectrum S, ∃ f : S, f ∉ q.asIdeal ∧ ∃ z : Sp (Localization.Away f) ⟶ Z, ∀ P' : FrPt Xo c (Localization.Away f), FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P' → (cellFrames hZ ht).Lies z P') → ∃ z : Sp S ⟶ Z, (cellFrames hZ ht).Lies z P := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht S _ _ P huniq hloc
  exact Glue.lies_of_local (cellFrames hZ ht) P huniq hloc

end GlobalTheory.FlagMod.FieldFlag
end
end
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagBundle_point_carrying_of_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S), (∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z), (cellFrames hZ ht).Lies z₁ P₁ → (cellFrames hZ ht).Lies z₂ P₁ → z₁ = z₂) → (∀ q : PrimeSpectrum S, ∃ f : S, f ∉ q.asIdeal ∧ ∃ z : Sp (Localization.Away f) ⟶ Z, ∀ P' : FrPt Xo c (Localization.Away f), FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P' → (cellFrames hZ ht).Lies z P') → ∃ z : Sp S ⟶ Z, (cellFrames hZ ht).Lies z P := by
  atlas_forward_decl GlobalTheory.FlagMod.FieldFlag.exists_lies_of_local
end

section
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory

theorem flat_to_spec_field : ∀ (K : Type) [Field K] (Z : Scheme.{0}) (f : Z ⟶ Sp K), Flat f := by
  intro K _ Z f
  haveI : IsIntegral (Sp K) := by unfold Sp; infer_instance
  haveI : Subsingleton (Sp K) := by unfold Sp; infer_instance
  infer_instance

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_to_spec_field' : ∀ (K : Type) [Field K] (Z : Scheme.{0}) (f : Z ⟶ Sp K), Flat f := by
  atlas_forward_decl GlobalTheory.flat_to_spec_field
end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

theorem nonempty_flagModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim Y.s → PushInvertible Y.t.G Y.t.PP.L → Nonempty (GlobalTheory.FlagMod.FlagModel Y) := by
  intro E _ _ _ H Dw l Xo c Y _ hP
  obtain ⟨p⟩ := LowRank.nonempty_proj_id (E := E) (c := c)
  obtain ⟨A⟩ := GlobalTheory.T.exists_eigenbundleFrameAffineAtlas E H Dw l Xo c Y p hP
  have := A.fin
  obtain ⟨Z, π, g, κ, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_proper_normal_flagScheme_of_affine_cover c.F Y.X Y.s (E →+* ℂ) Dw.mult A.N A.B A.V A.alpha A.cv A.Dv Y.proj Y.normal (GlobalTheory.T.eigenbundleFrameAffineAtlas_isFlagFrameCover E H Dw l Xo c Y p A) A.cov
  have hZ : Cells A π g κ := ⟨h1, h2, h3, h5, h6⟩
  have := h4
  have ht := GlobalTheory.T.flagCellFrameChangeTriangular_of_cells E H Dw l Xo c Y p A Z π g κ hZ
  have huniq : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z), (cellFrames hZ ht).Lies z₁ P₁ → (cellFrames hZ ht).Lies z₂ P₁ → z₁ = z₂ := by
    intro S' _ _ P₁ z₁ z₂ e₁ e₂
    refine GlobalTheory.T.spec_hom_ext_of_localizations_at_all_primes S' Z z₁ z₂ fun q => ?_
    obtain ⟨P', hP'⟩ := exists_frMap (IsScalarTower.toAlgHom c.F S' (Localization.AtPrime q.asIdeal)) P₁
    have l₁ := e₁.frMap hP'
    have l₂ := e₂.frMap hP'
    refine GlobalTheory.T.flagBundle_points_eq_of_same_steps_localRing E H Dw l Xo c Y p A Z π g κ hZ ht _ _ _ _ l₁.1 l₂.1 fun σ i => ?_
    obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover (spMap (algebraMap S' (Localization.AtPrime q.asIdeal)) ≫ z₁)
    obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover (spMap (algebraMap S' (Localization.AtPrime q.asIdeal)) ≫ z₂)
    exact (l₁.initSpan_eq hk l₁.1 rfl σ i).symm.trans (l₂.initSpan_eq hk' l₂.1 rfl σ i)
  refine ⟨{ YY := Z, π := π, proper := h1, normal := h2, flat := ?_, F := cellFrames hZ ht
            dense := GlobalTheory.T.dense_flagBundle_preimage_moduli E H Dw l Xo c Y p A Z π g κ hZ, top := GlobalTheory.T.flagCellFrames_lastStep_eigenmodules E H Dw l Xo c Y p A Z π g κ hZ ht
            rep := fun S _ _ P => ?_, fin := fun K _ _ z => ?_ }⟩
  · exact GlobalTheory.T.flat_to_spec_field' c.F Z (π ≫ Y.s)
  · obtain ⟨z, hz⟩ := GlobalTheory.T.exists_flagBundle_point_carrying_of_local E H Dw l Xo c Y p A Z π g κ hZ ht S P huniq fun q => GlobalTheory.T.exists_flagCell_containing_framed_point E H Dw l Xo c Y p A Z π g κ hZ ht S P q
    exact ⟨z, hz, fun z' hz' => huniq S P z' z hz' hz⟩
  · refine (Set.finite_singleton z).subset fun z' ⟨hx, h⟩ => ?_
    exact GlobalTheory.T.flagBundle_points_eq_of_same_steps_localRing E H Dw l Xo c Y p A Z π g κ hZ ht K z' z _ hx rfl h

end GlobalTheory.FlagMod.FieldFlag
end
end
