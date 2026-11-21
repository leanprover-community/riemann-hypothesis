import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroSourceTensorColumnProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OfTensColMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineModelKappaTransformIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingDualIndicatorAddNonzeroCosets
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualLatticeCosetIndicatorIsSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroTargetTensorRowProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulHalf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactQLat

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastTgtSlice

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sb_sec (p : SplitPt D k) {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : Submodule.IsLattice D.host.E LS)
    (hT : Submodule.IsLattice D.host.E LT) {Φ : WO S T → ℂ}
    (hΦ : IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) Φ) :
    (fun x : Matrix (Fin T.rank) (Fin S.rank) k => Φ (x.map p.sec)) ∈ SB (Matrix (Fin T.rank) (Fin S.rank) k) := by
  classical
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Fin T.rank) (n' := Fin S.rank)
  have : CharZero k := charZero_of_injective_ringHom (f := p.pr.comp (incA D)) (RingHom.injective _)
  obtain ⟨-, k0, hk0, hinv, hsup⟩ := hΦ
  obtain ⟨hUo, hUc⟩ := HalfInd.open_compact_sec p hS hT
  obtain ⟨ε, hε, heε⟩ := HalfInd.exists_idem p
  have hhalf : ∀ x : Matrix (Fin T.rank) (Fin S.rank) k, IsHalf p.e (x.map p.sec : WO S T) := fun x i j => by
    rw [Matrix.map_apply, ← p.sec_pr, p.pr_sec]
  set U := {y : Matrix (Fin T.rank) (Fin S.rank) k |
      y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} with hU
  have hUv : ∀ y ∈ U, (y.map p.sec : WO S T) ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
    intro y h
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε p.split.1 heε h).1
    rwa [(GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hhalf y))] at h2
  have hc : ((k0 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  have hwr : ∀ z : Matrix (Fin T.rank) (Fin S.rank) k,
      ((((k0 : ℕ) : k) • z).map p.sec : WO S T) = k0 • (z.map p.sec : WO S T) := by
    intro z
    rw [Nat.cast_smul_eq_nsmul]
    exact Matrix.ext fun i j => map_nsmul p.sec k0 (z i j)
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · refine ⟨{x' | ((k0 : ℕ) : k)⁻¹ • (x' - x) ∈ U}, hUo.preimage (by fun_prop), ?_, fun x' hx' => ?_⟩
    · show ((k0 : ℕ) : k)⁻¹ • (x - x) ∈ U
      rw [sub_self, smul_zero]
      show (0 : Matrix (Fin T.rank) (Fin S.rank) k).map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True
      rw [Matrix.map_zero _ (map_zero _)]; exact zero_mem _
    · set z := ((k0 : ℕ) : k)⁻¹ • (x' - x) with hz
      have hx'z : x' = x + ((k0 : ℕ) : k) • z := by
        rw [hz, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
      show Φ (x'.map p.sec) = Φ (x.map p.sec)
      rw [hx'z, Matrix.map_add _ (map_add _), hwr]
      exact hinv _ (hUv _ hx') (hhalf _) _
  · refine HasCompactSupport.intro (hUc.image (f := fun z => ((k0 : ℕ) : k)⁻¹ • z) (by fun_prop)) fun x hx => ?_
    by_contra h
    have h1 := hsup _ h
    have h2 : ((k0 : ℕ) : k) • x ∈ U := by
      show (((k0 : ℕ) : k) • x).map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True
      rw [hwr]; exact GlobalTheory.PlaceModel.latO_le_top _ h1
    exact hx ⟨_, h2, by beta_reduce; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem line_eq {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) (i j : Fin L.rank) : i = j := by
  have := hζ.1
  ext; omega

theorem line_ne {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) (j : Fin L.rank) : ζ j ≠ 0 := by
  intro h
  have : ζ = 0 := funext fun i => by rw [line_eq hζ i j]; exact h
  exact hζ.2 (by simp [this])

theorem line_sum {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {M : Type} [AddCommMonoid M]
    (f : Fin L.rank → M) (j : Fin L.rank) : ∑ i, f i = f j :=
  Finset.sum_eq_single j (fun i _ h => absurd (line_eq hζ i j) h) (by simp)

theorem isLattice_span {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) :
    Submodule.IsLattice D.host.E (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) := by
  refine ⟨Submodule.fg_span (Set.finite_singleton _), ?_⟩
  rw [eq_top_iff]
  intro x _
  have j : Fin L.rank := ⟨0, by have := hζ.1; omega⟩
  have hx : x = (x j / ζ j) • ζ := by
    funext i
    rw [line_eq hζ i j, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ (line_ne hζ j)]
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span rfl))

theorem exists_colFun (p : SplitPt D k) {n : Type} [Fintype n] [DecidableEq n] {L S : HSp D}
    {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) (β : Frame p S n) {LL : Lat L} {LS : Lat S}
    (hL : Submodule.IsLattice D.host.E LL) (hS : Submodule.IsLattice D.host.E LS) {Φ : WO L S → ℂ}
    (hΦ : IsSBHalf p.e (latO L S (LL : Set _) (LS : Set _) (· = p.v)) Φ) :
    ∃ b ∈ SB (n → k), colFun β ζ b = Φ := by
  classical
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  set z : Fin L.rank → k := fun j => p.pr (incA D (ζ j)) with hz
  have hz0 : ∀ j, z j ≠ 0 := fun j h =>
    line_ne hζ j ((p.pr.comp (incA D)).injective (by rw [map_zero]; exact h))
  have h1 := sb_sec p hL hS hΦ
  have h2 := Comm.comp_mem_SB h1
    (p := fun y : n → k => Matrix.of fun i j => (β.b *ᵥ y) i * (z j)⁻¹)
    (s := fun x : Matrix (Fin S.rank) (Fin L.rank) k => β.b' *ᵥ (x *ᵥ z)) ?_ ?_ ?_
  · refine ⟨_, h2, ?_⟩
    funext t
    unfold colFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      beta_reduce
      congr 1
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply, ExtZero.zcol, Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
      simp only [Matrix.mulVec, dotProduct]
      rw [line_sum hζ _ j, map_mul p.pr, mul_assoc, mul_inv_cancel₀ (hz0 j), mul_one, p.sec_pr, ht i j]
    · rw [if_neg ht]
      by_contra h
      exact ht (hΦ.1 t (Ne.symm h))
  · refine continuous_matrix fun i j => ?_
    exact ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)).mul continuous_const
  · exact continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)
  · intro y
    have : (Matrix.of fun i j => (β.b *ᵥ y) i * (z j)⁻¹) *ᵥ z = β.b *ᵥ y := by
      funext i
      have j : Fin L.rank := ⟨0, by have := hζ.1; omega⟩
      rw [Matrix.mulVec, dotProduct, line_sum hζ _ j, Matrix.of_apply, mul_assoc, inv_mul_cancel₀ (hz0 j), mul_one]
    beta_reduce
    rw [this, Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec]

theorem isSBHalf_halfInd {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf e Λ (halfInd e Λ) := by
  have h0 : ∀ t, halfInd e Λ t ≠ 0 → t ∈ Λ ∧ IsHalf e t := fun t ht => by
    by_contra h
    exact ht (by unfold halfInd; rw [if_neg h])
  refine ⟨fun t ht => (h0 t ht).2, 1, one_pos, fun u hu hh t => ?_, fun t ht => by simpa using (h0 t ht).1⟩
  have h1 : IsHalf e (t + u) ↔ IsHalf e t :=
    forall_congr' fun i => forall_congr' fun j => by rw [Matrix.add_apply, mul_add, hh i j, add_left_inj]
  have h2 : t + u ∈ Λ ↔ t ∈ Λ := ⟨fun h => by simpa using sub_mem h hu, fun h => add_mem h hu⟩
  rw [one_smul]
  unfold halfInd
  by_cases h : t ∈ Λ ∧ IsHalf e t
  · rw [if_pos h, if_pos ⟨h2.2 h.1, h1.2 h.2⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h2.1 h'.1, h1.1 h'.2⟩]

theorem heisO_resS_symm_right (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (a : WO L T)
    (F : WO S T → ℂ) (w : WO A T) (y : WO L T) :
    heisO ψ S T ((o.resS T).symm (0, a)) F ((o.resS T).symm (w, y)) =
      heisO ψ L T a (fun y' => F ((o.resS T).symm (w, y'))) y := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h0 : symplOH A T w 0 = 0 := by simp [symplOH, symplO, hO]
  rw [h0, zero_add, ← map_add]
  simp

theorem symplO_resS_symm_right {S A L T : HSp D} (o : OrthDec S A L) (t : WO S T) (a : WO L T) :
    symplO S T t ((o.resS T).symm (0, a)) = symplO L T ((o.resS T) t).2 a := by
  rw [o.symplO_resS, AddEquiv.apply_symm_apply]
  simp [symplO, hO]

theorem half_resS_symm_right {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {a : WO L T} (ha : IsHalf e a) :
    IsHalf e ((o.resS T).symm (0, a)) := by
  intro i j
  rw [OrthDec.resS_symm_apply]
  simp only [Matrix.zero_mul, zero_add, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, ha]

def restrRight {m n m' n' m'' n'' : ℕ} (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (h : Mx D m' n' → ℂ)
    (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) (x : Mx D m' n') :
    (Mx D m'' n'' → ℂ) →ₗ[ℂ] (Mx D m'' n'' → ℂ) where
  toFun Φ := fun y => T' (fun t => h (r t).1 * Φ (r t).2) (r.symm (x, y))
  map_add' Φ Φ' := by
    funext w
    have : (fun t => h (r t).1 * (Φ + Φ') (r t).2) =
        (fun t => h (r t).1 * Φ (r t).2) + fun t => h (r t).1 * Φ' (r t).2 := by
      funext t; simp [mul_add]
    rw [this, map_add]; rfl
  map_smul' c Φ := by
    funext w
    have : (fun t => h (r t).1 * (c • Φ) (r t).2) = c • fun t => h (r t).1 * Φ (r t).2 := by
      funext t; exact mul_left_comm _ _ _
    rw [this, map_smul]; rfl

theorem restrRight_apply {m n m' n' m'' n'' : ℕ} (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (h : Mx D m' n' → ℂ)
    (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) (x : Mx D m' n') (Φ : Mx D m'' n'' → ℂ) (y : Mx D m'' n'') :
    restrRight r h T' x Φ y = T' (fun t => h (r t).1 * Φ (r t).2) (r.symm (x, y)) := rfl

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SchrTheta in

theorem isTheta_image (p : SplitPt D k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {f₀ : WO S T → ℂ}
    (hf₀ : IsThetaFunO ψ S T f₀) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) 1 f₀ Tm)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) Φ) :
    IsThetaFunO ψ S T (Tm Φ) := by
  obtain ⟨ε, hε, heq⟩ := p.above
  have hs := p.split
  have he := hs.1
  have hec := hs.2.1
  have he' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by rw [← heq]; linear_combination he' + hec
  obtain ⟨hLL', hX, -, hfin, hden⟩ := OverProof.dualPair hψ hS hT hs hε heq
  exact placeModel_induction ψ _ hLL' hX hfin hden hTm (IsThetaFunO ψ S T) GlobalTheory.WeilVacMove.isTheta_zero
    (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) (fun c _ => GlobalTheory.WeilVacMove.isTheta_smul c)
    (fun x hx g hg => isTheta_heis_fin hψ hg (infPart_half hε heε hx))
    (fun y hy g hg => isTheta_heis_fin hψ hg (infPart_half hε heε' hy))
    hf₀ hΦ

theorem main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ u : WO A S, ∃ (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ ∧ IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ ∧ T₁ (colFun β ζ a) = fun y => Ξ ((o.resS S).symm (u, y)) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ _ V₀ A L S o ζ hζ α α₀ β hsum Ψ a ha LS hLS L₁ L₂ f₁ Ξ hΞ u
  obtain ⟨hL₁, hL₂, hf₁, hSB, ⟨T, hT⟩, hall⟩ := hΞ
  have hΞT : Ξ = T (extFun α₀ β (tensCol Ψ a)) := hall T hT
  have hΨSB : Ψ ∈ SB (Matrix n n' k) := TensSB.of_tensCol_mem hSB ha
  have hsumE := ExtZero.extFun_tensCol_sum D k p n n' V₀ A L S o ζ α α₀ β hsum
  set r := o.resS S with hr
  set h := extFun α β Ψ with hh
  set ΛL := latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _)
    (LS : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛL
  set Λ₁ := latO V₀ S (L₁ : Set (Fin V₀.rank → D.host.E)) (L₂ : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛ₁
  have hbox : ∀ Φ : WO L S → ℂ, (fun t => h (r t).1 * Φ (r t).2) = o.boxS S h Φ := fun Φ => rfl
  have hcol : ∀ Φ, IsSBHalf p.e ΛL Φ → ∃ b ∈ SB (n → k), colFun β ζ b = Φ := fun Φ hΦ =>
    exists_colFun p hζ β (isLattice_span hζ) hLS.1 hΦ
  have hsb : ∀ Φ, IsSBHalf p.e ΛL Φ → IsSBHalf p.e Λ₁ (fun t => h (r t).1 * Φ (r t).2) := by
    intro Φ hΦ
    obtain ⟨b, hb, rfl⟩ := hcol Φ hΦ
    rw [hbox, hh, ← hsumE]
    exact OverProof.isSBHalf_extFun D k p _ _ V₀ S α₀ β L₁ L₂ hL₁ hL₂ _ (Comm.tensCol_mem hΨSB hb)
  refine ⟨restrRight r h T u (halfInd p.e ΛL), restrRight r h T u, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_right o
      (isTheta_image p hψ hL₁ hL₂ hf₁.1 hT (hsb _ (isSBHalf_halfInd p.e ΛL))) u
  · intro Φ hΦ x hx
    funext w
    rw [restrRight_apply]
    have hfun : (fun t => h (r t).1 * (fun t => Φ (t + x)) (r t).2) =
        fun t => (fun t => h (r t).1 * Φ (r t).2) (t + r.symm (0, x)) := by
      funext t
      simp only [map_add, AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero]
    rw [hfun, hT.trans _ (hsb Φ hΦ) _ (half_resS_symm_right o hx), hr, heisO_resS_symm_right]
    rfl
  · intro Φ hΦ y' hy'
    funext w
    rw [restrRight_apply]
    have hfun : (fun t => h (r t).1 * (fun t => ψ (symplO L S t y') * Φ t) (r t).2) =
        fun t => ψ (symplO V₀ S t (r.symm (0, y'))) * (fun t => h (r t).1 * Φ (r t).2) t := by
      funext t
      rw [hr, symplO_resS_symm_right, mul_left_comm]
    rw [hfun, hT.modul _ (hsb Φ hΦ) _ (half_resS_symm_right o hy'), hr, heisO_resS_symm_right]
    rfl
  · rw [one_smul]
  · funext y
    rw [restrRight_apply, hΞT, hsumE]
    rfl

end GlobalTheory.LastTgtSlice

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSlice_lineSum_eq_intertwiner_image : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ u : WO A S, ∃ (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ ∧ IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ ∧ T₁ (colFun β ζ a) = fun y => Ξ ((o.resS S).symm (u, y)) := by
  atlas_forward_decl GlobalTheory.LastTgtSlice.main
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.OpenCompactLat

theorem isOpen_isCompact_of_nsmul {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {Y Y' : Type}
    (A A₀ : AddSubgroup (Matrix Y Y' k)) (ho : IsOpen (A₀ : Set (Matrix Y Y' k)))
    (hc : IsCompact (A₀ : Set (Matrix Y Y' k))) (M N : ℕ) (hM : (M : k) ≠ 0) (hN : (N : k) ≠ 0)
    (h1 : ∀ x ∈ A, M • x ∈ A₀) (h2 : ∀ y ∈ A₀, N • y ∈ A) :
    IsOpen (A : Set (Matrix Y Y' k)) ∧ IsCompact (A : Set (Matrix Y Y' k)) := by
  have hU : IsOpen ((fun x : Matrix Y Y' k => (N : k) • x) '' (A₀ : Set (Matrix Y Y' k))) :=
    (Homeomorph.smulOfNeZero (N : k) hN).isOpenMap _ ho
  have hA : IsOpen (A : Set (Matrix Y Y' k)) := by
    refine A.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hU.mem_nhds ⟨0, A₀.zero_mem, smul_zero _⟩) ?_)
    rintro _ ⟨y, hy, rfl⟩
    change (N : k) • y ∈ A
    rw [Nat.cast_smul_eq_nsmul]
    exact h2 y hy
  refine ⟨hA, IsCompact.of_isClosed_subset (hc.image (continuous_const_smul ((M : k)⁻¹))) (A.isClosed_of_isOpen hA) ?_⟩
  intro x hx
  refine ⟨M • x, h1 x hx, ?_⟩
  change (M : k)⁻¹ • (M • x) = x
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hM, one_smul]

theorem openCompact : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T), Submodule.IsLattice D.host.E LS → Submodule.IsLattice D.host.E LT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y), IsOpen (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) ∧ IsCompact (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) := by
  intro D k _ _ _ _ p S T LS LT hLS hLT Y Y' _ _ _ _ FS FT
  have hF := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hG := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨M, hM, hM'⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (S := S) (T := T) hLS.fg hLT.fg hF.1 hG.1
  obtain ⟨N, hN, hN'⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (S := S) (T := T) hF.1.fg hG.1.fg hLS hLT
  have hcast : ∀ n : ℕ, 0 < n → (n : k) ≠ 0 := fun n hn => by
    have h0 : IsUnit (n : D.host.E) := (Nat.cast_ne_zero.2 hn.ne').isUnit
    have h1 := (h0.map (incA D)).map p.pr
    rw [map_natCast, map_natCast] at h1
    exact h1.ne_zero
  refine isOpen_isCompact_of_nsmul _ _ (GlobalTheory.LocMod.Witness.lat_open (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT hF hG)
    (GlobalTheory.LocMod.Witness.lat_compact (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT hF hG) M N (hcast M hM) (hcast N hN) ?_ ?_
  · intro x hx
    rw [AddSubgroup.mem_comap] at hx ⊢
    rw [map_nsmul]
    exact hM' _ (GlobalTheory.PlaceModel.latO_le_top _ hx)
  · intro y hy
    rw [AddSubgroup.mem_comap] at hy ⊢
    refine GlobalTheory.SplitLinAt.latHalf D k p S T LS LT _ ?_ (Or.inl ?_)
    · rw [map_nsmul]
      exact hN' _ hy
    · exact GlobalTheory.LocMod.Witness.up_half (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT _

end GlobalTheory.OpenCompactLat
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_homLattice_completion_openCompact : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T), Submodule.IsLattice D.host.E LS → Submodule.IsLattice D.host.E LT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y), IsOpen (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) ∧ IsCompact (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) := by
  atlas_forward_decl GlobalTheory.OpenCompactLat.openCompact
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

namespace GlobalTheory.SBOfHalf

theorem exists_sb_ext_eq : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Λ : AddSubgroup (WO S T)), IsOpen ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → IsCompact ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → ∀ Φ : WO S T → ℂ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Y Y' k), GlobalTheory.LocMod.Witness.ext p FS FT Φ' = Φ := by
  intro D k _ _ _ _ p S T Y Y' _ _ _ _ FS FT Λ hAo hAc Φ hΦ
  classical
  set A : AddSubgroup (Matrix Y Y' k) := Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) with hA
  obtain ⟨hsupp, k₀, hk₀, hinv, hsup⟩ := hΦ
  have hkF : ((k₀ : D.host.F)) ≠ 0 := Nat.cast_ne_zero.2 hk₀.ne'
  have hkk : ((k₀ : k)) ≠ 0 := by
    have h := (map_ne_zero (p.π.comp (algebraMap D.host.F (AE D)))).2 hkF
    simpa using h
  have hupA : ∀ a : Matrix Y Y' k, a ∈ A ↔ p.up FS FT a ∈ Λ := fun a => Iff.rfl
  have hnsmul : ∀ (x : Matrix Y Y' k), k₀ • x = (k₀ : k) • x := fun x => by
    rw [← Nat.cast_smul_eq_nsmul k]
  have hup_nsmul : ∀ (x : Matrix Y Y' k), p.up FS FT (k₀ • x) = k₀ • p.up FS FT x := fun x =>
    map_nsmul (GlobalTheory.LocMod.Witness.upH p FS FT) k₀ x
  let f : Matrix Y Y' k → ℂ := fun x => Φ (p.up FS FT x)
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hV : IsOpen {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A} :=
      hAo.preimage (continuous_const_smul _)
    have h0 : (x - x) ∈ {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A} := by
      simp only [sub_self, Set.mem_setOf_eq, smul_zero]; exact A.zero_mem
    have hn := (continuous_sub_right x).continuousAt.preimage_mem_nhds (hV.mem_nhds h0)
    filter_upwards [hn] with y hy
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy
    have hy' : y = x + k₀ • ((k₀ : k)⁻¹ • (y - x)) := by
      rw [hnsmul, smul_smul, mul_inv_cancel₀ hkk, one_smul, add_sub_cancel]
    show Φ (p.up FS FT y) = Φ (p.up FS FT x)
    rw [hy', GlobalTheory.LocMod.Witness.up_add, hup_nsmul]
    exact hinv _ hy (GlobalTheory.LocMod.Witness.up_half p FS FT _) _
  have hcpt : HasCompactSupport f := by
    refine HasCompactSupport.intro (hAc.image (continuous_const_smul ((k₀ : k)⁻¹))) fun x hx => ?_
    by_contra hne
    apply hx
    refine ⟨k₀ • x, ?_, ?_⟩
    · show p.up FS FT (k₀ • x) ∈ Λ
      rw [hup_nsmul]; exact hsup _ hne
    · show (k₀ : k)⁻¹ • k₀ • x = x
      rw [hnsmul, smul_smul, inv_mul_cancel₀ hkk, one_smul]
  refine ⟨⟨f, hloc, hcpt⟩, ?_⟩
  funext t
  rw [GlobalTheory.LocMod.Witness.ext_apply]
  split_ifs with ht
  · show Φ (p.up FS FT (p.down FS FT t)) = Φ t
    rw [GlobalTheory.LocMod.Witness.up_down p FS FT ht]
  · by_contra h
    exact ht (hsupp t (Ne.symm h))

end GlobalTheory.SBOfHalf
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartzBruhat_extByZero_of_splitPlaceHalf : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Λ : AddSubgroup (WO S T)), IsOpen ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → IsCompact ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → ∀ Φ : WO S T → ℂ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Y Y' k), GlobalTheory.LocMod.Witness.ext p FS FT Φ' = Φ := by
  atlas_forward_decl GlobalTheory.SBOfHalf.exists_sb_ext_eq
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModSB

theorem continuous_pi_hO_up {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (y : WO S T) :
    Continuous fun t : Matrix Y Y' k => p.π (hO S T (p.up FS FT t) y) := by
  have h : (fun t : Matrix Y Y' k => p.π (hO S T (p.up FS FT t) y)) = fun t =>
      ∑ a, ∑ b, ∑ c, ∑ d, p.π (incA D (S.gram⁻¹ a b)) * p.π (cA D (y c b)) * p.π (incA D (T.gram c d)) *
        (FT.β * t * FS.γ) d a := by
    funext t
    unfold hO
    simp only [map_sum, map_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [GlobalTheory.LocMod.Place.up, Matrix.map_apply, p.π_ι]
  rw [h]
  have hm : Continuous fun t : Matrix Y Y' k => FT.β * t * FS.γ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ =>
    continuous_finset_sum _ fun d _ => continuous_const.mul (hm.matrix_elem d a)

theorem mul_char_mem_SB : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (y : WO S T), IsHalf (cA D p.e) y → ∀ Φ ∈ SB (Matrix Y Y' k), (fun t => ψ (symplO S T (p.up FS FT t) y) * Φ t) ∈ SB (Matrix Y Y' k) := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT y hy Φ hΦ
  obtain ⟨⟨ψk, hk⟩, hc, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  have hcont := (hc ψk hk).1
  have heq : (fun t => ψ (symplO S T (p.up FS FT t) y) * Φ t) =
      fun t => ((ψk (p.π (hO S T (p.up FS FT t) y)) : Circle) : ℂ) * Φ t := by
    funext t
    rw [GlobalTheory.LocSympl.psi_sympl_up p FS FT ψ ψk hk t y]
  rw [heq]
  have hl : IsLocallyConstant (fun t : Matrix Y Y' k => ((ψk (p.π (hO S T (p.up FS FT t) y)) : Circle) : ℂ)) :=
    ((GlobalTheory.IrredSB.char_isLocallyConstant ψk hcont).comp_continuous (continuous_pi_hO_up p FS FT y)).comp
      (fun z : Circle => (z : ℂ))
  exact ⟨hl.mul hΦ.1, HasCompactSupport.mul_left hΦ.2⟩

end GlobalTheory.ModSB

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_mul_conjugateHalf_character_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (y : WO S T), IsHalf (cA D p.e) y → ∀ Φ ∈ SB (Matrix Y Y' k), (fun t => ψ (symplO S T (p.up FS FT t) y) * Φ t) ∈ SB (Matrix Y Y' k) := by
  atlas_forward_decl GlobalTheory.ModSB.mul_char_mem_SB
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModelExtend

theorem isLattice_span {D : D7} {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) :
    Submodule.IsLattice D.host.E (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) := by
  refine ⟨Submodule.fg_span_singleton ζ, ?_⟩
  have h0 : ζ ≠ 0 := fun h0 => h.2 (by simp [h0])
  rw [Submodule.span_span_of_tower]
  have hr : Module.finrank D.host.E (Fin L.rank → D.host.E) = 1 := by simp [h.1]
  exact (finrank_eq_one_iff_of_nonzero ζ h0).1 hr

open GlobalTheory.LocMod in

theorem exists_placeModel_ext : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S L'' : HSp D) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : GlobalTheory.LocMod.Frame k S.rank n) (FL'' : GlobalTheory.LocMod.Frame k L''.rank Unit) (TL : SB (Matrix Unit n k) →ₗ[ℂ] (WO S L'' → ℂ)), (GlobalTheory.LocMod.Place.ofSplitPt p).IsModel ψ FS FL'' TL → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ ∀ Φ, T₃ (GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FS FL'' Φ) = TL Φ := by
  intro D k _ _ _ _ p ψ hψ hU S L'' ζ₀ hζ LS hLS n _ _ FS FL'' TL hTL
  classical
  set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP
  set Λ := latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v) with hΛ
  obtain ⟨hAo, hAc⟩ := GlobalTheory.T.splitPlace_homLattice_completion_openCompact D k p S L'' LS (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀}) hLS.1
    (isLattice_span hζ) Unit n FS FL''
  have hinj : Function.Injective (Witness.ext P FS FL'') := by
    intro Φ Ψ h
    apply Subtype.ext; funext x
    have := congrFun h (P.up FS FL'' x)
    rwa [Witness.ext_apply, Witness.ext_apply, if_pos (Witness.up_half P FS FL'' x),
      if_pos (Witness.up_half P FS FL'' x), Witness.down_up] at this
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Witness.ext P FS FL'') (LinearMap.ker_eq_bot.2 hinj)
  set T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ) := TL ∘ₗ G with hT₃d
  have hT₃ : ∀ Φ, T₃ (Witness.ext P FS FL'' Φ) = TL Φ := fun Φ => by
    change TL (G (Witness.ext P FS FL'' Φ)) = TL Φ
    rw [← LinearMap.comp_apply G, hG, LinearMap.id_apply]
  have hsb : ∀ Φ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Unit n k), Witness.ext P FS FL'' Φ' = Φ :=
    GlobalTheory.T.exists_schwartzBruhat_extByZero_of_splitPlaceHalf D k P S L'' Unit n FS FL'' Λ hAo hAc
  generalize hA : (Λ.comap (Witness.upH P FS FL'') : AddSubgroup (Matrix Unit n k)) = A at hAo hAc
  have hcl : IsClopen (A : Set (Matrix Unit n k)) := ⟨A.isClosed_of_isOpen hAo, hAo⟩
  let Φ₀ : SB (Matrix Unit n k) := ⟨(A : Set (Matrix Unit n k)).indicator 1,
    (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩
  have e1 : Witness.ext P FS FL'' Φ₀ = halfInd p.e Λ := by
    funext t
    rw [Witness.ext_apply, halfInd]
    change (if IsHalf p.e t then _ else _) = _
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      change (A : Set (Matrix Unit n k)).indicator 1 _ = _
      rw [Set.indicator_apply, ← hA]
      refine if_congr ?_ rfl rfl
      change P.up FS FL'' (P.down FS FL'' t) ∈ Λ ↔ _
      rw [Witness.up_down P FS FL'' ht, and_iff_left ht]
    · rw [if_neg ht, if_neg fun h => ht h.2]
  refine ⟨TL Φ₀, T₃, hTL.theta Φ₀, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, hT₃⟩
  · obtain ⟨Φ', rfl⟩ := hsb Φ hΦ
    let Φ'' : SB (Matrix Unit n k) := ⟨fun s => Φ'.1 (s + P.down FS FL'' x),
      Φ'.2.1.comp_continuous (continuous_add_right _), Φ'.2.2.comp_homeomorph (Homeomorph.addRight _)⟩
    have e2 : (fun t => Witness.ext P FS FL'' Φ' (t + x)) = Witness.ext P FS FL'' Φ'' := by
      funext t
      rw [Witness.ext_apply, Witness.ext_apply, Witness.down_add]
      exact if_congr (Witness.half_add hx) rfl rfl
    rw [e2, hT₃, hT₃, hTL.trans (P.down FS FL'' x) Φ' Φ'' (fun t => rfl), Witness.up_down P FS FL'' hx]
  · obtain ⟨Φ', rfl⟩ := hsb Φ hΦ
    let Φ'' : SB (Matrix Unit n k) := ⟨fun s => ψ (symplO S L'' (P.up FS FL'' s) y) * Φ'.1 s,
      GlobalTheory.T.schwartzBruhat_mul_conjugateHalf_character_splitPlace D k P ψ hψ S L'' Unit n FS FL'' y hy Φ'.1 Φ'.2⟩
    have e2 : (fun t => ψ (symplO S L'' t y) * Witness.ext P FS FL'' Φ' t) = Witness.ext P FS FL'' Φ'' := by
      funext t
      rw [Witness.ext_apply, Witness.ext_apply]
      split_ifs with ht
      · change _ = ψ (symplO S L'' (P.up FS FL'' (P.down FS FL'' t)) y) * _
        rw [Witness.up_down P FS FL'' ht]
      · rw [mul_zero]
    rw [e2, hT₃, hT₃, hTL.modul y hy Φ' Φ'' (fun t => rfl)]
  · rw [one_smul, ← e1, hT₃]

end GlobalTheory.ModelExtend
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlaceModel_extension_lineLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S L'' : HSp D) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : GlobalTheory.LocMod.Frame k S.rank n) (FL'' : GlobalTheory.LocMod.Frame k L''.rank Unit) (TL : SB (Matrix Unit n k) →ₗ[ℂ] (WO S L'' → ℂ)), (GlobalTheory.LocMod.Place.ofSplitPt p).IsModel ψ FS FL'' TL → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ ∀ Φ, T₃ (GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FS FL'' Φ) = TL Φ := by
  atlas_forward_decl GlobalTheory.ModelExtend.exists_placeModel_ext
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineLatModel

variable {D : D7} {S T : HSp D}

theorem sbHalf_of_nsmul {e : AE D} {Λ Λ' : AddSubgroup (WO S T)} {M₁ M₂ : ℕ} (p₁ : 0 < M₁) (p₂ : 0 < M₂)
    (h1 : ∀ u ∈ Λ', M₁ • u ∈ Λ) (h2 : ∀ u ∈ Λ, M₂ • u ∈ Λ') {Φ : WO S T → ℂ} (h : IsSBHalf e Λ Φ) :
    IsSBHalf e Λ' Φ := by
  obtain ⟨a1, k, hk, a2, a3⟩ := h
  refine ⟨a1, M₁ * M₂ * k, Nat.mul_pos (Nat.mul_pos p₁ p₂) hk, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have e : (M₁ * M₂ * k) • u = k • (M₂ • (M₁ • u)) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [e]
    exact a2 _ (nsmul_mem (h1 u hu) M₂) (GlobalTheory.SplitLinAt.isHalf_nsmul (GlobalTheory.SplitLinAt.isHalf_nsmul hh M₁) M₂) t
  · have e : (M₁ * M₂ * k) • t = M₁ • (M₂ • (k • t)) := by
      rw [smul_smul, smul_smul]
    rw [e]
    exact nsmul_mem (h2 _ (a3 t ht)) M₁

theorem isModel_ext : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (L S : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ → IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ → ∀ (n : Type) [Fintype n] [DecidableEq n] (FL : GlobalTheory.LocMod.Frame k L.rank Unit) (FS : GlobalTheory.LocMod.Frame k S.rank n), (GlobalTheory.LocMod.Place.ofSplitPt p).IsModel ψ FL FS (T₁ ∘ₗ GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS) := by
  classical
  intro D k _ _ _ _ p ψ hψ _ L S ζ hζ LS hS g₁ T₁ hg₁ hT n _ _ FL FS
  have he : IsSplitIdem D p.e := p.split
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    exact hζ.2 (by simp)
  have hlat : Submodule.IsLattice D.host.E
      (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) := by
    refine ⟨Submodule.fg_span_singleton ζ, ?_⟩
    rw [Submodule.span_span_of_tower]
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton hζ0, Module.finrank_fin_fun, hζ.1]
  have hA : ∀ u ∈ latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _)
      (fun _ => True), IsHalf p.e u →
      u ∈ latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v) :=
    fun u hu hh => GlobalTheory.SplitLinAt.latHalf D k p L S _ LS u hu (Or.inl hh)
  have hle := GlobalTheory.SplitLinAt.latO_le (S := L) (T := S)
    ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)
  have hT' := (GlobalTheory.SplitLinAt.placeModel_congr hA hle).1 hT
  have dL := GlobalTheory.PlaceModel.isSelfDualC_latFrame L
  have hsb : ∀ Φ, IsSBHalf p.e
      (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v))
      (GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS Φ) := fun Φ => by
    have h0 := GlobalTheory.LocMod.Witness.ext_sb (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS dL hS Φ
    obtain ⟨M₁, p₁, h₁⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (S := L) (T := S) hlat.fg hS.1.fg dL.1 hS.1
    obtain ⟨M₂, p₂, h₂⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (S := L) (T := S) dL.1.fg hS.1.fg hlat hS.1
    exact (GlobalTheory.SplitLinAt.sbHalf_congr hA hle).2 (sbHalf_of_nsmul p₁ p₂ h₁ h₂ h0)
  refine ⟨fun Φ => ?_, fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩
  · exact GlobalTheory.DiagLiftFix.isTheta_placeModel hψ hlat hS.1 he.1 he.2.1 (GlobalTheory.PlaceCoord.infPart_split he) hg₁ T₁ hT' _
      ((GlobalTheory.SplitLinAt.sbHalf_congr hA hle).1 (hsb Φ))
  · rw [LinearMap.comp_apply, LinearMap.comp_apply]
    refine Eq.trans (congrArg T₁ ?_) (hT.trans _ (hsb Φ) _ (GlobalTheory.LocMod.Witness.up_half (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS x))
    funext t
    rw [GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.down_add,
      GlobalTheory.LocMod.Witness.down_up, h]
    exact if_congr (GlobalTheory.LocMod.Witness.half_add (GlobalTheory.LocMod.Witness.up_half (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS x)).symm rfl rfl
  · rw [LinearMap.comp_apply, LinearMap.comp_apply]
    refine Eq.trans (congrArg T₁ ?_) (hT.modul _ (hsb Φ) _ hy)
    funext t
    rw [GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.ext_apply, h]
    split_ifs with ht
    · rw [GlobalTheory.LocMod.Witness.up_down (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS ht]
    · rw [mul_zero]

end GlobalTheory.LineLatModel
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
namespace GlobalTheory.KapStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colExt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (L T : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (s : k), s ≠ 0 → ∀ (FL : GlobalTheory.LocMod.Frame k L.rank Unit), (∀ r, FL.β r () = s * (GlobalTheory.LocMod.Place.ofSplitPt p).pr (ζ r)) → ∀ (a : (n → k) → ℂ) (c : SB (Matrix n Unit k)), (∀ M, c.1 M = a (s⁻¹ • fun r => M r ())) → GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FL (GlobalTheory.LocMod.Frame.ofFinPl β) c = colFun β ζ a := by
  intro D k _ _ _ _ p L T n _ _ β ζ s hs FL hFL a c hc
  classical
  funext y
  rw [GlobalTheory.LocMod.Witness.ext_apply, hc, colFun]
  refine if_congr Iff.rfl ?_ rfl
  congr 1
  funext r
  simp only [GlobalTheory.LocMod.Place.down, GlobalTheory.FinPl.ExtZero.zcol, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, map_sum, map_mul, hFL, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show s⁻¹ * (β.b' r i * p.pr (y i j) * (s * p.pr (incA D (ζ j)))) = _
  field_simp

theorem rowExt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (T L : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p T n) (ζ₀ : Fin L.rank → D.host.E), IsLineVec L ζ₀ → ∀ (FL : GlobalTheory.LocMod.Frame k L.rank Unit), (∀ r, FL.β r () = (GlobalTheory.LocMod.Place.ofSplitPt p).pr (ζ₀ r)) → ∀ (b : (n → k) → ℂ) (Φ : SB (Matrix Unit n k)), (∀ M, Φ.1 M = b (M ())) → GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) (GlobalTheory.LocMod.Frame.ofFinPl β) FL Φ = rowFun β ζ₀ b := by
  intro D k _ _ _ _ p T L n _ _ β ζ hζ FL hFL b Φ hΦ
  classical
  funext x
  rw [GlobalTheory.LocMod.Witness.ext_apply, hΦ, rowFun]
  refine if_congr Iff.rfl ?_ rfl
  congr 1
  set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP
  set f := GlobalTheory.LocMod.Witness.prH P with hf
  have hfa : ∀ a, f a = p.pr (incA D a) := fun _ => rfl
  set h : D.host.E := star ζ ⬝ᵥ Matrix.mulVec L.gram ζ with hh
  have h0 : f h ≠ 0 := (map_ne_zero f).2 hζ.2
  set u : Fin L.rank → k := fun j => f ((Matrix.vecMul (star ζ) L.gram) j) with hu
  have hu1 : ∑ j, u j * f (ζ j) = f h := by
    rw [hh, Matrix.dotProduct_mulVec, dotProduct, map_sum]
    exact Finset.sum_congr rfl fun j _ => (map_mul f _ _).symm
  have hγ : ∀ j, FL.γ () j = (f h)⁻¹ * u j := fun j => by
    have h1 : ∀ i, f (ζ i) * FL.γ () j = (1 : Matrix _ _ k) i j := fun i => by
      rw [← FL.βγ, Matrix.mul_apply]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact congrArg (· * _) (hFL i).symm
    have h2 : u j = f h * FL.γ () j := by
      rw [← hu1, Finset.sum_mul]
      simp only [mul_assoc, h1, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h2, inv_mul_cancel_left₀ h0]
  funext r
  simp only [GlobalTheory.LocMod.Place.down, GlobalTheory.FinPl.ExtZero.zrow, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, hγ, Matrix.map_apply]
  show _ = (f h)⁻¹ * ∑ i, p.pr (∑ j, incA D (Matrix.vecMul (star ζ) L.gram j) * x j i) * β.b i r
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, ← mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_assoc]
  rfl

open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (Lifts InDual resUnit) in

theorem fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : MeasureTheory.Measure k), ν.IsAddHaarMeasure → ∀ (n : Type) [Fintype n] [DecidableEq n] (χ : AddChar k Circle) (hχ : HasConductor χ 1) (q : Unif k) (ψk : AddChar k Circle) (xi s : k), (∀ x, ψk x = χ (xi * x)) → s ≠ 0 → ∀ w : 𝒪[k]ˣ, -(xi * s) = ((w : 𝒪[k]) : k) → ∀ Q : Pair k n, ∃ (C : ℂ) (c : SB (Matrix n Unit k)) (Ψ : SB (Matrix Unit n k)), (∀ M, c.1 M = charInd (resChar χ hχ q) Q (s⁻¹ • fun r => M r ())) ∧ (∀ M, Ψ.1 M = cosetInd q Q.lat ((GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.resUnit w)⁻¹ • Q).red (M ())) ∧ ∀ η, C * Ψ.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ()) := by
  intro k _ _ _ _ _ _ ν hν n _ _ χ hχ q ψk xi s hψk hs w hw Q
  classical
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  haveI := hν
  obtain ⟨F, hF⟩ := GlobalTheory.FinPl.CosetPairing.exists_lifts Q
  set wk : k := ((w : 𝒪[k]) : k) with hwk
  set wi : k := (((w⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) with hwi
  have hww : wk * wi = 1 := by rw [hwk, hwi, ← Subring.coe_mul, Units.mul_inv]; rfl
  have hF' : Lifts Q.lat (wi • F) ((resUnit w)⁻¹ • Q).red := fun y => by
    obtain ⟨t, ht, hr⟩ := hF y
    refine ⟨(w⁻¹ : 𝒪[k]ˣ) * t, by rw [smul_dotProduct, ← ht]; rfl, ?_⟩
    rw [map_mul, hr]
    rfl
  let L' : Submodule 𝒪[k] (n → k) := Q.lat.comap ((LinearMap.lsmul k (n → k) s⁻¹).restrictScalars 𝒪[k])
  have hc : (fun M : Matrix n Unit k => charInd (resChar χ hχ q) Q (s⁻¹ • fun r => M r ())) ∈ SB (Matrix n Unit k) :=
    GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.SBFacts.charInd_mem _ Q) (s := fun y => Matrix.of fun r _ => s * y r)
      (by fun_prop) (continuous_pi fun r => continuous_pi fun _ => by simp only [Matrix.of_apply]; fun_prop) fun M => by
        ext r u
        simp [hs]
  have hΨ : (fun M : Matrix Unit n k => cosetInd q Q.lat ((resUnit w)⁻¹ • Q).red (M ())) ∈ SB (Matrix Unit n k) :=
    GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB k n q Q.lat _) (s := fun y => Matrix.of fun _ r => y r)
      (by fun_prop) (continuous_pi fun _ => continuous_pi fun r => by simp only [Matrix.of_apply]; fun_prop) fun M => rfl
  refine ⟨∫ y, vecInd L' y ∂(MeasureTheory.Measure.pi fun _ => ν), ⟨_, hc⟩, ⟨_, hΨ⟩, fun _ => rfl, fun _ => rfl, fun η => ?_⟩
  set η' : n → k := η () - q.inv • wi • F with hη'
  have e1 : cosetInd q Q.lat ((resUnit w)⁻¹ • Q).red (η ()) = dualInd Q.lat η' := by
    rw [← GlobalTheory.FinPl.CosetPairing.cosetInd_add q hF' η', hη', sub_add_cancel]
  have e2 : ∀ y : n → k, charInd (resChar χ hχ q) Q (s⁻¹ • y) * (ψk (-1 * (η () ⬝ᵥ y)) : ℂ) =
      vecInd L' y * (χ (wk * s⁻¹ * (η' ⬝ᵥ y)) : ℂ) := fun y => by
    by_cases hy : s⁻¹ • y ∈ Q.lat
    · have hy' : y ∈ L' := hy
      obtain ⟨t, ht, hr⟩ := hF ⟨_, hy⟩
      have hr' : Q.ev (s⁻¹ • y) = residue 𝒪[k] t := ((Q.hasVal_fn ⟨_, hy⟩).ev_eq).trans hr.symm
      rw [charInd, vecInd, vecInd, if_pos hy, if_pos hy', hr', ← map_neg, resChar_residue, hψk, mul_one, one_mul,
        ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      have ht' : (t : k) = s⁻¹ * (F ⬝ᵥ y) := by rw [ht]; simp
      have hx : xi = -wk * s⁻¹ := by rw [← hw]; field_simp
      rw [hη', sub_dotProduct, smul_dotProduct, smul_dotProduct, Subring.coe_neg, ht', hx, smul_eq_mul, smul_eq_mul]
      linear_combination (q.inv * s⁻¹ * (F ⬝ᵥ y)) * hww
    · have hy' : y ∉ L' := hy
      rw [charInd, vecInd, vecInd, if_neg hy, if_neg hy', mul_zero, zero_mul, zero_mul]
  show _ * cosetInd q Q.lat ((resUnit w)⁻¹ • Q).red (η ()) =
    ∫ y, charInd (resChar χ hχ q) Q (s⁻¹ • y) * (ψk (-1 * (η () ⬝ᵥ y)) : ℂ) ∂(MeasureTheory.Measure.pi fun _ => ν)
  simp only [e2]
  rw [e1, dualInd]
  split_ifs with hd
  · rw [mul_one]
    congr 1
    funext y
    by_cases hy : y ∈ L'
    · have h1 : wk * s⁻¹ * (η' ⬝ᵥ y) ∈ 𝒪[k] := by
        have := mul_mem (w : 𝒪[k]).2 (hd _ hy)
        convert this using 1
        simp [mul_assoc, hwk]
      rw [apply_int_eq_one hχ ⟨_, h1⟩]
      simp
    · rw [vecInd, if_neg hy, zero_mul]
  · rw [mul_zero]
    obtain ⟨y, hy, hn⟩ : ∃ y ∈ Q.lat, η' ⬝ᵥ y ∉ 𝒪[k] := by
      by_contra h
      push Not at h
      exact hd h
    have h0 : η' ⬝ᵥ y ≠ 0 := fun h => hn (h ▸ zero_mem _)
    obtain ⟨z, hz, hz1⟩ : ∃ z, valuation k z ≤ valuation k (η' ⬝ᵥ y) ∧ χ z ≠ 1 := by
      by_contra h
      push Not at h
      exact hn ((Valuation.mem_integer_iff _ _).2 (by simpa using (hχ _).1 h))
    have ht : z / (η' ⬝ᵥ y) ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hz zero_le'
    let t : 𝒪[k] := (w⁻¹ : 𝒪[k]ˣ) * ⟨_, ht⟩
    have hy₀ : s • t • y ∈ L' := by
      show s⁻¹ • s • t • y ∈ Q.lat
      rw [inv_smul_smul₀ hs]
      exact Q.lat.smul_mem t hy
    refine (GlobalTheory.FinPl.Comm.integral_vecInd_eq_zero χ _ _ L' η' hy₀ ?_).symm
    convert hz1 using 2
    show wk * s⁻¹ * (η' ⬝ᵥ s • (wi * (z / (η' ⬝ᵥ y))) • y) = z
    rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, mul_assoc wi, div_mul_cancel₀ _ h0]
    field_simp
    linear_combination z * hww

theorem kapStep : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n : Type) [Fintype n] [DecidableEq n] (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (β : Frame p S n) (LS : Lat S), IsSelfDualC S LS → ∀ (Q : Pair k n) (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ → IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ T₃ (rowFun β ζ₀ (cosetInd q Q.lat (ε • Q).red)) = fun w => T₁ (colFun β ζ (charInd (resChar χ hχ q) Q)) (kap τ S w) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hc n _ _ L S L'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP
  set l : k := p.pr (incA D lam) with hl
  have hl0 : l ≠ 0 := fun h => by rw [h, map_zero] at hlam; exact zero_ne_one hlam
  have hlO : l ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hlam.le
  have hliO : l⁻¹ ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by rw [map_inv₀, hlam, inv_one])
  let w : 𝒪[k]ˣ := ⟨⟨l, hlO⟩, ⟨l⁻¹, hliO⟩, Subtype.ext (mul_inv_cancel₀ hl0), Subtype.ext (inv_mul_cancel₀ hl0)⟩
  refine ⟨(GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.resUnit w)⁻¹, ?_⟩
  intro β LS hLS Q g₁ T₁ hg₁ hT₁
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  have hν : (MeasureTheory.Measure.addHaar : MeasureTheory.Measure k).IsAddHaarMeasure := inferInstance
  have hxi : P.xi ≠ 0 := GlobalTheory.LocMod.Witness.xi_ne P
  set s : k := -l / P.xi with hs
  have hs0 : s ≠ 0 := div_ne_zero (neg_ne_zero.2 hl0) hxi
  have hxs : -(P.xi * s) = ((w : 𝒪[k]) : k) := by
    show -(P.xi * (-l / P.xi)) = l
    field_simp

  have hζne : ∃ r, ζ r ≠ 0 := by
    by_contra h
    push Not at h
    apply hζ.2
    have : ζ = 0 := funext h
    simp [this]
  have hz : (fun r => s * P.pr (ζ r)) ≠ 0 := by
    obtain ⟨r, hr⟩ := hζne
    intro h
    have h1 := congrFun h r
    simp only [Pi.zero_apply] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hs0 h2
    · exact hr ((GlobalTheory.LocMod.Witness.prH P).injective (h2.trans (map_zero _).symm))
  obtain ⟨FL, hFL⟩ := GlobalTheory.KappaModel.exists_frame_col hζ.1 _ hz
  set FS := GlobalTheory.LocMod.Frame.ofFinPl β with hFS
  have hTLS := GlobalTheory.LineLatModel.isModel_ext D k p ψ hψ hU L S ζ hζ LS hLS g₁ T₁ hg₁ hT₁ n FL FS

  let ψk : AddChar k Circle := χ.compAddMonoidHom (AddMonoidHom.mulLeft P.xi)
  have hψk : ∀ x, ψk x = χ (P.xi * x) := fun _ => rfl
  have hk : P.IsChar ψ ψk := (GlobalTheory.LocMod.Place.isChar_ofSplitPt p hc).2 hψk
  set z₀ : Fin L''.rank → k := fun i => P.pr (ζ₀ i) with hz₀
  have hτz : (τ.map P.pr).mulVec z₀ = (-(P.xi * s)) • fun i => P.pr (ζ i) := by
    rw [hxs]
    funext i
    have h2 := congrArg (fun v => GlobalTheory.LocMod.Witness.prH P (v i)) hτ
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.map_mulVec] at h2
    simp only [Pi.smul_apply, smul_eq_mul]
    exact h2
  obtain ⟨FL'', hFL'', TL, hTL, hTLc⟩ := GlobalTheory.KappaModel.kappa_model D k P MeasureTheory.Measure.addHaar hν ψ hψ ψk hk
    L S L'' ζ τ hζ₀.1 hG s z₀ hs0 hτz n FS FL hFL _ hTLS
  obtain ⟨C, c, Ψ, hc1, hΨ, hCΨ⟩ := fourier k MeasureTheory.Measure.addHaar hν n χ hχ q ψk P.xi s hψk hs0 w hxs Q
  obtain ⟨g₃, T₃, hg₃, hT₃, hT₃e⟩ := GlobalTheory.T.exists_splitPlaceModel_extension_lineLattice D k p ψ hψ hU S L'' ζ₀ hζ₀ LS hLS n FS FL'' (C • TL)
    (GlobalTheory.LocMod.Witness.isModel_smul P hTL C)
  refine ⟨g₃, T₃, hg₃, hT₃, ?_⟩
  have hrow := rowExt D k p S L'' n β ζ₀ hζ₀ FL'' hFL'' _ Ψ hΨ
  have hcol := colExt D k p L S n β ζ s hs0 FL hFL _ c hc1
  rw [← hrow, hT₃e, LinearMap.smul_apply, ← map_smul]
  funext w'
  rw [hTLc c (C • Ψ) (fun η => by rw [← hCΨ η]; rfl) w']
  show T₁ (GlobalTheory.LocMod.Witness.ext P FL FS c) _ = _
  rw [hcol]
  rfl

end GlobalTheory.KapStep

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticePairCharacterIndicator_transform_eq_cosetIndicator : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n : Type) [Fintype n] [DecidableEq n] (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (β : Frame p S n) (LS : Lat S), IsSelfDualC S LS → ∀ (Q : Pair k n) (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ → IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ T₃ (rowFun β ζ₀ (cosetInd q Q.lat (ε • Q).red)) = fun w => T₁ (colFun β ζ (charInd (resChar χ hχ q) Q)) (kap τ S w) := by
  atlas_forward_decl GlobalTheory.KapStep.kapStep
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
open scoped TensorProduct

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.BoxDatum

variable {D : D7}

theorem exists_nsmul_mulVec {m m' : ℕ} (M : Matrix (Fin m') (Fin m) D.host.E)
    {L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin m → D.host.E)}
    {L' : Submodule (NumberField.RingOfIntegers D.host.E) (Fin m' → D.host.E)} (hL : L.FG)
    (hL' : Submodule.IsLattice D.host.E L') : ∃ N : ℕ, 0 < N ∧ ∀ t ∈ L, N • M.mulVec t ∈ L' := by
  classical
  obtain ⟨s, rfl⟩ := hL
  choose N hN hm using fun t => GlobalTheory.VacUnique.Den.exists_nsmul_mem_lattice L' hL' (M.mulVec t)
  refine ⟨∏ t ∈ s, N t, Finset.prod_pos fun t _ => hN t, fun t ht => ?_⟩
  induction ht using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul s N (Finset.mem_coe.1 hx), mul_nsmul']
    exact nsmul_mem (hm x) _
  | zero => rw [Matrix.mulVec_zero, nsmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, nsmul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul, smul_comm]; exact L'.smul_mem c hx

theorem exists_nsmul_rat_mul (S : HSp D) {T T' : HSp D} (M : Matrix (Fin T'.rank) (Fin T.rank) D.host.E)
    (LS : Set (Fin S.rank → D.host.E)) {L : Lat T} {L' : Lat T'} (hL : L.FG)
    (hL' : Submodule.IsLattice D.host.E L') (P : Pl D → Prop) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T LS (L : Set _) P, N • (rat M ⬝ u : WO S T') ∈ latO S T' LS (L' : Set _) P := by
  obtain ⟨N, hN, h⟩ := exists_nsmul_mulVec M hL hL'
  refine ⟨N, hN, fun u hu => ?_⟩
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, _, h t ht, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, Pi.smul_apply,
      Matrix.mulVec, dotProduct]
    have e : ∀ l, (incA D (M i l) : AE D) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t l * ∑ k, star (s k) * S.gram k j)) =
        pairA D.host.F 0 α ⊗ₜ[D.host.F] (M i l * (a * t l * ∑ k, star (s k) * S.gram k j)) := fun l => by
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i l) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    simp only [e]
    rw [← TensorProduct.tmul_sum, ← TensorProduct.mk_apply, ← map_nsmul, TensorProduct.mk_apply]
    congr 1
    generalize ∑ k, star (s k) * S.gram k j = c
    simp only [nsmul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => by ring
  | zero => rw [Matrix.mul_zero, nsmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, nsmul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, neg_nsmul]; exact neg_mem hx

theorem isLattice_span {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) :
    Submodule.IsLattice D.host.E (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) := by
  refine ⟨Submodule.fg_span_singleton ζ, ?_⟩
  have h0 : ζ ≠ 0 := fun h0 => h.2 (by simp [h0])
  rw [Submodule.span_span_of_tower]
  have hr : Module.finrank D.host.E (Fin L.rank → D.host.E) = 1 := by simp [h.1]
  exact (finrank_eq_one_iff_of_nonzero ζ h0).1 hr

theorem isHalf_mul {l m n : ℕ} {e : AE D} (M : Mx D l m) {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (M ⬝ u : Mx D l n) :=
  fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_left_comm, hu a j]

variable {S X T L : HSp D}

def boxMap (o : OrthDec X T L) (S : HSp D) (T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (T₃ : (WO S L → ℂ) →ₗ[ℂ] (WO S L → ℂ)) :
    (WO S X → ℂ) →ₗ[ℂ] (WO S X → ℂ) where
  toFun Φ z := T₃ (fun w => T₂ (fun x => Φ ((o.resT S).symm (x, w))) (o.resT S z).1) (o.resT S z).2
  map_add' Φ Φ' := by
    funext z
    have : (fun w => T₂ (fun x => (Φ + Φ') ((o.resT S).symm (x, w))) (o.resT S z).1) =
        (fun w => T₂ (fun x => Φ ((o.resT S).symm (x, w))) (o.resT S z).1) +
          fun w => T₂ (fun x => Φ' ((o.resT S).symm (x, w))) (o.resT S z).1 := by
      funext w
      exact congrFun (T₂.map_add (fun x => Φ ((o.resT S).symm (x, w))) fun x => Φ' ((o.resT S).symm (x, w))) _
    rw [this, map_add]; rfl
  map_smul' c Φ := by
    funext z
    have : (fun w => T₂ (fun x => (c • Φ) ((o.resT S).symm (x, w))) (o.resT S z).1) =
        c • fun w => T₂ (fun x => Φ ((o.resT S).symm (x, w))) (o.resT S z).1 := by
      funext w
      exact congrFun (T₂.map_smul c fun x => Φ ((o.resT S).symm (x, w))) _
    rw [this, map_smul]; rfl

theorem boxMap_apply (o : OrthDec X T L) (T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (T₃ : (WO S L → ℂ) →ₗ[ℂ] (WO S L → ℂ))
    (Φ : WO S X → ℂ) (z : WO S X) : boxMap o S T₂ T₃ Φ z =
      T₃ (fun w => T₂ (fun x => Φ ((o.resT S).symm (x, w))) (o.resT S z).1) (o.resT S z).2 := rfl

theorem boxMap_boxT (o : OrthDec X T L) (T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (T₃ : (WO S L → ℂ) →ₗ[ℂ] (WO S L → ℂ))
    (φ : WO S T → ℂ) (φ' : WO S L → ℂ) : boxMap o S T₂ T₃ (o.boxT S φ φ') = o.boxT S (T₂ φ) (T₃ φ') := by
  funext z
  rw [boxMap_apply]
  have : (fun w => T₂ (fun x => o.boxT S φ φ' ((o.resT S).symm (x, w))) (o.resT S z).1) =
      T₂ φ (o.resT S z).1 • φ' := by
    funext w
    have e : (fun x => o.boxT S φ φ' ((o.resT S).symm (x, w))) = φ' w • φ := by
      funext x
      simp only [OrthDec.boxT, AddEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [this, map_smul]; rfl

theorem half_fst (o : OrthDec X T L) {e : AE D} {t : WO S X} (ht : IsHalf e t) : IsHalf e (o.resT S t).1 :=
  isHalf_mul o.pA ht

theorem half_snd (o : OrthDec X T L) {e : AE D} {t : WO S X} (ht : IsHalf e t) : IsHalf e (o.resT S t).2 :=
  isHalf_mul o.pB ht

theorem half_symm (o : OrthDec X T L) {e : AE D} {x : WO S T} {w : WO S L} (hx : IsHalf e x) (hw : IsHalf e w) :
    IsHalf e ((o.resT S).symm (x, w)) :=
  GlobalTheory.FinPl.Rebase.isHalf_add (isHalf_mul o.jA hx) (isHalf_mul o.jB hw)

theorem half_zero {m n : ℕ} (e : AE D) : IsHalf e (0 : Mx D m n) := fun _ _ => mul_zero _

structure Near (o : OrthDec X T L) (ΛX : AddSubgroup (WO S X)) (ΛT : AddSubgroup (WO S T)) (ΛL : AddSubgroup (WO S L))
    (N : ℕ) : Prop where
  pos : 0 < N
  fst : ∀ t ∈ ΛX, N • (o.resT S t).1 ∈ ΛT
  snd : ∀ t ∈ ΛX, N • (o.resT S t).2 ∈ ΛL
  inl : ∀ u ∈ ΛT, N • (o.resT S).symm (u, 0) ∈ ΛX
  inr : ∀ u ∈ ΛL, N • (o.resT S).symm (0, u) ∈ ΛX

theorem exists_near (o : OrthDec X T L) (LS : Set (Fin S.rank → D.host.E)) {LX : Lat X} {LT : Lat T} {LL : Lat L}
    (hX : Submodule.IsLattice D.host.E LX) (hT : Submodule.IsLattice D.host.E LT) (hL : Submodule.IsLattice D.host.E LL)
    (P : Pl D → Prop) :
    ∃ N, Near o (latO S X LS (LX : Set _) P) (latO S T LS (LT : Set _) P) (latO S L LS (LL : Set _) P) N := by
  obtain ⟨a, ha, h1⟩ := exists_nsmul_rat_mul S o.qA LS hX.fg hT P
  obtain ⟨b, hb, h2⟩ := exists_nsmul_rat_mul S o.qB LS hX.fg hL P
  obtain ⟨c, hc, h3⟩ := exists_nsmul_rat_mul S o.iA LS hT.fg hX P
  obtain ⟨d, hd, h4⟩ := exists_nsmul_rat_mul S o.iB LS hL.fg hX P
  refine ⟨a * b * c * d, by positivity, fun t ht => ?_, fun t ht => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [show a * b * c * d = a * (b * c * d) by ring, mul_nsmul]
    exact nsmul_mem (h1 t ht) _
  · rw [show a * b * c * d = b * (a * c * d) by ring, mul_nsmul]
    exact nsmul_mem (h2 t ht) _
  · rw [show a * b * c * d = c * (a * b * d) by ring, mul_nsmul, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
    exact nsmul_mem (h3 u hu) _
  · rw [show a * b * c * d = d * (a * b * c) by ring, mul_nsmul, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    exact nsmul_mem (h4 u hu) _

section Slices

variable {o : OrthDec X T L} {ΛX : AddSubgroup (WO S X)} {ΛT : AddSubgroup (WO S T)} {ΛL : AddSubgroup (WO S L)} {N : ℕ}
  {e : AE D}

theorem symm_add_left (o : OrthDec X T L) (x u : WO S T) (w : WO S L) (K : ℕ) :
    (o.resT S).symm (x + K • u, w) = (o.resT S).symm (x, w) + K • (o.resT S).symm (u, 0) := by
  rw [← map_nsmul, ← map_add, Prod.smul_mk, Prod.mk_add_mk, nsmul_zero, add_zero]

theorem symm_add_right (o : OrthDec X T L) (x : WO S T) (w u : WO S L) (K : ℕ) :
    (o.resT S).symm (x, w + K • u) = (o.resT S).symm (x, w) + K • (o.resT S).symm (0, u) := by
  rw [← map_nsmul, ← map_add, Prod.smul_mk, Prod.mk_add_mk, nsmul_zero, add_zero]

theorem sb_slice_left (h : Near o ΛX ΛT ΛL N) {Φ : WO S X → ℂ} (hΦ : IsSBHalf e ΛX Φ) (w : WO S L) :
    IsSBHalf e ΛT fun x => Φ ((o.resT S).symm (x, w)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  refine ⟨fun x hx => ?_, N * k, Nat.mul_pos h.pos hk, fun u hu hh x => ?_, fun x hx => ?_⟩
  · have := half_fst o (h1 _ hx)
    rwa [AddEquiv.apply_symm_apply] at this
  · beta_reduce
    rw [symm_add_left, mul_nsmul]
    exact h2 _ (h.inl u hu) (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (half_symm o hh (half_zero e)) N) _
  · have := h.fst _ (h3 _ hx)
    rwa [map_nsmul, AddEquiv.apply_symm_apply, Prod.smul_fst, ← mul_nsmul'] at this

theorem sb_slice_right (h : Near o ΛX ΛT ΛL N) {Φ : WO S X → ℂ} (hΦ : IsSBHalf e ΛX Φ)
    (T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (z : WO S T) :
    IsSBHalf e ΛL fun w => T₂ (fun x => Φ ((o.resT S).symm (x, w))) z := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  have hne : ∀ w, T₂ (fun x => Φ ((o.resT S).symm (x, w))) z ≠ 0 → ∃ x, Φ ((o.resT S).symm (x, w)) ≠ 0 := by
    intro w hw
    by_contra hc
    refine hw ?_
    have : (fun x => Φ ((o.resT S).symm (x, w))) = 0 := funext fun x => by
      by_contra hx; exact hc ⟨x, hx⟩
    rw [this, map_zero]; rfl
  refine ⟨fun w hw => ?_, N * k, Nat.mul_pos h.pos hk, fun u hu hh w => ?_, fun w hw => ?_⟩
  · obtain ⟨x, hx⟩ := hne w hw
    have := half_snd o (h1 _ hx)
    rwa [AddEquiv.apply_symm_apply] at this
  · have : (fun x => Φ ((o.resT S).symm (x, w + (N * k) • u))) = fun x => Φ ((o.resT S).symm (x, w)) := by
      funext x
      rw [symm_add_right, mul_nsmul]
      exact h2 _ (h.inr u hu) (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (half_symm o (half_zero e) hh) N) _
    simp only [this]
  · obtain ⟨x, hx⟩ := hne w hw
    have := h.snd _ (h3 _ hx)
    rwa [map_nsmul, AddEquiv.apply_symm_apply, Prod.smul_snd, ← mul_nsmul'] at this

theorem sb_boxT (h : Near o ΛX ΛT ΛL N) {φ : WO S T → ℂ} {φ' : WO S L → ℂ} (hφ : IsSBHalf e ΛT φ)
    (hφ' : IsSBHalf e ΛL φ') : IsSBHalf e ΛX (o.boxT S φ φ') := by
  obtain ⟨a1, a, ha, a2, a3⟩ := hφ
  obtain ⟨b1, b, hb, b2, b3⟩ := hφ'
  have hN := h.pos
  refine ⟨fun t ht => ?_, N * a * b, by positivity, fun u hu hh t => ?_, fun t ht => ?_⟩
  · rw [← (o.resT S).symm_apply_apply t]
    exact half_symm o (a1 _ (left_ne_zero_of_mul ht)) (b1 _ (right_ne_zero_of_mul ht))
  · simp only [OrthDec.boxT]
    rw [map_add, map_nsmul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
    congr 1
    · rw [show N * a * b = N * b * a by ring, mul_nsmul, mul_nsmul]
      exact a2 _ (nsmul_mem (h.fst u hu) b)
        (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (half_fst o hh) N) b) _
    · rw [mul_nsmul, mul_nsmul]
      exact b2 _ (nsmul_mem (h.snd u hu) a)
        (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (half_snd o hh) N) a) _
  · have p1 := h.inl _ (nsmul_mem (a3 _ (left_ne_zero_of_mul ht)) b)
    have p2 := h.inr _ (nsmul_mem (b3 _ (right_ne_zero_of_mul ht)) a)
    have := add_mem p1 p2
    rw [← nsmul_add, ← map_add, Prod.mk_add_mk, add_zero, zero_add, ← mul_nsmul, ← mul_nsmul, mul_comm b a,
      ← Prod.smul_mk, map_nsmul, Prod.mk.eta, AddEquiv.symm_apply_apply, ← mul_nsmul'] at this
    rwa [mul_assoc]

theorem isPlaceModel_boxMap {ψ : AddChar (AF D.host.F) ℂ} (h : Near o ΛX ΛT ΛL N) {f₂ : WO S T → ℂ} {f₃ : WO S L → ℂ}
    {T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {T₃ : (WO S L → ℂ) →ₗ[ℂ] (WO S L → ℂ)}
    (h₂ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e ΛT 1 f₂ T₂)
    (h₃ : IsPlaceModel ψ (symplO S L) (heisO ψ S L) e ΛL 1 f₃ T₃) :
    IsPlaceModel ψ (symplO S X) (heisO ψ S X) e ΛX 1 (boxMap o S T₂ T₃ (halfInd e ΛX)) (boxMap o S T₂ T₃) := by
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, by rw [one_smul]⟩
  · funext z
    rw [boxMap_apply]
    have e1 : (fun w => T₂ (fun x' => Φ ((o.resT S).symm (x', w) + x)) (o.resT S z).1) =
        ψ (symplOH S T (o.resT S z).1 (o.resT S x).1) • fun w =>
          (fun w => T₂ (fun x' => Φ ((o.resT S).symm (x', w))) ((o.resT S z).1 + (o.resT S x).1)) (w + (o.resT S x).2) := by
      funext w
      have e2 : (fun x' => Φ ((o.resT S).symm (x', w) + x)) =
          fun x' => (fun x' => Φ ((o.resT S).symm (x', w + (o.resT S x).2))) (x' + (o.resT S x).1) := by
        funext x'
        show _ = Φ ((o.resT S).symm ((x', w) + o.resT S x))
        rw [map_add, AddEquiv.symm_apply_apply]
      rw [e2, h₂.trans _ (sb_slice_left h hΦ _) _ (half_fst o hx)]
      rfl
    rw [e1, map_smul, h₃.trans _ (sb_slice_right h hΦ T₂ _) _ (half_snd o hx)]
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    rw [boxMap_apply, o.symplOH_resT, AddChar.map_add_eq_mul, map_add, Prod.fst_add, Prod.snd_add, mul_assoc]
  · funext z
    rw [boxMap_apply]
    have e1 : (fun w => T₂ (fun x' => ψ (symplO S X ((o.resT S).symm (x', w)) y) * Φ ((o.resT S).symm (x', w)))
          (o.resT S z).1) =
        ψ (symplOH S T (o.resT S z).1 (o.resT S y).1) • fun w => ψ (symplO S L w (o.resT S y).2) *
          (fun w => T₂ (fun x' => Φ ((o.resT S).symm (x', w))) ((o.resT S z).1 + (o.resT S y).1)) w := by
      funext w
      have e2 : (fun x' => ψ (symplO S X ((o.resT S).symm (x', w)) y) * Φ ((o.resT S).symm (x', w))) =
          ψ (symplO S L w (o.resT S y).2) • fun x' => ψ (symplO S T x' (o.resT S y).1) *
            (fun x' => Φ ((o.resT S).symm (x', w))) x' := by
        funext x'
        rw [o.symplO_resT, AddEquiv.apply_symm_apply, AddChar.map_add_eq_mul]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e2, map_smul, h₂.modul _ (sb_slice_left h hΦ _) _ (half_fst o hy)]
      simp only [heisO, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, map_smul, h₃.modul _ (sb_slice_right h hΦ T₂ _) _ (half_snd o hy)]
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    rw [boxMap_apply, o.symplOH_resT, AddChar.map_add_eq_mul, map_add, Prod.fst_add, Prod.snd_add, mul_assoc]

end Slices

theorem isTheta_comb {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (c : WO S X →₀ ℂ) {f : WO S X → ℂ}
    (hf : IsThetaFunO ψ S X f) : IsThetaFunO ψ S X (comb ψ S X c f) := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_induction _ (IsThetaFunO ψ S X) (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) GlobalTheory.WeilVacMove.isTheta_zero
    fun u _ => GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u)

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.FinPl.OverProof in

theorem over_boxT : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S X T L'' : HSp D) (o'' : OrthDec X T L'') (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o'' ζ₀ γ γ₀ → ∀ (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → ∀ (f₂ F₂ : WO S T → ℂ) (Ψ₂ : Matrix n'' n k → ℂ), Over ψ β γ LS LT f₂ Ψ₂ F₂ → ∀ (b : (n → k) → ℂ) (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ → IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ → GlobalTheory.FinPl.tensRow Ψ₂ b ∈ SB (Matrix (n'' ⊕ Fin 1) n k) → ∃ g, Over ψ β γ₀ LS LX g (GlobalTheory.FinPl.tensRow Ψ₂ b) (o''.boxT S F₂ (T₃ (rowFun β ζ₀ b))) := by
  intro D k _ _ _ _ p n n'' _ _ _ _ ψ hψ _ S X T L o ζ hζ β γ γ₀ hγ LS LT LX hS hT hX f₂ F₂ Ψ₂ hO b g₃ T₃ hg₃ h₃ hSB
  obtain ⟨T₂, h₂⟩ := hO.2.2.2.2.1
  have hF : F₂ = T₂ (extFun β γ Ψ₂) := hO.2.2.2.2.2 T₂ h₂
  obtain ⟨N, hN⟩ := exists_near (S := S) o (LS : Set _) hX.1 hT.1 (isLattice_span hζ) (· = p.v)
  have h₀ := isPlaceModel_boxMap hN h₂ h₃
  obtain ⟨ε, hε, heq⟩ := p.above
  have hs := p.split
  have he := hs.1
  have hec := hs.2.1
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  obtain ⟨hLL', hXX, -, hfin, hden⟩ := dualPair hψ hS hX hs hε heq
  have hdX : ∀ x ∈ half S X p.e, ∃ k : ℕ, 0 < k ∧ k • x ∈ latO S X (LS : Set _) (LX : Set _) (· = p.v) := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := exists_nsmul_mem_latO' hS.1 hX.1 x (infPart_half hε heε hx)
    refine ⟨k, hk, ?_⟩
    have := (idem_smul_mem hε he heε hkx).1
    rwa [smul_comm, (mem_half S X).1 hx] at this
  have hb := sb_boxT hN (GlobalTheory.isSBHalf_halfInd p.e _) (GlobalTheory.isSBHalf_halfInd p.e _)
  obtain ⟨c, -, hc⟩ := GlobalTheory.FinPl.DatumBack.exists_back ψ hec _ hLL' hXX hfin hdX hden hb fun h0 => by
    have := congrFun h0 0
    rw [OrthDec.boxT_zero] at this
    simp [halfInd, half_zero] at this
  have v₂ := h₂.vac
  have v₃ := h₃.vac
  rw [one_smul] at v₂ v₃
  refine ⟨_, hS, hX, ⟨?_, GlobalTheory.FinPl.Rebase.latVac_image D k p ψ hψ S X LS LS LX LX hS hX hS hX _ _ h₀⟩, hSB, ⟨_, h₀⟩,
    fun T' hT' => ?_⟩
  · rw [hc _ _ h₀, boxMap_boxT, v₂, v₃]
    exact isTheta_comb hψ c (o.isThetaFunO_boxT hO.2.2.1.1 hg₃)
  · beta_reduce
    rw [← placeModel_unique_of_dual ψ _ hLL' hXX hfin hden h₀ hT'
      (isSBHalf_extFun D k p _ n S X β γ₀ LS LX hS hX _ hSB),
      GlobalTheory.FinPl.ExtZero.extFun_tensRow D k p n n'' X T L S o ζ hζ γ γ₀ β hγ Ψ₂ b, boxMap_boxT, hF]

end GlobalTheory.FinPl.BoxDatum

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_datum_boxTensor_line_over_vacuum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S X T L'' : HSp D) (o'' : OrthDec X T L'') (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o'' ζ₀ γ γ₀ → ∀ (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → ∀ (f₂ F₂ : WO S T → ℂ) (Ψ₂ : Matrix n'' n k → ℂ), Over ψ β γ LS LT f₂ Ψ₂ F₂ → ∀ (b : (n → k) → ℂ) (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ → IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ → GlobalTheory.FinPl.tensRow Ψ₂ b ∈ SB (Matrix (n'' ⊕ Fin 1) n k) → ∃ g, Over ψ β γ₀ LS LX g (GlobalTheory.FinPl.tensRow Ψ₂ b) (o''.boxT S F₂ (T₃ (rowFun β ζ₀ b))) := by
  atlas_forward_decl GlobalTheory.FinPl.BoxDatum.over_boxT
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

namespace GlobalTheory.LastTarget

theorem tensRow_eq_phiOne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n n'' : Type} [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (q : Unif k) (Q : Pair k n)
    (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k] (c : 𝓀[k]ˣ) :
    tensRow (latInd Q.lat Λ) (cosetInd q Q.lat (c • Q).red) = phiOne (c • Q) (lastPair q Λ) := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  have h := ((GlobalTheory.LastSteps.lastTwoSteps k n n n'').2.2.2 q Q.lat Λ).1 ⟨(c • Q).red, (c • Q).red_ne⟩
  funext x
  have hx : withRow (x.submatrix Sum.inl id) (x (Sum.inr 0)) = x := by
    ext i j
    rcases i with i | i
    · rfl
    · fin_cases i; rfl
  have h2 := (h (x.submatrix Sum.inl id) (x (Sum.inr 0))).2
  rw [hx] at h2
  exact h2.symm

end GlobalTheory.LastTarget

namespace GlobalTheory.LastTarget

theorem charInd_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n) : charInd χ Q ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have hne : ∀ a, χ a ≠ 0 := fun a ha => by
    have h1 := AddChar.map_add_eq_mul χ a (-a)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, ha, zero_mul] at h1
    exact one_ne_zero h1
  simp only [charInd, vecInd, Q.lat.zero_mem, if_true, mul_one, Pi.zero_apply] at h0
  exact hne _ h0

theorem lastTarget : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k] (Ψ : Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → ∀ u : WO A S, ∃ g, Over ψ β γ₀ LS LX g (phiOne (ε • Q) (lastPair q Λ)) (lastBi o o'' τ Ξ Φ₂ u) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hc n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  obtain ⟨ε, hε⟩ := GlobalTheory.T.latticePairCharacterIndicator_transform_eq_cosetIndicator D k p q ψ hψ hU χ hχ hc n L S L'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  refine ⟨ε, ?_⟩
  intro α α₀ β γ γ₀ hα hγ Q Λ _ Ψ LS LT LX hLS hLT hLX hβQ hγΛ L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂ u
  obtain ⟨g₁, T₁, hg₁, hT₁, hT₁a⟩ := GlobalTheory.T.thetaSlice_lineSum_eq_intertwiner_image D k p n n' ψ hψ hU V₀ A L S o ζ hζ α α₀ β hα Ψ
    (charInd (resChar χ hχ q) Q) (charInd_ne_zero _ Q) LS hLS L₁ L₂ f₁ Ξ hΞ u
  obtain ⟨g₃, T₃, hg₃, hT₃, hT₃b⟩ := hε β LS hLS Q g₁ T₁ hg₁ hT₁
  have hO2 : Over ψ β γ LS LT Φ₂ (latInd Q.lat Λ) Φ₂ :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D) k p n'' n ψ hψ S T β γ LS LT hLS hLT Φ₂ hΦ₂).2.2 hU Q.lat Λ hβQ hγΛ
  have hrow := tensRow_eq_phiOne q Q Λ ε
  have hSB : tensRow (latInd Q.lat Λ) (cosetInd q Q.lat (ε • Q).red) ∈ SB (Matrix (n'' ⊕ Fin 1) n k) :=
    hrow ▸ GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _
  obtain ⟨g, hg⟩ := GlobalTheory.T.splitPlace_datum_boxTensor_line_over_vacuum D k p n n'' ψ hψ hU S X T L'' o'' ζ₀ hζ₀ β γ γ₀ hγ LS LT LX hLS hLT hLX Φ₂ Φ₂
    (latInd Q.lat Λ) hO2 (cosetInd q Q.lat (ε • Q).red) g₃ T₃ hg₃ hT₃ hSB
  refine ⟨g, ?_⟩
  rw [← hrow]
  have hl : lastBi o o'' τ Ξ Φ₂ u = o''.boxT S Φ₂ (T₃ (rowFun β ζ₀ (cosetInd q Q.lat (ε • Q).red))) := by
    rw [hT₃b, hT₁a]
    rfl
  rw [hl]
  exact hg

end GlobalTheory.LastTarget
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeesaw_datum_eq_lattice_pair_over_vacuum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k] (Ψ : Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → ∀ u : WO A S, ∃ g, Over ψ β γ₀ LS LX g (phiOne (ε • Q) (lastPair q Λ)) (lastBi o o'' τ Ξ Φ₂ u) := by
  atlas_forward_decl GlobalTheory.LastTarget.lastTarget
end
