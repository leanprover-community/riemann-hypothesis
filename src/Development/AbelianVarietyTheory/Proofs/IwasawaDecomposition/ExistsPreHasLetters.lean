import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTuple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsPotential
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEmbeddingMemUnitGroup
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsAllLifts
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaarStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SCuIsom
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModulusBbDisjoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelevelCoprimeOfModOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormNonnegOfImagQuadratic
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsHost
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagSpacesOfCh
import BuildAid.ForwardExisting
import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral

section
noncomputable section

namespace GlobalTheory.Mem.RowsModel

open Formalism.BasicNotions NumberField IsDedekindDomain

abbrev Euc (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

def stdOLat (O : Type) [CommRing O] (φ : O →+* ℂ) (n : ℕ) : Rows.OLat O φ (Euc n) := by
  classical
  exact
    { gen := Finset.univ.image (fun i => EuclideanSpace.basisFun (Fin n) ℂ i)
      span_top := by
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
        exact (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq }

theorem mem_stdOLat {O : Type} [CommRing O] {φ : O →+* ℂ} {n : ℕ} {x : Euc n}
    (hx : x ∈ (stdOLat O φ n).gen) : ∃ i, EuclideanSpace.basisFun (Fin n) ℂ i = x := by
  classical
  simpa [stdOLat] using hx

def coordEmb {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) : (Fin n → K) →ₛₗ[σ] Euc n where
  toFun x := WithLp.toLp 2 (fun i => σ (x i))
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

theorem coordEmb_single {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) (i : Fin n) :
    coordEmb σ n (Pi.single i 1) = EuclideanSpace.basisFun (Fin n) ℂ i := by
  ext j
  by_cases h : j = i
  · subst h; simp [coordEmb]
  · simp [coordEmb, h]

theorem coordEmb_basis {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) {ι : Type}
    (b : Module.Basis ι K (Fin n → K)) :
    LinearIndependent ℂ (fun i => coordEmb σ n (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => coordEmb σ n (b i))) = ⊤ := by
  classical
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have hs : ⊤ ≤ Submodule.span ℂ (Set.range (fun i => coordEmb σ n (b i))) := by
    rw [← (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [OrthonormalBasis.coe_toBasis, ← coordEmb_single σ, ← b.sum_repr (Pi.single i 1), map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hs ?_, top_le_iff.mp hs⟩
  rw [← Module.finrank_eq_card_basis b]
  simp

theorem exists_frame {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (c : InnerProductSpace.Core ℂ V) :
    ∃ e : Euc (Module.finrank ℂ V) ≃ₗ[ℂ] V, ∀ x y, inner ℂ x y = c.inner (e x) (e y) := by
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  refine ⟨(stdOrthonormalBasis ℂ V).repr.symm.toLinearEquiv, fun x y => ?_⟩
  exact ((stdOrthonormalBasis ℂ V).repr.symm.inner_map_map x y).symm

variable {B : Base} (C : Cols B)

def ramCore (u : B.Word)
    (h1 : ∀ φ ∈ (C.mem u).A.Mram, ∀ ψ ∈ (C.mem u).A.Mram,
      (C.fm u).ipC 0 ψ φ = starRingEnd ℂ ((C.fm u).ipC 0 φ ψ))
    (h2 : ∀ φ ∈ (C.mem u).A.Mram, φ ≠ 0 → 0 < ((C.fm u).ipC 0 φ φ).re) :
    InnerProductSpace.Core ℂ (C.mem u).A.Mram where
  inner φ ψ := (C.fm u).ipC 0 φ.1 ψ.1
  conj_inner_symm φ ψ := (h1 ψ.1 ψ.2 φ.1 φ.2).symm
  re_inner_nonneg φ := by
    by_cases h : φ.1 = 0
    · show 0 ≤ ((C.fm u).ipC 0 φ.1 φ.1).re
      rw [h]
      simp [MemberForms.ipC]
    · exact (h2 φ.1 φ.2 h).le
  add_left φ ψ χ := by
    show (C.fm u).ipC 0 (φ.1 + ψ.1) χ.1 = _
    simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib]
  smul_left φ ψ r := by
    show (C.fm u).ipC 0 (r • φ.1) ψ.1 = _
    simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm]
  definite φ h := by
    by_contra hne
    have := h2 φ.1 φ.2 (fun h0 => hne (Subtype.ext h0))
    change (C.fm u).ipC 0 φ.1 φ.1 = 0 at h
    rw [h] at this
    simp at this

theorem mram_fd (u : B.Word) : FiniteDimensional ℂ (C.mem u).A.Mram := by
  have := (C.mem u).A.Mu0_fd
  exact Submodule.finiteDimensional_of_le (show (C.mem u).A.Mram ≤ (C.mem u).A.Mu0 from inf_le_left)

def eucCast {a b : ℕ} (h : a = b) : Euc a ≃ₗᵢ[ℂ] Euc b :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr h)

open Classical in

def model (n : C.Tup → ℕ) (D : ℕ)
    (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Euc (n C.mu0)) (eTw : ∀ u μ, (C.PTw u μ).Mt ≃ₗ[ℂ] Euc (n μ))
    (eM : ∀ u, Euc (C.mem u).A.du ≃ₗ[ℂ] (C.mem u).A.Mram)
    (heM : ∀ u φ ψ, inner ℂ φ ψ = (C.fm u).ipC 0 (eM u φ).1 (eM u ψ).1) : RowsRest B C where
  muAt _ := C.mu0
  muAt_conj _ := rfl
  muTw _ := C.mu0
  muTw_conj _ := rfl
  muAt_or _ := Or.inl rfl
  EE := Euc D
  Drows := D
  onb := EuclideanSpace.basisFun (Fin D) ℂ
  Dall := D
  delp := 0
  delp_le_one := zero_le_one
  D_eq := by simp
  EE0 := Euc D
  D0 := D
  onb0 := EuclideanSpace.basisFun (Fin D) ℂ
  FT := Unit
  ft _ := ()
  ft0 _ := ()
  Amb μ := Euc (n μ)
  Mult μ j := Euc (if j = 0 then D else n μ)
  multZero _ := eucCast (if_pos rfl)
  multTop _ := eucCast (if_neg (by have := B.R.two_le_m; omega))
  io _ _ := Matrix.toEuclideanLin (Matrix.of fun a b => if (a : ℕ) = (b : ℕ) then 1 else 0)
  Mtilde μ := stdOLat _ _ (n μ)
  eOp _ := LinearMap.id
  eOp_idem _ := rfl
  eOp_sa _ _ _ := rfl
  Mu u := Euc (C.mem u).A.du
  perCol u μ φ F :=
    if h : μ = C.mu0 then (C.mem u).P.PtilCol (eM u φ).1 ((e0 u).symm (eucCast (congrArg n h) F))
    else (C.PTw u μ).PtilCol (C.e0Tw u μ (eM u φ).1) ((eTw u μ).symm F)
  Bu _ φ F := (∑ a, φ a) * ∑ b, F b
  ze _ _ := 1
  rowsRest_wordColumnUnit_baseTuple _ := rfl
  Mj _ := Euc D
  MjLat _ := stdOLat _ _ D
  kaBig _ _ _ := 0
  kaSmall _ _ _ := 0
  Mt _ _ := Euc D
  MtLat _ _ := stdOLat _ _ D
  MtL _ _ := Fin D → B.LL
  jMt _ _ := coordEmb B.embLL D
  jMt_basis _ _ b := coordEmb_basis B.embLL D b
  MtLat_sub _ _ x hx := by
    obtain ⟨i, rfl⟩ := mem_stdOLat hx
    exact ⟨_, coordEmb_single _ _ i⟩
  eMt _ _ := LinearMap.id
  eMt_idem _ _ := rfl
  eMt_sa _ _ _ _ := rfl
  eMt_LL _ _ x := ⟨x, rfl⟩
  thetaP _ _ := LinearMap.id
  isot _ _ := ⊤
  lamP _ _ _ := 1
  Ij _ _ _ := 0
  jw _ _ _ := 0
  etaJ _ _ := 0
  etaJ_nonneg _ _ := le_rfl
  shaLen _ _ := 0
  shaLen_nonneg _ _ := le_rfl
  eMu := eM
  eMt0 := e0
  perCol_base_eq_PtilCol u φ F := by
    rw [dif_pos rfl]
    rfl
  Bu_linL _ F := ⟨fun φ ψ => by simp [Finset.sum_add_distrib, add_mul],
    fun a φ => by simp [← Finset.mul_sum, mul_assoc]⟩
  Bu_linR _ φ := ⟨fun F G => by simp [Finset.sum_add_distrib, mul_add],
    fun a F => by simp [← Finset.mul_sum, mul_left_comm]⟩
  eMtTw := eTw
  perCol_tie u μ h φ F := dif_neg h
  eMu_isom := heM

end GlobalTheory.Mem.RowsModel

namespace GlobalTheory.Mem

open Formalism.BasicNotions RowsModel in

theorem exists_rowsRest :
    ∀ (B : Base) (C : Cols B) (n : C.Tup → ℕ) (D : ℕ),
      (∀ u, Nonempty ((C.mem u).P.Mt ≃ₗ[ℂ] (Fin (n C.mu0) → ℂ))) →
      (∀ u μ, Nonempty ((C.PTw u μ).Mt ≃ₗ[ℂ] (Fin (n μ) → ℂ))) →
      (∀ u, ∀ φ ∈ (C.mem u).A.Mram, ∀ ψ ∈ (C.mem u).A.Mram,
        (C.fm u).ipC 0 ψ φ = starRingEnd ℂ ((C.fm u).ipC 0 φ ψ)) →
      (∀ u, ∀ φ ∈ (C.mem u).A.Mram, φ ≠ 0 → 0 < ((C.fm u).ipC 0 φ φ).re) →
      ∃ W : RowsRest B C, W.Drows = D ∧ W.D0 = D ∧ (∀ μ, Module.finrank ℂ (W.Amb μ) = n μ) ∧
        (∀ μ, W.eOp μ = LinearMap.id) ∧ ∀ μ j, Module.finrank ℂ (W.Mt μ j) = D := by
  intro B C n D h0 hT h1 h2
  have hf : ∀ u, ∃ e : Euc (C.mem u).A.du ≃ₗ[ℂ] (C.mem u).A.Mram,
      ∀ φ ψ, inner ℂ φ ψ = (C.fm u).ipC 0 (e φ).1 (e ψ).1 := fun u =>
    haveI := mram_fd C u
    exists_frame (ramCore C u (h1 u) (h2 u))
  choose eM heM using hf
  refine ⟨model C n D (fun u => (h0 u).some.trans (WithLp.linearEquiv 2 ℂ _).symm)
    (fun u μ => (hT u μ).some.trans (WithLp.linearEquiv 2 ℂ _).symm) eM heM, rfl, rfl, fun μ => ?_,
    fun _ => rfl, fun _ _ => ?_⟩
  · exact finrank_euclideanSpace_fin
  · exact finrank_euclideanSpace_fin

theorem RowsModel.ipC_cols (B : Base) (u : B.Word)
    (φ ψ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) :
    ((ColsModel.cols B).fm u).ipC 0 φ ψ = ∑ c, starRingEnd ℂ (φ c ()) * ψ c () := by
  refine Finset.sum_congr rfl fun c _ => ?_
  show ((Nat.card PUnit : ℕ) : ℂ)⁻¹ * (starRingEnd ℂ (φ c ()) * ψ c ()) = _
  simp

open Formalism.BasicNotions RowsModel in

theorem exists_cols_rowsRest (B : Base) (D : ℕ) :
    ∃ (C : Cols B) (W : RowsRest B C), W.Drows = D ∧ W.D0 = D ∧ (∀ u, Nontrivial (W.Mu u)) ∧
      (∀ μ, Module.finrank ℂ (W.Amb μ) = 1) ∧ (∀ μ, W.eOp μ = LinearMap.id) ∧
      ∀ μ j, Module.finrank ℂ (W.Mt μ j) = D := by
  classical
  obtain ⟨W, h1, h2, h3, h4, h5⟩ := exists_rowsRest B (ColsModel.cols B) (fun _ => 1) D
    (fun _ => ⟨(LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm⟩)
    (fun _ _ => ⟨(LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm⟩)
    (fun u φ _ ψ _ => by
      rw [ipC_cols, ipC_cols, map_sum]
      exact Finset.sum_congr rfl fun c _ => by simp [mul_comm])
    (fun u φ _ hφ => by
      rw [ipC_cols, Complex.re_sum]
      obtain ⟨c, hc⟩ : ∃ c, φ c () ≠ 0 := by
        by_contra h
        exact hφ (funext fun c => funext fun _ => not_not.mp fun hc => h ⟨c, hc⟩)
      refine Finset.sum_pos' (fun c _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
      · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        positivity
      · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        positivity)
  refine ⟨_, W, h1, h2, fun u => ?_, h3, h4, h5⟩
  have : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  have hne : ((ColsModel.cols B).mem u).A.Mram ≠ ⊥ :=
    MemberTorsor.mram_ne_bot B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) (ColsModel.two_lt_alt B.toPre u)
  have := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact (W.eMu u).toEquiv.nontrivial


end GlobalTheory.Mem

end
end

section
noncomputable section

namespace GlobalTheory.Mem.GJInhab

open Formalism.BasicNotions NumberField IsDedekindDomain

def baseVol (B : Base) (cd : CDHaar) (W : @HSpace B.host.E _ _ B.host.cmStar) : ℝ :=
  letI := B.host.cmStar
  GlobalTheory.Mem.Vol.trueVol B.sp.cm (fun τ : Tau B.R => B.host.emb τ.1) cd W

theorem baseVol_pos (B : Base) (cd : CDHaar) (W : @HSpace B.host.E _ _ B.host.cmStar) : 0 < baseVol B cd W :=
  letI := B.host.cmStar
  GlobalTheory.Mem.Vol.trueVol_pos B.sp.cm (fun τ : Tau B.R => B.host.emb τ.1) cd W

def noJet {R : Ranks} (H : Host R) : ThetaJet R H where
  Sit := Empty
  loc := fun i => i.elim
  l_inert := fun i => i.elim
  jOf := fun i => i.elim
  j_mem := fun i => i.elim
  N0_eq := fun i => i.elim
  N1_eq_exponentN1 := fun i => i.elim
  Sit1 := Empty
  loc1 := fun i => i.elim
  l_inert1 := fun i => i.elim
  j1Of := fun i => i.elim
  firstJetIndex_mem_range := fun i => i.elim
  firstJet_lowerRank_eq := fun i => i.elim
  firstJet_upperRank_eq := fun i => i.elim

def oneJet {R : Ranks} (H : Host R) (hm : 1 ≤ R.m) (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l)
    (hc : H.cls l = .signal ∨ H.cls l = .inertClass) : ThetaJet R H where
  Sit := Unit
  loc := fun _ =>
    haveI : Fact l.Prime := ⟨hl⟩
    { l := l
      five_le_l := h5
      d := 2
      d_even := even_two
      two_le_d := le_rfl
      N0 := R.N 0
      N1 := R.N 1
      Th := 1 }
  l_inert := fun _ => hc
  jOf := fun _ => 1
  j_mem := fun _ => ⟨le_rfl, hm⟩
  N0_eq := fun _ => rfl
  N1_eq_exponentN1 := fun _ => rfl
  Sit1 := Empty
  loc1 := fun i => i.elim
  l_inert1 := fun i => i.elim
  j1Of := fun i => i.elim
  firstJetIndex_mem_range := fun i => i.elim
  firstJet_lowerRank_eq := fun i => i.elim
  firstJet_upperRank_eq := fun i => i.elim

theorem exists_noJet (B : Base) (C : Cols B) (cd : CDHaar) :
    ∃ J : GJStage B C, J.cd = cd ∧ J.vol = baseVol B J.cd ∧ J.jet = noJet B.host ∧
      ∀ u w h, (J.gat u w h).FinClasses := by
  obtain ⟨J, hv, hcd, hj, -, hf⟩ := GJModel.exists_of_jet B C (baseVol B cd) (baseVol_pos B cd) cd
    (noJet B.host) (GJModel.gxOne B) (fun i => i.elim) (fun i => i.elim)
  exact ⟨J, hcd, by rw [hv, hcd], hj, hf⟩

theorem exists_oneJet (B : Base) (C : Cols B) (cd : CDHaar) (hm : 1 ≤ B.R.m) (u : B.Word)
    (h0 : Nonempty ((C.mem u).C.cls 0)) (h1 : Nonempty ((C.mem u).C.cls 1))
    (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l) (hc : B.host.cls l = .signal ∨ B.host.cls l = .inertClass) :
    ∃ J : GJStage B C, J.cd = cd ∧ J.vol = baseVol B J.cd ∧ J.jet = oneJet B.host hm l hl h5 hc ∧
      (∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 ∧
        B.places.resChar (J.jetW i) = l) ∧
      ∀ u w h, (J.gat u w h).FinClasses := by
  obtain ⟨J, hv, hcd, hj, -, hf⟩ := GJModel.exists_of_jet B C (baseVol B cd) (baseVol_pos B cd) cd
    (oneJet B.host hm l hl h5 hc) (GJModel.gxOne B) (fun _ => ⟨u, h0, h1⟩) (fun i => i.elim)
  have key : ∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 := by
    rw [hj]
    exact ⟨(), rfl, rfl, rfl⟩
  obtain ⟨i, hi1, hil, hid⟩ := key
  exact ⟨J, hcd, by rw [hv, hcd], hj, ⟨i, hi1, hil, hid, (J.jetW_l i).trans hil⟩, hf⟩

theorem nonempty_stage (B : Base) (C : Cols B) : Nonempty (GJStage B C) := by
  obtain ⟨cd⟩ := GlobalTheory.T.nonempty_compactDualHaar
  obtain ⟨J, -⟩ := exists_noJet B C cd
  exact ⟨J⟩

theorem inhabited_stage (B : Base) (C : Cols B) :
    (∃ J : GJStage B C, J.vol = baseVol B J.cd) ∧
    (1 ≤ B.R.m → Nonempty ((C.mem B.u₀).C.cls 0) → Nonempty ((C.mem B.u₀).C.cls 1) →
      ∀ l : ℕ, l.Prime → 5 ≤ l → (B.host.cls l = .signal ∨ B.host.cls l = .inertClass) →
        ∃ J : GJStage B C, J.vol = baseVol B J.cd ∧ Nonempty J.jet.Sit ∧
          ∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 ∧
            B.places.resChar (J.jetW i) = l) ∧
    (Nonempty ((C.mem B.u₀).C.cls 0) → Nonempty ((C.mem B.u₀).C.cls 1) →
      ∃ J : GJStage B C, J.vol = baseVol B J.cd ∧ Nonempty J.jet.Sit) := by
  obtain ⟨cd⟩ := GlobalTheory.T.nonempty_compactDualHaar
  refine ⟨?_, fun hm h0 h1 l hl h5 hc => ?_, fun h0 h1 => ?_⟩
  · obtain ⟨J, -, hv, -⟩ := exists_noJet B C cd
    exact ⟨J, hv⟩
  · obtain ⟨J, -, hv, -, ⟨i, hi⟩, -⟩ := exists_oneJet B C cd hm B.u₀ h0 h1 l hl h5 hc
    exact ⟨J, hv, ⟨i⟩, i, hi⟩
  · obtain ⟨l, hl, h5, hc⟩ := GJModel.exists_inert B.host
    have hm := B.R.two_le_m
    obtain ⟨J, -, hv, -, ⟨i, -⟩, -⟩ := exists_oneJet B C cd (by omega) B.u₀ h0 h1 l hl h5 hc
    exact ⟨J, hv, ⟨i⟩⟩

end GlobalTheory.Mem.GJInhab

end
end

section
open Formalism Formalism.BasicNotions

namespace GlobalTheory.Mem

theorem locStage_inhabited : Nonempty GlobalTheory.Mem.LocStage := by
  classical
  choose P AI hT using GlobalTheory.MemLoc.exists_locPrime_tied
  exact ⟨{ loc := fun l _ => P l, locA := fun l _ => AI l, locT := fun l _ => (hT l).some }⟩

end GlobalTheory.Mem
end

section
noncomputable section

namespace GlobalTheory.Mem.SStageInhab

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

theorem ncard_primesOver_eq (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime) :
    ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)).ncard = (placesOver E l).ncard := by
  symm
  apply Set.ncard_congr (fun v _ => v.asIdeal)
  · intro v hv
    refine ⟨v.isPrime, ⟨?_⟩⟩
    have hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
      Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl)) (by simpa using hl.ne_zero)
    refine hm.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ v.asIdeal)) ?_
    rw [Ideal.span_singleton_le_iff_mem]
    simpa [Ideal.under, placesOver] using hv
  · intro a b _ _ h; exact HeightOneSpectrum.ext h
  · rintro P ⟨hP, hP'⟩
    have hmem : ((l:ℕ) : 𝓞 E) ∈ P := by
      have : (l:ℤ) ∈ P.under ℤ := by rw [← hP'.over]; exact Ideal.mem_span_singleton_self _
      simpa [Ideal.under] using this
    refine ⟨⟨P, hP, ?_⟩, hmem, rfl⟩
    rintro rfl
    exact hl.ne_zero (by simpa using hmem)

theorem conjF_ne_id (B : Base) : B.toPre.conjF ≠ AlgHom.id _ _ := by
  letI := B.host.cmStar
  intro h
  have h2 := B.sp.cm.deg2
  have hs : Function.Surjective (algebraMap B.host.F B.host.E) := fun a => by
    have : B.toPre.conjF a = a := by rw [h]; rfl
    exact (B.sp.cm.fixed a).1 this
  have : Module.finrank B.host.F B.host.E = 1 := by
    rw [← Algebra.finrank_eq_one_iff_bijective_algebraMap.symm] ; exact ⟨(algebraMap B.host.F B.host.E).injective, hs⟩
  omega

theorem exists_locAt_split_iff (B : Base) (h2 : Module.finrank B.host.F B.host.E = 2) (hne : B.toPre.conjF ≠ AlgHom.id _ _) (p) :
    ∃ L : Formalism.MainNotions.S.Loc.LocAt B.host.F B.host.E B.toPre.conjF p, (L.split.isSome ↔
    Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)) := by
  obtain ⟨L, hL⟩ := GlobalTheory.LocalData.exists_locAt _ _ B.toPre.conjF h2 p
  by_cases h : Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  · obtain ⟨S⟩ := GlobalTheory.LocSplit.nonempty_splitAt _ _ _ h2 hne p L (by
      rw [ncard_primesOver_eq _ _ L.ellPrime.out]
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> rw [h] <;> exact B.toPre.g_split _)
    exact ⟨{L with split := some S}, by simp [h]⟩
  · exact ⟨L, by simp [hL, h]⟩

theorem nonempty_conj_embedding (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] (d D : ℕ) (h : d ≤ D)
    (b : OrthonormalBasis (Fin d) ℂ EE) : Nonempty (EE →ₗᵢ⋆[ℂ] EuclideanSpace ℂ (Fin D)) := by
  let e := EuclideanSpace.basisFun (Fin D) ℂ
  have ho : Orthonormal ℂ (fun i : Fin d => e (Fin.castLE h i)) := e.orthonormal.comp _ (Fin.castLE_injective h)
  let f : EE →ₛₗ[starRingEnd ℂ] EuclideanSpace ℂ (Fin D) :=
    { toFun := fun x => ∑ i, (inner ℂ x (b i)) • e (Fin.castLE h i)
      map_add' := by intro x y; simp [inner_add_left, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.smul_sum, smul_smul, mul_comm] }
  refine ⟨⟨f, fun x => ?_⟩⟩
  have h1 : inner ℂ (f x) (f x) = ∑ i, (starRingEnd ℂ) (inner ℂ x (b i)) * inner ℂ x (b i) :=
    ho.inner_sum _ _ _
  have h2 := b.sum_inner_mul_inner x x
  have h3 : inner ℂ (f x) (f x) = inner ℂ x x := by
    rw [h1, ← h2]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_conj_symm, mul_comm]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
  have h4 : ‖f x‖^2 = ‖x‖^2 := by exact_mod_cast h3
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h4

theorem exists_innerProductSpace (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ip : V → V → ℂ)
    (hs : ∀ x y, (starRingEnd ℂ) (ip y x) = ip x y) (hp : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (ha : ∀ x y z, ip (x+y) z = ip x z + ip y z) (hm : ∀ x y (r:ℂ), ip (r • x) y = (starRingEnd ℂ) r * ip x y) :
    ∃ (U : Type) (_ : NormedAddCommGroup U) (_ : InnerProductSpace ℂ U) (_ : FiniteDimensional ℂ U) (e : U ≃ₗ[ℂ] V),
      ∀ x y, inner ℂ x y = ip (e x) (e y) := by
  let c : InnerProductSpace.Core ℂ V :=
    { inner := ip, conj_inner_symm := hs
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · have := hm x x 0; subst h; simp at this; simp [this]
        · exact (hp x h).le
      add_left := ha, smul_left := hm
      definite := fun x h => by by_contra h'; have := hp x h'; rw [h] at this; simp at this }
  letI n : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI i : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  exact ⟨V, n, i, inferInstance, LinearEquiv.refl _ _, fun x y => rfl⟩

theorem exists_sStage (B : Base) (C : Cols B) (W : RowsRest B C)
    (Del : ℚ) (hD : 0 < Del)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (letter : B.Word → Fin (B.R.k - 2) → Bool) (hinj : Function.Injective letter)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0))
    (hs : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, ∀ y ∈ (C.mem u).A.Mu0, (starRingEnd ℂ) ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y)
    (hp : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, x ≠ 0 → 0 < ((C.fm u).ipC 0 x x).re)
    (hDD : W.Drows ≤ W.Dall) :
    ∃ S : SStage B C W, S.s.Del = Del ∧ S.s.letter = letter ∧ (∀ u u', Nonempty (S.s.Term u u')) ∧
      ∀ u u', Nonempty (S.s.Pair u u') := by
  have hloc := by
    letI := B.host.cmStar
    exact exists_locAt_split_iff B B.sp.cm.deg2 (conjF_ne_id B)
  choose L hL using hloc
  let pt : Formalism.MainNotions.S.Point B.host.E (B.R.rS + 1) := ⟨[(1, B.R.rS + 1)], by simp, by simp⟩
  have hU := fun u => by
    haveI := (C.mem u).A.Mu0_fd
    exact exists_innerProductSpace (C.mem u).A.Mu0 (fun x y => (C.fm u).ipC 0 x.1 y.1) (fun x y => hs u _ x.2 _ y.2)
      (fun x hx => hp u _ x.2 (fun h => hx (Subtype.ext h)))
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun x y r => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
  choose U n i f e he using hU
  obtain ⟨sE⟩ := nonempty_conj_embedding W.EE _ _ hDD W.onb
  let s : Formalism.MainNotions.S.Draft.SData B.R B.host.F B.host.E B.toPre.conjF B.Word (Tau B.R) B.hcW :=
    { cdScale := fun _ _ => 1, cdScale_pos := fun _ _ => one_pos, Del := Del, Del_pos := hD, cloud_gap := gap
      letter := letter, letter_inj := hinj, u_letter := hu, HH := EuclideanSpace ℂ (Fin W.Dall)
      Cu := U, cuN := n, cuI := i, cuF := f, Pu := fun _ => 0, volN := fun _ => 1, volH := fun _ => 1
      volN_pos := fun _ => one_pos, volH_pos := fun _ => one_pos, Term := fun _ _ => Unit
      aTerm := fun _ _ _ => 0, isId := fun _ => True, inS := fun _ => True, relevant := fun _ => True
      FeqF := fun _ => True, Gterm := fun _ => 0, atP := L, PlF := HeightOneSpectrum (𝓞 B.host.F)
      BBne := fun _ _ => False, generic := fun _ => False, Pair := fun _ _ => Unit
      pfst := fun _ => (), psnd := fun _ => (), s0 := fun _ => 0, scalarPair := fun _ => True
      pval := fun _ => 0, ptOf := fun _ => pt, cTerm := fun _ => 1, massPair := fun _ => 1
      meanCount := fun _ _ _ => 0 }
  exact ⟨{ dsig := fun _ => 1, dsig_pos := fun _ => one_pos, s := s, s_split := hL, s_HH := by simp [s]
           s_Cu := e, s_PlF := Equiv.refl _, s_Cu_isom := he, sEE := sE },
    rfl, rfl, fun _ _ => ⟨()⟩, fun _ _ => ⟨()⟩⟩

theorem nonempty_sStage (B : Base) (C : Cols B) (W : RowsRest B C)
    (Del : ℚ) (hD : 0 < Del)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (letter : B.Word → Fin (B.R.k - 2) → Bool) (hinj : Function.Injective letter)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0))
    (hs : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, ∀ y ∈ (C.mem u).A.Mu0, (starRingEnd ℂ) ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y)
    (hp : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, x ≠ 0 → 0 < ((C.fm u).ipC 0 x x).re)
    (hDD : W.Drows ≤ W.Dall) : Nonempty (SStage B C W) :=
  (exists_sStage B C W Del hD gap letter hinj hu hs hp hDD).elim fun S _ => ⟨S⟩

end GlobalTheory.Mem.SStageInhab

end
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem

theorem exists_relevel_primes_one_mod (R : Ranks) (H₀ : Host R) (N : ℕ) : ∃ H : Host R, H.toHostAx = H₀.toHostAx ∧ H.splitBound = H₀.splitBound ∧ H.ccK = ⊤ ∧ H.TT = H₀.TT ∧ (∀ k, H.g k % (H.QS * H.q * H.d) = 1) ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧ (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) ∧ (∀ k, N < H.g k) ∧ (∀ k, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g k : H.E) ∧ ((H.QS * H.q * H.d : ℕ) : 𝓞 H.E) ∣ π - 1) ∧ H.pde % (H.QS * H.q * H.d) = 1 ∧ H.pde' % (H.QS * H.q * H.d) = 1 := by
  suffices h : ∀ H₁ : Host R, H₁.ccK = ⊤ → ∃ H : Host R, H.toHostAx = H₁.toHostAx ∧ H.splitBound = H₁.splitBound ∧ H.ccK = ⊤ ∧ H.TT = H₁.TT ∧ (∀ k, H.g k % (H.QS * H.q * H.d) = 1) ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧ (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) ∧ (∀ k, N < H.g k) ∧ (∀ k, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g k : H.E) ∧ ((H.QS * H.q * H.d : ℕ) : 𝓞 H.E) ∣ π - 1) ∧ H.pde % (H.QS * H.q * H.d) = 1 ∧ H.pde' % (H.QS * H.q * H.d) = 1 from
    h (UpperTheory.Host.withTop H₀) rfl
  intro H hK
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = H.QS * H.q * H.d := ⟨_, rfl⟩
  have hc1 : 1 < c := by
    have h1 : 0 < H.QS * H.q := Nat.mul_pos H.QS_pos H.q_prime.pos
    have h2 : 1 * H.d ≤ H.QS * H.q * H.d := Nat.mul_le_mul_right _ h1
    have h3 := H.d_prime.one_lt
    omega
  have hmod : ∀ x : ℕ, x ≡ 1 [MOD c] → x % c = 1 := fun x hx => by
    have : x % c = 1 % c := hx
    rwa [Nat.mod_eq_of_lt hc1] at this
  obtain ⟨π₀, g₀, hg₀, hN₀, hK₀, hn₀, hi₀, hm₀⟩ :=
    ImaginaryQuadraticNorm.exists_norm_prime R H c 1 N (by omega) (Nat.coprime_one_left c)
  obtain ⟨M, N', hM0, hcM, hdis⟩ := exists_modulus_bb_disjoint R.r g₀ c hg₀ (by omega)
  have hcop : Nat.Coprime (1 + M) (M ^ 2) := Nat.Coprime.pow_right 2 (by simp)
  obtain ⟨π₁, g₁, hg₁, hN₁, hK₁, hn₁, hi₁, hm₁⟩ :=
    ImaginaryQuadraticNorm.exists_norm_prime R H (M ^ 2) (1 + M) (N' + g₀) (pow_ne_zero 2 hM0) hcop
  have hD := hdis g₁ hg₁ (by omega) hm₁
  have hg₀c : g₀ % c = 1 := hmod _ (by simpa using hm₀)
  have hg₁c : g₁ % c = 1 := by
    apply hmod
    refine (hm₁.of_dvd (hcM.trans (dvd_pow_self M two_ne_zero))).trans ?_
    have h1 : 1 + M ≡ 1 + 0 [MOD c] := Nat.ModEq.add_left 1 ((Nat.modEq_zero_iff_dvd).2 hcM)
    simpa using h1.pow 2
  have hd₀ : (c : 𝓞 H.E) ∣ π₀ - 1 := by
    simpa [Ideal.mem_span_singleton] using hi₀
  have hd₁ : (c : 𝓞 H.E) ∣ π₁ - 1 := by
    have h1 : (c : 𝓞 H.E) ∣ (M : 𝓞 H.E) := Nat.cast_dvd_cast hcM
    have h2 : ((M ^ 2 : ℕ) : 𝓞 H.E) ∣ π₁ - ((1 + M : ℕ) : 𝓞 H.E) := Ideal.mem_span_singleton.1 hi₁
    have h3 : (c : 𝓞 H.E) ∣ π₁ - ((1 + M : ℕ) : 𝓞 H.E) :=
      (Nat.cast_dvd_cast (hcM.trans (dvd_pow_self M two_ne_zero))).trans h2
    have h4 : π₁ - 1 = (π₁ - ((1 + M : ℕ) : 𝓞 H.E)) + M := by push_cast; ring
    rw [h4]
    exact dvd_add h3 h1
  obtain ⟨p, hpN, hp, hpm⟩ := Nat.forall_exists_prime_gt_and_modEq g₁ (q := 15 * c) (a := 1) (by omega)
    (Nat.coprime_one_left _)
  obtain ⟨p', hpN', hp', hpm'⟩ := Nat.forall_exists_prime_gt_and_modEq p (q := 15 * c) (a := 1) (by omega)
    (Nat.coprime_one_left _)
  have hpc : p % c = 1 := hmod _ (hpm.of_mul_left 15)
  have hpc' : p' % c = 1 := hmod _ (hpm'.of_mul_left 15)
  have hp15 : p % 15 = 1 := hpm.of_mul_right c
  have hp15' : p' % 15 = 1 := hpm'.of_mul_right c
  subst hc
  have hlv : ∀ x ∈ ({g₀, g₁, p, p'} : Finset ℕ), x.Prime ∧ x % (H.QS * H.q * H.d) = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h <;> subst h
    · exact ⟨hg₀, hg₀c⟩
    · exact ⟨hg₁, hg₁c⟩
    · exact ⟨hp, hpc⟩
    · exact ⟨hp', hpc'⟩
  have hS : ∀ x ∈ ({g₀, g₁, p, p'} : Finset ℕ), Nat.Coprime x H.QS := by
    intro x hx
    have h1 : Nat.Coprime x (H.QS * H.q * H.d) := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, (hlv x hx).2, Nat.gcd_one_left]
    exact (h1.coprime_mul_right_right).coprime_mul_right_right
  refine ⟨{ H with
    levelPrimes := {g₀, g₁, p, p'}
    g := ![g₀, g₁]
    g_prime := by intro i; fin_cases i <;> simpa
    g_ne := by simp; omega
    g_level := by intro i; fin_cases i <;> simp
    pde := p
    pde' := p'
    pde_prime := hp
    pde'_prime := hp'
    pde_ne := by omega
    pde_level := by constructor <;> simp
    pde_mod := ⟨hp15, hp15'⟩
    pde_ne_g := by intro i; fin_cases i <;> simp <;> omega
    ccK_coprime := fun x _ => by rw [hK, Ideal.absNorm_top]; exact Nat.coprime_one_left x
    level_coprimeS := hS }, rfl, rfl, hK, rfl, ?_, hD, hlv, ?_, ?_, hpc, hpc'⟩
  · intro k
    fin_cases k
    · exact hg₀c
    · exact hg₁c
  · intro k
    fin_cases k
    · exact hN₀
    · show N < g₁
      omega
  · intro k
    fin_cases k
    · exact ⟨π₀, hK₀, hn₀, hd₀⟩
    · exact ⟨π₁, hK₁, hn₁, hd₁⟩

theorem exists_host_level_primes_one_mod : ∀ (R : Ranks), Function.Injective R.h → R.o ^ 64 ≤ 2 ^ R.e → 2 ≤ R.e → ∀ (B N : ℕ) (TT : Finset (R.A)), ∃ H : Host R, H.splitBound = B ∧ N < H.q ∧ N < H.d ∧ H.ccK = ⊤ ∧ H.TT = TT ∧ (∀ k, H.g k % (H.QS * H.q * H.d) = 1) ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧ (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) ∧ (∀ k, N < H.g k) ∧ (∀ k, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g k : H.E) ∧ ((H.QS * H.q * H.d : ℕ) : 𝓞 H.E) ∣ π - 1) ∧ H.pde % (H.QS * H.q * H.d) = 1 ∧ H.pde' % (H.QS * H.q * H.d) = 1 := by
  intro R hinj ho he B N TT
  obtain ⟨H₀, hB, hq, hd, -, hT, -⟩ := UpperTheory.Host.exists_host_of_injective R hinj ho he B N TT
  obtain ⟨H, h1, h2, h3, h4, h5⟩ := exists_relevel_primes_one_mod R H₀ N
  refine ⟨H, h2.trans hB, ?_, ?_, h3, h4.trans hT, h5⟩
  · rw [h1]; exact hq
  · rw [h1]; exact hd

end GlobalTheory.Mem
end

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_host_congruence_primes : ∀ (R : Ranks), Function.Injective R.h → R.o ^ 64 ≤ 2 ^ R.e → 2 ≤ R.e → ∀ (B N : ℕ) (TT : Finset (R.A)), ∃ H : Host R, H.splitBound = B ∧ N < H.q ∧ N < H.d ∧ H.ccK = ⊤ ∧ H.TT = TT ∧ (∀ k, H.g k % (H.QS * H.q * H.d) = 1) ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧ (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) ∧ (∀ k, N < H.g k) ∧ (∀ k, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g k : H.E) ∧ ((H.QS * H.q * H.d : ℕ) : 𝓞 H.E) ∣ π - 1) ∧ H.pde % (H.QS * H.q * H.d) = 1 ∧ H.pde' % (H.QS * H.q * H.d) = 1 := by
  atlas_forward_decl GlobalTheory.Mem.exists_host_level_primes_one_mod
end

section
namespace GlobalTheory.Mem.LevelPrime

section Quadratic

open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

theorem norm_nonneg_of_imag_quadratic (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (x : 𝓞 K) : 0 ≤ Algebra.norm ℤ x := by
  classical
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hne : ComplexEmbedding.conjugate φ ≠ φ := by
    intro h
    exact IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 h)
  have hcard : Fintype.card (K →+* ℂ) = 2 := by rw [Embeddings.card, h2]
  have huniv : (Finset.univ : Finset (K →+* ℂ)) = {ComplexEmbedding.conjugate φ, φ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, hcard]
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K)
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f (x : K)) (fun σ => σ (x : K))
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), huniv, Finset.prod_pair hne,
    ComplexEmbedding.conjugate_coe_eq, mul_comm, Complex.mul_conj, ← Algebra.coe_norm_int] at h1
  have h3 : ((Algebra.norm ℤ x : ℤ) : ℝ) = Complex.normSq (φ x) := by
    apply Complex.ofReal_injective
    rw [← h1]; simp
  have h4 : (0 : ℝ) ≤ ((Algebra.norm ℤ x : ℤ) : ℝ) := h3 ▸ Complex.normSq_nonneg _
  exact_mod_cast h4

theorem exists_prime_norm_of_two_le (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (M : ℕ) (hM : 2 ≤ M) (a : 𝓞 K) (ha : IsCoprime a (M : 𝓞 K)) (N : ℕ) :
    ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by
  obtain ⟨D⟩ := nonempty_rayData_of_ne_zero K M (by omega)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hu : IsUnit ((M : ℕ) : 𝓞 K) := isCoprime_zero_left.1 ha
    have h1 := hu.map (Algebra.norm ℤ)
    have h3 : Algebra.norm ℤ ((M : ℕ) : 𝓞 K) = (M : ℤ) ^ 2 := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 K) (M : ℤ)
      rw [RingOfIntegers.rank, h2] at this
      simpa using this
    rw [h3, isUnit_pow_iff two_ne_zero, Int.isUnit_iff] at h1
    omega
  have hac : IsCoprime (Ideal.span {a}) (Ideal.span {(M : 𝓞 K)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 ha
  obtain ⟨v, hc, hp, hN⟩ := GlobalTheory.Mem.RayPrimes.exists_prime_in_class K h2 M hM D (D.cls (Ideal.span {a})) N
  obtain ⟨x, y, hx0, hy0, hx, hy, hxy⟩ := (D.cls_eq _ _ v.2 hac v.1.ne_bot
    (by simpa using ha0)).1 hc
  rw [Ideal.span_singleton_mul_span_singleton] at hxy
  have hdvd : x ∣ y * a := by
    rw [← Ideal.mem_span_singleton]
    have : y * a ∈ Ideal.span {x} * v.1.asIdeal := by
      rw [hxy]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left this
  obtain ⟨π, hπ⟩ := hdvd
  have hv : v.1.asIdeal = Ideal.span {π} := by
    rw [hπ, ← Ideal.span_singleton_mul_span_singleton] at hxy
    exact mul_left_cancel₀ (by simpa using hx0) hxy
  refine ⟨π, Ideal.absNorm v.1.asIdeal, hp, hN, ?_, ?_⟩
  · rw [hv, Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg (norm_nonneg_of_imag_quadratic K h2 π)]
  · have : π - a = (y - 1) * a - (x - 1) * π := by linear_combination -hπ
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hy) (Ideal.mul_mem_right _ _ hx)

theorem exists_prime_norm : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), M ≠ 0 → ∀ (a : 𝓞 K), IsCoprime a (M : 𝓞 K) → ∀ N : ℕ, ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by
  intro K _ _ _ h2 M hM a ha N
  rcases Nat.lt_or_ge M 2 with h | h
  · obtain rfl : M = 1 := by omega
    obtain ⟨π, p, hp, hN, hn, -⟩ := exists_prime_norm_of_two_le K h2 2 le_rfl 1 isCoprime_one_left N
    exact ⟨π, p, hp, hN, hn, by simp⟩
  · exact exists_prime_norm_of_two_le K h2 M h a ha N

end Quadratic

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

theorem norm_eq_mul_conj {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (x : K) :
    ((Algebra.norm ℚ x : ℚ) : ℂ) = φ x * starRingEnd ℂ (φ x) := by
  classical
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have hne : φ.toRatAlgHom ≠ (ComplexEmbedding.conjugate φ).toRatAlgHom := by
    intro he
    have hc := IsTotallyComplex.isComplex (InfinitePlace.mk φ)
    apply InfinitePlace.isComplex_mk_iff.mp hc
    rw [ComplexEmbedding.isReal_iff]
    ext y
    exact (congrArg (fun f : K →ₐ[ℚ] ℂ => f y) he).symm
  have hu : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) =
      {φ.toRatAlgHom, (ComplexEmbedding.conjugate φ).toRatAlgHom} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, AlgHom.card, h2]
  rw [hu, Finset.prod_pair hne] at h
  exact h

variable {R : Ranks}

theorem sqrtMinusD_mem (H : Host R) : H.sqrtMinusD ∈ H.K :=
  IntermediateField.mem_adjoin_simple_self ℚ _

theorem finrank_K (H : Host R) : Module.finrank ℚ H.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos H.sqrtMinusD_sq

theorem isTotallyComplex_K (H : Host R) : IsTotallyComplex H.K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  set b : H.K := ⟨H.sqrtMinusD, sqrtMinusD_mem H⟩
  have hb : b ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [b] using H.sqrtMinusD_sq
  have h1 := congrArg (InfinitePlace.embedding_of_isReal hw) hb
  rw [map_pow, map_neg, map_natCast] at h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw b)]

theorem norm_K (H : Host R) (x : H.K) :
    (x : H.E) * H.conj (x : H.E) = ((Algebra.norm ℚ x : ℚ) : H.E) := by
  have := isTotallyComplex_K H
  apply H.φ₀.injective
  have h1 : H.φ₀ (H.conj (x : H.E)) = starRingEnd ℂ (H.φ₀ (x : H.E)) :=
    Formalism.HC.HostAx.conjE_apply H.toHostAx _ _
  rw [map_mul, h1, map_ratCast,
    norm_eq_mul_conj (finrank_K H) (H.φ₀.comp (algebraMap H.K H.E)) x]
  rfl

theorem dvd_of_eq_mul_integral {E : Type} [Field E] [NumberField E] {M : ℕ} (hM : M ≠ 0) {n : ℤ} {y : E}
    (hy : IsIntegral ℤ y) (h : (n : E) = M * y) : (M : ℤ) ∣ n := by
  have hM' : (M : E) ≠ 0 := by exact_mod_cast hM
  have hM'' : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have e : y = algebraMap ℚ E ((n : ℚ) / M) := by
    rw [map_div₀, map_intCast, map_natCast, h]; field_simp
  rw [e, isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at hy
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hy
  refine ⟨k, ?_⟩
  have : (n : ℚ) = M * k := by
    have hk' : (k : ℚ) = n / M := by simpa using hk
    rw [hk']; field_simp
  exact_mod_cast this

theorem exists_norm_prime : ∀ (R : Ranks) (H : Host R) (M a N : ℕ), M ≠ 0 → Nat.Coprime a M →
    ∃ (π : 𝓞 H.E) (p : ℕ), p.Prime ∧ N < p ∧ (π : H.E) ∈ H.K ∧
      (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ π - (a : 𝓞 H.E) ∈ Ideal.span {(M : 𝓞 H.E)} ∧
      p ≡ a ^ 2 [MOD M] := by
  intro R H M a N hM haM
  have := isTotallyComplex_K H
  obtain ⟨π, p, hp, hN, hn, hc⟩ := exists_prime_norm H.K (finrank_K H) M hM (a : 𝓞 H.K)
    (Nat.Coprime.cast haM) N
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hc
  have hπ : ((algebraMap (𝓞 H.K) (𝓞 H.E) π : 𝓞 H.E) : H.E) = ((π : H.K) : H.E) := rfl
  have hnorm : ((π : H.K) : H.E) * H.conj ((π : H.K) : H.E) = (p : H.E) := by
    rw [norm_K, ← Algebra.coe_norm_int, hn]
    simp
  have hx' : algebraMap (𝓞 H.K) (𝓞 H.E) x * (M : 𝓞 H.E) =
      algebraMap (𝓞 H.K) (𝓞 H.E) π - (a : 𝓞 H.E) := by
    have := congrArg (algebraMap (𝓞 H.K) (𝓞 H.E)) hx
    rwa [map_mul, map_sub, map_natCast, map_natCast] at this
  refine ⟨algebraMap (𝓞 H.K) (𝓞 H.E) π, p, hp, hN, ?_, ?_, Ideal.mem_span_singleton'.mpr ⟨_, hx'⟩, ?_⟩
  · rw [hπ]; exact (π : H.K).2
  · rw [hπ]; exact hnorm
  · set y : 𝓞 H.E := algebraMap (𝓞 H.K) (𝓞 H.E) x
    have hy : IsIntegral ℤ (y : H.E) := y.isIntegral_coe
    have hcy : IsIntegral ℤ (H.conj (y : H.E)) := hy.map (H.conj.toAlgHom.restrictScalars ℤ)
    have e : ((π : H.K) : H.E) = a + M * (y : H.E) := by
      have := congrArg (algebraMap (𝓞 H.E) H.E) hx'
      rw [map_mul, map_sub, map_natCast, map_natCast] at this
      rw [← hπ]
      linear_combination -this
    rw [e, map_add, map_mul, map_natCast, map_natCast] at hnorm
    have hd : (M : ℤ) ∣ (p : ℤ) - (a : ℤ) ^ 2 := by
      apply dvd_of_eq_mul_integral (E := H.E) hM
        (y := a * (y : H.E) + a * H.conj (y : H.E) + M * ((y : H.E) * H.conj (y : H.E)))
      · have ha : IsIntegral ℤ (a : H.E) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (a : ℤ)))
        have hMi : IsIntegral ℤ (M : H.E) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (M : ℤ)))
        exact ((ha.mul hy).add (ha.mul hcy)).add (hMi.mul (hy.mul hcy))
      · push_cast
        linear_combination -hnorm
    apply Nat.ModEq.symm
    rw [Nat.modEq_iff_dvd]
    exact_mod_cast hd

end GlobalTheory.Mem.LevelPrime
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem.LevelPrime

theorem window_low {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) :
    (4 * T ^ x / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / x) * (2 : ℝ) ^ (-(2 : ℝ) / x) = T := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
  rw [Nat.cast_one, div_one, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT _), ← Real.rpow_mul hT,
    mul_one_div_cancel hx.ne', Real.rpow_one, h4, ← Real.rpow_mul (by norm_num), mul_right_comm,
    ← Real.rpow_add (by norm_num)]
  have h0 : (2 : ℝ) * (1 / x) + -2 / x = 0 := by ring
  rw [h0, Real.rpow_zero, one_mul]

theorem exists_levCh_gt : ∀ (P : PreCh) (N : ℕ), ∃ L : LevCh P, ∀ u, N < L.T u := by
  intro P N
  have hq8 : P.H.q % 8 = 3 := P.H.hyp.2.2.1
  have hd16 : P.H.d % 16 = 7 := P.H.hyp.2.2.2.1
  have hn : 0 < P.R.n := Nat.pos_of_ne_zero (by unfold Ranks.n; positivity)
  have hq : 0 < P.H.q := by omega
  have hd : 0 < P.H.d := by omega
  have hQ : 0 < P.H.QS := P.H.QS_pos
  have hg0 : 0 < P.H.g 0 := (P.level_cond _ (P.H.g_level 0)).1.pos
  have hg1 : 0 < P.H.g 1 := (P.level_cond _ (P.H.g_level 1)).1.pos
  have hc : 1 < P.H.QS * P.H.q * P.H.d := by
    have h1 : 0 < P.H.QS * P.H.q := Nat.mul_pos hQ hq
    have h2 : P.H.d ≤ P.H.QS * P.H.q * P.H.d := Nat.le_mul_of_pos_left _ h1
    omega
  have hM : P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 ≠ 0 := by positivity
  obtain ⟨π, p, hp, hN, hK, hnorm, hcong, hmod⟩ := exists_norm_prime P.R P.H _ 1
    (N + P.H.pde + P.H.pde') hM (Nat.coprime_one_left _)
  have hmod' : p % (P.H.QS * P.H.q * P.H.d) = 1 := by
    have h := hmod.of_mul_right _
    rw [one_pow] at h
    exact Eq.trans h (Nat.mod_eq_of_lt hc)
  have hx : (0 : ℝ) < (P.R.f : ℝ) * P.R.k := by
    have hf : 0 < P.R.f := by unfold Ranks.f; omega
    have hk : 0 < P.R.k := by have := P.R.m_add_three_le_k; omega
    positivity
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  refine ⟨{ T := fun _ => p
            T_prime := fun _ => hp
            T_cond := fun _ => hmod'
            piT := fun _ => π
            piT_K := fun _ => hK
            piT_norm := fun _ => hnorm
            piT_cong := fun _ => by simpa only [Nat.cast_one] using hcong
            T_ne_pde := fun _ => ⟨by omega, by omega⟩
            duStar := fun _ => 1
            duStar_pos := fun _ => one_pos
            Dstar := 4 * (p : ℝ) ^ ((P.R.f : ℝ) * P.R.k)
            Dstar_pos := by positivity
            GamP := 2
            one_lt_gammaP := by norm_num
            T_win := fun _ => ?_ }, fun _ => by show N < p; omega⟩
  rw [window_low hx hp0.le]
  refine ⟨le_rfl, ?_⟩
  have h1 : (0 : ℝ) ≤ 1 / ((P.R.f : ℝ) * P.R.k) := by positivity
  nlinarith

end GlobalTheory.Mem.LevelPrime
end

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_characters_large : ∀ (P : PreCh) (N : ℕ), ∃ L : LevCh P, ∀ u, N < L.T u := by
  atlas_forward_decl GlobalTheory.Mem.LevelPrime.exists_levCh_gt
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

def hcStdU (k Del : ℕ) (uF uL : ℤ) (c : Fin (k - 2) → Bool) (i : ℕ) : ℚ :=
  if i = 0 then (uF : ℚ) + 1 / 2
  else if h : i - 1 < k - 2 then
    ((k - 2 - (i - 1) : ℕ) : ℚ) * (4 * (Del : ℚ)) - 1 / 2 - (if c ⟨i - 1, h⟩ then (Del : ℚ) else 0)
  else (uL : ℚ) + 1 / 2

theorem hcStdU_zero (k Del : ℕ) (uF uL : ℤ) (c : Fin (k - 2) → Bool) :
    hcStdU k Del uF uL c 0 = (uF : ℚ) + 1 / 2 := by simp [hcStdU]

theorem hcStdU_succ (k Del : ℕ) (uF uL : ℤ) (c : Fin (k - 2) → Bool) (l : ℕ) (h : l < k - 2) :
    hcStdU k Del uF uL c (l + 1) =
      ((k - 2 - l : ℕ) : ℚ) * (4 * (Del : ℚ)) - 1 / 2 - (if c ⟨l, h⟩ then (Del : ℚ) else 0) := by
  unfold hcStdU
  rw [if_neg (Nat.succ_ne_zero l), dif_pos (by simpa using h)]
  rfl

theorem hcStdU_last (k Del : ℕ) (uF uL : ℤ) (c : Fin (k - 2) → Bool) (i : ℕ) (h0 : i ≠ 0)
    (h : ¬ i - 1 < k - 2) : hcStdU k Del uF uL c i = (uL : ℚ) + 1 / 2 := by
  unfold hcStdU
  rw [if_neg h0, dif_neg h]

theorem exists_hcParam_std : ∀ (R : Ranks) (Del hh : ℕ) (uF uL b1 : ℤ), 1 ≤ Del → R.t + 3 ≤ 2 * hh → ((R.k - 2 : ℕ) : ℤ) * (4 * Del) ≤ uF → uL ≤ -1 → -b1 ≤ uL → ∀ c : Fin (R.k - 2) → Bool, ∃ P : HCParam R, (∀ i : Fin (R.k - 1), (P).v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Del : ℚ))) ∧ (∀ j : Fin R.m, (P).b j = (b1 : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ) ∧ (P).e j = (P).b j + hh) ∧ (∀ h : 0 < R.k, (P).u ⟨0, h⟩ = (uF : ℚ) + 1 / 2 ∧ (P).u ⟨R.k - 1, by omega⟩ = (uL : ℚ) + 1 / 2) ∧ ∀ (l : ℕ) (h : l < R.k - 2), (P).u ⟨l + 1, by omega⟩ = (P).v ⟨l, by omega⟩ - 1 / 2 - (if c ⟨l, h⟩ then (Del : ℚ) else 0) := by
  intro R Del hh uF uL b1 hD hhh hF hL hb c
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hDq : (1 : ℚ) ≤ Del := by exact_mod_cast hD
  have hhq : (R.t : ℚ) + 3 ≤ 2 * hh := by exact_mod_cast hhh
  have hFq : ((R.k - 2 : ℕ) : ℚ) * (4 * (Del : ℚ)) ≤ uF := by exact_mod_cast hF
  have hLq : (uL : ℚ) ≤ -1 := by exact_mod_cast hL
  have hbq : -(b1 : ℚ) ≤ uL := by exact_mod_cast hb
  refine ⟨{
    u := fun i => hcStdU R.k Del uF uL c i.1
    v := fun i => ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Del : ℚ))
    b := fun j => (b1 : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ)
    e := fun j => (b1 : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ) + hh
    u_gt_v := ?_
    v_gt_u := ?_
    u_last_gt := ?_
    gap_be := ?_
    gap_eb := ?_
    e_int := ?_
    u_half := ?_
    v_int := ?_
    b_int := ?_ }, fun i => rfl, fun j => ⟨rfl, rfl⟩, fun h => ⟨?_, ?_⟩, fun l h => ?_⟩
  · rintro ⟨i, hi⟩
    rcases i with _ | l
    · simp only [hcStdU_zero, Nat.sub_zero]
      linarith
    · have hl : l < R.k - 2 := by omega
      simp only [hcStdU_succ _ _ _ _ _ l hl]
      have : R.k - 2 - l = (R.k - 2 - (l + 1)) + 1 := by omega
      rw [this]
      push_cast
      split_ifs <;> linarith
  · rintro ⟨i, hi⟩
    by_cases hl : i < R.k - 2
    · simp only [hcStdU_succ _ _ _ _ _ i hl]
      split_ifs <;> linarith
    · simp only
      rw [hcStdU_last _ _ _ _ _ _ (by omega) (by simpa using hl)]
      have : R.k - 2 - i = 0 := by omega
      rw [this]
      push_cast
      linarith
  · intro h h'
    simp only
    rw [hcStdU_last _ _ _ _ _ _ (by omega) (by omega)]
    push_cast
    linarith
  · intro j
    linarith
  · intro j h
    push_cast
    linarith
  · intro j
    exact ⟨b1 + j.1 * (2 * hh) + hh, by push_cast; ring⟩
  · rintro ⟨i, hi⟩
    rcases i with _ | l
    · exact ⟨uF, hcStdU_zero _ _ _ _ _⟩
    · by_cases hl : l < R.k - 2
      · refine ⟨((R.k - 2 - l : ℕ) : ℤ) * (4 * Del) - 1 - (if c ⟨l, hl⟩ then (Del : ℤ) else 0), ?_⟩
        simp only [hcStdU_succ _ _ _ _ _ l hl]
        split_ifs <;> push_cast <;> ring
      · exact ⟨uL, hcStdU_last _ _ _ _ _ _ (by simp) (by simpa using hl)⟩
  · intro i
    exact ⟨((R.k - 2 - i.1 : ℕ) : ℤ) * (4 * Del), by push_cast; ring⟩
  · intro j
    exact ⟨b1 + j.1 * (2 * hh), by push_cast; ring⟩
  · exact hcStdU_zero R.k Del uF uL c
  · exact hcStdU_last R.k Del uF uL c (R.k - 1) (by omega) (by omega)
  · exact hcStdU_succ R.k Del uF uL c l h

end GlobalTheory.Mem
end

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_parameter_formula : ∀ (R : Ranks) (Del hh : ℕ) (uF uL b1 : ℤ), 1 ≤ Del → R.t + 3 ≤ 2 * hh → ((R.k - 2 : ℕ) : ℤ) * (4 * Del) ≤ uF → uL ≤ -1 → -b1 ≤ uL → ∀ c : Fin (R.k - 2) → Bool, ∃ P : HCParam R, (∀ i : Fin (R.k - 1), (P).v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Del : ℚ))) ∧ (∀ j : Fin R.m, (P).b j = (b1 : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ) ∧ (P).e j = (P).b j + hh) ∧ (∀ h : 0 < R.k, (P).u ⟨0, h⟩ = (uF : ℚ) + 1 / 2 ∧ (P).u ⟨R.k - 1, by omega⟩ = (uL : ℚ) + 1 / 2) ∧ ∀ (l : ℕ) (h : l < R.k - 2), (P).u ⟨l + 1, by omega⟩ = (P).v ⟨l, by omega⟩ - 1 / 2 - (if c ⟨l, h⟩ then (Del : ℚ) else 0) := by
  atlas_forward_decl GlobalTheory.Mem.exists_hcParam_std
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem exists_preCh_of_prescribed : ∀ (R : Ranks) (H : Host R) (u0 : R.A), H.ccK = ⊤ → (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) → Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) → ∀ (M : ℕ), 0 < M → ∀ (c : Fin M → Fin (R.k - 2) → Bool) (Del hh : ℕ) (uF uL b1 : Tau R → ℤ), 1 ≤ Del → R.t + 3 ≤ 2 * hh → (∀ τ, ((R.k - 2 : ℕ) : ℤ) * (4 * Del) ≤ uF τ ∧ uL τ ≤ -1 ∧ -b1 τ ≤ uL τ) → ∃ hcW : Fin M → Tau R → HCParam R, (∀ u τ, (∀ i : Fin (R.k - 1), (hcW u τ).v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Del : ℚ))) ∧ (∀ j : Fin R.m, (hcW u τ).b j = (b1 τ : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ) ∧ (hcW u τ).e j = (hcW u τ).b j + hh) ∧ (∀ h : 0 < R.k, (hcW u τ).u ⟨0, h⟩ = (uF τ : ℚ) + 1 / 2 ∧ (hcW u τ).u ⟨R.k - 1, by omega⟩ = (uL τ : ℚ) + 1 / 2) ∧ ∀ (l : ℕ) (h : l < R.k - 2), (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if c u ⟨l, h⟩ then (Del : ℚ) else 0)) ∧ ∃ P : PreCh, P.R = R ∧ HEq P.H ({ H with u0 := u0 } : Host R) ∧ P.Word = Fin M ∧ HEq P.hcW hcW := by
  intro R H u0 hcc hlev hBB M hM c Del hh uF uL b1 hDel hhh hends
  choose hcW hW using fun (u : Fin M) (τ : Tau R) =>
    GlobalTheory.T.harish_chandra_parameter_formula R Del hh (uF τ) (uL τ) (b1 τ) hDel hhh (hends τ).1 (hends τ).2.1 (hends τ).2.2 (c u)
  refine ⟨hcW, hW, ?_⟩
  have hb : ∀ u u' τ, (hcW u τ).b = (hcW u' τ).b := fun u u' τ => funext fun j => by
    rw [((hW u τ).2.1 j).1, ((hW u' τ).2.1 j).1]
  refine ⟨{ R := R
            H := { H with u0 := u0 }
            ccK_top := hcc
            level_cond := hlev
            BB_disj := hBB
            Word := Fin M
            u₀ := ⟨0, hM⟩
            hcW := hcW
            hcW_v := fun u τ => funext fun i => by rw [(hW u τ).1 i, (hW _ τ).1 i]
            hcW_b := fun u τ => hb _ _ τ
            hcW_e := fun u τ => funext fun j => by
              rw [((hW u τ).2.1 j).2, ((hW _ τ).2.1 j).2, hb u ⟨0, hM⟩ τ]
            hcW_first := fun u τ h => by rw [((hW u τ).2.2.1 h).1, ((hW _ τ).2.2.1 h).1]
            hcW_last := fun u τ h => by rw [((hW u τ).2.2.1 h).2, ((hW _ τ).2.2.1 h).2] },
    rfl, HEq.rfl, rfl, HEq.rfl⟩

end GlobalTheory.Mem
end

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harish_chandra_weights : ∀ (R : Ranks) (H : Host R) (u0 : R.A), H.ccK = ⊤ → (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) → Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) → ∀ (M : ℕ), 0 < M → ∀ (c : Fin M → Fin (R.k - 2) → Bool) (Del hh : ℕ) (uF uL b1 : Tau R → ℤ), 1 ≤ Del → R.t + 3 ≤ 2 * hh → (∀ τ, ((R.k - 2 : ℕ) : ℤ) * (4 * Del) ≤ uF τ ∧ uL τ ≤ -1 ∧ -b1 τ ≤ uL τ) → ∃ hcW : Fin M → Tau R → HCParam R, (∀ u τ, (∀ i : Fin (R.k - 1), (hcW u τ).v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Del : ℚ))) ∧ (∀ j : Fin R.m, (hcW u τ).b j = (b1 τ : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ) ∧ (hcW u τ).e j = (hcW u τ).b j + hh) ∧ (∀ h : 0 < R.k, (hcW u τ).u ⟨0, h⟩ = (uF τ : ℚ) + 1 / 2 ∧ (hcW u τ).u ⟨R.k - 1, by omega⟩ = (uL τ : ℚ) + 1 / 2) ∧ ∀ (l : ℕ) (h : l < R.k - 2), (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if c u ⟨l, h⟩ then (Del : ℚ) else 0)) ∧ ∃ P : PreCh, P.R = R ∧ HEq P.H ({ H with u0 := u0 } : Host R) ∧ P.Word = Fin M ∧ HEq P.hcW hcW := by
  atlas_forward_decl GlobalTheory.Mem.exists_preCh_of_prescribed
end

section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem

theorem exists_nat_bound_pre {ι : Type} [Finite ι] (s : ι → ℝ) (c : ℕ) :
    ∃ a : ℕ, c < 4 * a ∧ ∀ i, s i ≤ 2 * (a : ℝ) := by
  obtain ⟨b, hb⟩ := (Set.finite_range s).bddAbove
  obtain ⟨a, ha⟩ := exists_nat_ge b
  refine ⟨a + c + 1, by omega, fun i => ?_⟩
  have h1 : s i ≤ b := hb ⟨i, rfl⟩
  have h2 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have h3 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  push_cast
  linarith

theorem exists_pre_two_words : ∃ B : Pre, Nonempty (PreX B) ∧ 2 ≤ Fintype.card B.Word ∧ B.host.TT.Nonempty ∧ (letI := B.host.cmStar; DiagSpaces B.sp ∧ ∀ j, B.sp.Vneg j = false) ∧ (∃ (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool), 0 < Del ∧ Function.Injective letter ∧ (∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) ∧ ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ = (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)) := by
  obtain ⟨R, hRi, hRo, hR⟩ : ∃ R : Ranks, Function.Injective R.h ∧ R.o ^ 64 ≤ 2 ^ R.e ∧ 2 ≤ R.e := by
    refine ⟨Formalism.MainNotions.Inhab.Rt 0, Formalism.HC.frameCyc_h_injective 2 1, ?_, le_rfl⟩
    have h1 : (Formalism.MainNotions.Inhab.Rt 0).o = 1 := Formalism.HC.cyclicFrame_index 2
    rw [h1, one_pow]
    exact Nat.one_le_two_pow
  obtain ⟨H, -, -, -, hcc, hTT, -, hBB, hlev, hg, hπ, hp, hp'⟩ :=
    GlobalTheory.T.exists_host_congruence_primes R hRi hRo hR 0 (2 * R.f * R.k + 1) {0}
  have hk : 0 < R.k - 2 := by have := R.m_add_three_le_k; omega
  let c : Fin 2 → Fin (R.k - 2) → Bool := fun u _ => decide (u = 0)
  have hc : Function.Injective c := by
    intro u u' h
    have h0 := congrFun h ⟨0, hk⟩
    simp only [c, decide_eq_decide] at h0
    fin_cases u <;> fin_cases u' <;> simp_all
  obtain ⟨hcW, hW, P, hPR, hPH, hPW, hPc⟩ :=
    GlobalTheory.T.exists_harish_chandra_weights R H H.u0 hcc hlev hBB 2 (by norm_num) c 1 (R.t + 3)
      (fun _ => ((R.k - 2 : ℕ) : ℤ) * (4 * (1 : ℕ))) (fun _ => -1) (fun _ => 1) le_rfl (by omega)
      (fun _ => ⟨le_rfl, le_rfl, le_rfl⟩)
  obtain ⟨R', H', hcc', hlev', hBB', Wd, u₀, hcW', hv, hb, he, hf, hl⟩ := P
  dsimp only at hPR hPH hPW hPc
  subst hPR hPW
  have e1 : H' = H := eq_of_heq hPH
  have e2 : hcW' = hcW := eq_of_heq hPc
  subst e1 e2
  rename_i inst
  obtain ⟨a, ha1, ha2⟩ := exists_nat_bound_pre
    (fun x : Fin 2 × Fin (R'.m + 1) × Tau R' => ((Formalism.BasicNotions.Examples₂.lamOf (hcW' x.1 x.2.2) x.2.1.1).spread : ℝ))
    (2 * R'.f * R'.N R'.m + 1)
  let P : PreCh := @PreCh.mk R' H' hcc' hlev' hBB' (Fin 2) inst u₀ hcW' hv hb he hf hl
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_level_characters_large P (4 * a)
  obtain ⟨sp, hT, hY, hA, hV, hz, hD, -⟩ := GlobalTheory.Mem.exists_diagSpaces_ofCh P L
  choose πg hπ1 hπ2 hπ3 using hπ
  have hne : Nonempty (Tau R') := Fintype.card_pos_iff.1 (by
    rw [card_Tau H']; unfold Ranks.f Ranks.n; have := R'.ord_pos; positivity)
  refine ⟨Pre.ofCh P L sp hT hY hA hV hz, ⟨{
      piG := πg
      piG_K := hπ1
      piG_norm := hπ2
      piG_cong := hπ3
      piT := L.piT
      piT_K := L.piT_K
      piT_norm := L.piT_norm
      piT_cong := fun u => Ideal.mem_span_singleton.1 (L.piT_cong u)
      pde_split := ⟨?_, ?_⟩
      ccK_top := hcc'
      e_even := ?_
      hcW_inj := ?_
      a := a
      g_big := ?_
      T_gt := ?_
      a_gt := ?_
      spread_le := ?_ }⟩, ?_, ?_, hD, 1, c, one_pos, hc, ?_, ?_⟩
  · exact (GlobalTheory.HostSplit.ncard_placesOver H'.E H'.pde_prime).symm.trans
      (GlobalTheory.HostSplit.split_of_one_mod R' H' _ H'.pde_prime hp).1
  · exact (GlobalTheory.HostSplit.ncard_placesOver H'.E H'.pde'_prime).symm.trans
      (GlobalTheory.HostSplit.split_of_one_mod R' H' _ H'.pde'_prime hp').1
  · intro j
    refine UpperTheory.Mu.muq_of_const H' (Equiv.refl _)
      (1 + (j.1 : ℤ) * (2 * ((R'.t + 3 : ℕ) : ℤ)) + ((R'.t + 3 : ℕ) : ℤ)) (fun τ => ?_)
    show (hcW' u₀ τ).e j = _
    rw [((hW u₀ τ).2.1 j).2, ((hW u₀ τ).2.1 j).1]
    push_cast
    ring
  · show Function.Injective hcW'
    intro u u' h
    obtain ⟨τ⟩ := hne
    have h1 := (hW u τ).2.2.2 0 hk
    have h2 := (hW u' τ).2.2.2 0 hk
    rw [h, h2] at h1
    have h3 : (if c u' ⟨0, hk⟩ = true then ((1 : ℕ) : ℚ) else 0) = if c u ⟨0, hk⟩ = true then ((1 : ℕ) : ℚ) else 0 :=
      sub_right_injective h1
    clear h h1 h2
    revert h3
    simp only [c]
    revert u u'
    simp [Fin.forall_fin_two]
  · intro i
    have := hg i
    show 2 * R'.f * R'.k < H'.g i - 1
    omega
  · intro u
    have := hL u
    show 4 * (a : ℝ) < (L.T u : ℝ)
    exact_mod_cast this
  · show ((2 * R'.f * R'.N R'.m + 1 : ℕ) : ℝ) < 4 * (a : ℝ)
    exact_mod_cast ha1
  · intro u j hj τ
    exact ha2 (u, ⟨j, Nat.lt_succ_of_le hj⟩, τ)
  · show 2 ≤ @Fintype.card (Fin 2) inst
    rw [Subsingleton.elim inst (Fin.fintype 2), Fintype.card_fin]
  · show H'.TT.Nonempty
    rw [hTT]
    exact Finset.singleton_nonempty _
  · intro w τ l h
    have h' : l + 1 < R'.k - 1 := h
    show (hcW' w τ).v ⟨l, by omega⟩ - (hcW' w τ).v ⟨l + 1, h'⟩ = 4 * 1
    rw [(hW w τ).1, (hW w τ).1]
    have h3 : R'.k - 2 - l = (R'.k - 2 - (l + 1)) + 1 := by omega
    dsimp only
    rw [h3]
    push_cast
    ring
  · intro w τ l h
    have h1 := (hW w τ).2.2.2 l h
    rw [Nat.cast_one] at h1
    exact h1

end GlobalTheory.Mem
end

section
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace StagesInhab

def HasLetters (P : Pre) : Prop :=
  ∃ (Del : ℚ) (letter : P.Word → Fin (P.R.k - 2) → Bool), 0 < Del ∧ Function.Injective letter ∧
    (∀ w τ (l : ℕ) (h : l + 1 < P.R.k - 1), (P.hcW w τ).v ⟨l, by omega⟩ - (P.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) ∧
    ∀ w τ (l : ℕ) (h : l < P.R.k - 2), (P.hcW w τ).u ⟨l + 1, by omega⟩ =
      (P.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)

theorem ipC_conj (B : Base) (u : B.Word)
    (φ ψ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) :
    ((ColsModel.cols B).fm u).ipC 0 ψ φ = starRingEnd ℂ (((ColsModel.cols B).fm u).ipC 0 φ ψ) := by
  rw [RowsModel.ipC_cols, RowsModel.ipC_cols, map_sum]
  exact Finset.sum_congr rfl fun c _ => by simp [mul_comm]

theorem ipC_pos (B : Base) (u : B.Word)
    (φ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) (hφ : φ ≠ 0) :
    0 < (((ColsModel.cols B).fm u).ipC 0 φ φ).re := by
  rw [RowsModel.ipC_cols, Complex.re_sum]
  obtain ⟨c, hc⟩ : ∃ c, φ c () ≠ 0 := by
    by_contra h
    exact hφ (funext fun c => funext fun _ => not_not.mp fun hc => h ⟨c, hc⟩)
  refine Finset.sum_pos' (fun c _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
  · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity
  · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity

theorem exists_rows (B : Base) (D : ℕ) :
    ∃ W : RowsRest B (ColsModel.cols B), W.Drows = D ∧ W.Dall = D ∧ ∀ u, Nontrivial (W.Mu u) := by
  classical
  have hf : ∀ u, ∃ e : RowsModel.Euc ((ColsModel.cols B).mem u).A.du ≃ₗ[ℂ] ((ColsModel.cols B).mem u).A.Mram,
      ∀ φ ψ, inner ℂ φ ψ = ((ColsModel.cols B).fm u).ipC 0 (e φ).1 (e ψ).1 := fun u =>
    haveI := RowsModel.mram_fd (ColsModel.cols B) u
    RowsModel.exists_frame (RowsModel.ramCore (ColsModel.cols B) u (fun φ _ ψ _ => ipC_conj B u φ ψ)
      (fun φ _ h => ipC_pos B u φ h))
  choose eM heM using hf
  let e : ℂ ≃ₗ[ℂ] RowsModel.Euc 1 :=
    (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm.trans (WithLp.linearEquiv 2 ℂ _).symm
  refine ⟨RowsModel.model (ColsModel.cols B) (fun _ => 1) D (fun _ => e) (fun _ _ => e) eM heM, rfl, rfl,
    fun u => ?_⟩
  have : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  have hne : ((ColsModel.cols B).mem u).A.Mram ≠ ⊥ :=
    MemberTorsor.mram_ne_bot B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) (ColsModel.two_lt_alt B.toPre u)
  have := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact (eM u).toEquiv.nontrivial

theorem exists_stages_over (B : Base) (hB : HasLetters B.toPre) (D : ℕ) :
    ∃ X : Stages, X.B = B ∧ X.W.Drows = D ∧ X.W.Dall = D ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
      (∀ u i, Nonempty ((X.C.mem u).C.cls i)) ∧ Nonempty X.G.jet.Sit := by
  obtain ⟨Del, letter, hD, hinj, gap, hu⟩ := hB
  obtain ⟨W, h1, h2, h3⟩ := exists_rows B D
  have hc : ∀ u i, Nonempty (((ColsModel.cols B).mem u).C.cls i) :=
    fun u _ => ⟨(1 : Tau B.R → (ZMod (B.T u))ˣ)⟩
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W L
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ (GaloisStage.adapt W)
  obtain ⟨S⟩ := SStageInhab.nonempty_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu
    (fun u x _ y _ => (ipC_conj B u y x).symm) (fun u x _ h => ipC_pos B u x h)
    (show W.Drows ≤ W.Dall by omega)
  obtain ⟨G, -, hG⟩ := (GJInhab.inhabited_stage B (ColsModel.cols B)).2.2 (hc _ _) (hc _ _)
  exact ⟨⟨B, _, GaloisStage.adapt W, V, S, N, G⟩, rfl, h1, h2, h3, hc, hG⟩

theorem exists_pre_hasLetters : ∃ P : Pre, HasLetters P ∧ Nonempty (PreX P) ∧ 2 ≤ Fintype.card P.Word := by
  obtain ⟨P, h1, h2, -, -, h3⟩ := exists_pre_two_words
  exact ⟨P, h3, h1, h2⟩

theorem exists_stages_large (P : Pre) (hP : HasLetters P) (D : ℕ) (S₀ S₁ S₂ : Finset ℂ)
    (h₀ : ∀ z ∈ S₀, IsAlgebraic ℚ z) (h₁ : ∀ z ∈ S₁, IsAlgebraic ℚ z) (h₂ : ∀ z ∈ S₂, IsAlgebraic ℚ z) :
    ∃ X : Stages, X.B.toPre = P ∧ (∀ z ∈ S₀, ∃ x ∈ X.B.Ks, X.B.embLL x = z) ∧
      (∀ z ∈ S₁, ∃ x ∈ X.B.LL0, X.B.embLL x = z) ∧ (∀ z ∈ S₂, ∃ x : X.B.LL, X.B.embLL x = z) ∧
      X.W.Drows = D ∧ X.W.Dall = D ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
      (∀ u i, Nonempty ((X.C.mem u).C.cls i)) ∧ Nonempty X.G.jet.Sit := by
  obtain ⟨B, rfl, a, b, c⟩ := BaseExt.exists_base P S₀ S₁ S₂ h₀ h₁ h₂
  obtain ⟨X, rfl, h⟩ := exists_stages_over B hP D
  exact ⟨X, rfl, a, b, c, h⟩

end StagesInhab

theorem exists_stages : ∃ X : GlobalTheory.Mem.Stages, 0 < X.W.Drows ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
    ∀ u i, Nonempty ((X.C.mem u).C.cls i) := by
  obtain ⟨P, hP, -⟩ := StagesInhab.exists_pre_hasLetters
  obtain ⟨X, -, -, -, -, h1, -, h2, h3, -⟩ :=
    StagesInhab.exists_stages_large P hP 1 ∅ ∅ ∅ (by simp) (by simp) (by simp)
  exact ⟨X, by omega, h2, h3⟩

theorem nonempty_stages : Nonempty Stages := exists_stages.elim fun X _ => ⟨X⟩

theorem nonempty_record : Nonempty Formalism.BasicNotions.D7 := nonempty_stages.map Stages.toD7

end GlobalTheory.Mem

end
end
