import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstanceIotaReadoutRealTrivialStabilizerUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanSingletonMulIdealCompletionIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoprimeScalingIdealValuationLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeRationalLineTraceFractionalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLatticeSelfDualComponentsRescaledWordFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramEqOfInst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeUnimodular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportCorrectionCarriesColumnLatticeRowTrace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JZeroMulMemLatticeIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomotheticOfMonomialPrimitiveSelfDualCores
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeSplitsOffUnitNormLineAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralUnitaryScalarOfNormOneIdele
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOneIdeleWithSplitPlaceComponent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastWittLineOfBesselJacobiLatticesGood
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilShapeOfFrameMoves
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralElementHomotheticGluedCores
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnLevelIffRowLatticeKeptAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalSumCoresHomotheticOffLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCoreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFrameFinitePartMulOfCarriesLattice

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.SeeSaw.SplitLat

variable {D : D7}

theorem pair_eq_dot {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_i₀ {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x : Fin S.rank → D.host.E) (y : Fin S₀.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * (d.i₀ *ᵥ y) j = ∑ i, ∑ j, star ((d.q0 *ᵥ x) i) * S₀.gram i j * y j := by
  have hG : S.gram * d.i₀ = d.q0ᴴ * S₀.gram := by
    rw [gram_eq d]
    simp only [Matrix.add_mul, Matrix.mul_assoc, qX_i₀, qY_i₀, wittDecomposition_coreProj_mul_core_eq_one, Matrix.mul_zero, Matrix.mul_one, add_zero,
      zero_add]
  rw [pair_eq_dot, pair_eq_dot, Matrix.mulVec_mulVec, hG, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.star_mulVec]

theorem mulVec_eq_sum_cols {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    M *ᵥ w = ∑ i, fun r => w i * M r i := by
  funext r
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem colProj_mulVec' {S : HSp D} {ρ m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E)
    (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) (x : Fin m → D.host.E) :
    colProj q f i *ᵥ x = fun r => (q *ᵥ x) i * f r i := by
  funext k
  simp only [colProj, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem selfDual_core_monoAt (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (hL : IsSelfDualC S L)
    (hcol : ∀ y ∈ L, ∀ i, (fun r => (d.qX *ᵥ y) i * d.e r i) ∈ L ∧ (fun r => (d.qY *ᵥ y) i * d.e' r i) ∈ L) :
    IsSelfDualC S₀ (coreLat d L) ∧ ∀ v : GlobalTheory.FinPl.Pl D, MonoAt d L (coreLat d L) v := by

  have hcore : ∀ y ∈ L, d.q0 *ᵥ y ∈ coreLat d L := by
    intro y hy
    rw [mem_coreLat]
    have hdec : y = d.e *ᵥ (d.qX *ᵥ y) + d.i₀ *ᵥ (d.q0 *ᵥ y) + d.e' *ᵥ (d.qY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        d.sum_eq_one_rat, Matrix.one_mulVec]
    have hX : d.e *ᵥ (d.qX *ᵥ y) ∈ L := by
      rw [mulVec_eq_sum_cols]; exact sum_mem fun i _ => (hcol y hy i).1
    have hY : d.e' *ᵥ (d.qY *ᵥ y) ∈ L := by
      rw [mulVec_eq_sum_cols]; exact sum_mem fun i _ => (hcol y hy i).2
    have key : ∀ a b c z : Fin S.rank → D.host.E, z = a + b + c → b = z - a - c := by
      intro a b c z hz; rw [hz]; abel
    have h : d.i₀ *ᵥ (d.q0 *ᵥ y) = y - d.e *ᵥ (d.qX *ᵥ y) - d.e' *ᵥ (d.qY *ᵥ y) := key _ _ _ _ hdec
    rw [h]
    exact sub_mem (sub_mem hy hX) hY
  have hinj : Function.Injective ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) := by
    intro x x' hxx
    have h := congrArg (fun z => d.q0 *ᵥ z) hxx
    simpa only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one,
      Matrix.one_mulVec] using h
  refine ⟨⟨⟨?_, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩, fun v => ?_⟩
  ·
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have hLfg : L.FG := hL.1.fg
    haveI : IsNoetherian (𝓞 D.host.E) L := isNoetherian_of_fg_of_noetherian L hLfg
    have hle : (coreLat d L).map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ≤ L :=
      Submodule.map_comap_le _ _
    have h1 : (((coreLat d L).map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))).comap L.subtype).FG :=
      IsNoetherian.noetherian _
    have h2 := h1.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
  ·
    rw [eq_top_iff]
    intro x _
    have hx : d.i₀ *ᵥ x ∈ Submodule.span D.host.E (L : Set (Fin S.rank → D.host.E)) := by
      rw [hL.1.span_eq_top]; exact Submodule.mem_top
    have hm := Submodule.mem_map_of_mem (f := Matrix.mulVecLin d.q0) hx
    rw [Submodule.map_span, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mulVec] at hm
    refine Submodule.span_mono ?_ hm
    rintro _ ⟨z, hz, rfl⟩
    exact hcore z hz
  ·
    obtain ⟨b, hb⟩ := (hL.2 (d.i₀ *ᵥ y)).1 hy (d.i₀ *ᵥ x) hx
    refine ⟨b, ?_⟩
    rw [hb, pair_i₀, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mulVec]
  ·
    rw [mem_coreLat]
    refine (hL.2 (d.i₀ *ᵥ y)).2 fun x hx => ?_
    obtain ⟨b, hb⟩ := h (d.q0 *ᵥ x) (hcore x hx)
    exact ⟨b, hb.trans (pair_i₀ d x y).symm⟩
  ·
    have hX : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qX d.e i *ᵥ x ∈ L := fun i x hx => by
      rw [colProj_mulVec']; exact (hcol x hx i).1
    have hY : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qY d.e' i *ᵥ x ∈ L := fun i x hx => by
      rw [colProj_mulVec']; exact (hcol x hx i).2
    intro y
    constructor
    · intro hy
      refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · change colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
        rw [colMul_rat]
        exact rat_mulVec_mem_latV _ (hX i) _ hy
      · change colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
        rw [colMul_rat]
        exact rat_mulVec_mem_latV _ (hY i) _ hy
      · exact rat_mulVec_mem_latV d.q0 hcore _ hy
    · rintro ⟨h1, h3, h2⟩
      have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
          d.sum_eq_one, Matrix.one_mulVec]
      rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
      refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
      exact rat_mulVec_mem_latV d.i₀ (fun x hx => hx) _ h2

end GlobalTheory.Core.Mi.LatMatch

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lineStable_lattice_splitsAlongWitt_selfDualCore : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S), IsSelfDualC S L → (∀ y ∈ L, ∀ i, (fun r => (d.qX *ᵥ y) i * d.e r i) ∈ L ∧ (fun r => (d.qY *ᵥ y) i * d.e' r i) ∈ L) → IsSelfDualC S₀ (coreLat d L) ∧ ∀ v : GlobalTheory.FinPl.Pl D, MonoAt d L (coreLat d L) v := by
  atlas_forward_decl GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.SZ

variable {D : D7}

theorem cY_eq_repr (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (y : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h y = (X.bas.reindex (finCongr (rank_eq X h)).symm).repr y := by
  funext k
  simp [GlobalTheory.Core.SBesEx.cY, HidaSetting.crd, crdOf, Module.Basis.repr_reindex]

theorem sum_bas_mem_iff (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (ιE : I.E ≃+* D.host.E)
    (hId : ∀ x : I.E, HEq (ιE x) x) (hn : (D.sp.Y 0).rank = I.n) (bas : Module.Basis (Fin I.n) D.host.E (VS D).V)
    (hL : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0) (v : Fin (D.sp.Y 0).rank → D.host.E) :
    (∑ k, v k • bas (Fin.cast hn k)) ∈ (VS D).L0 ↔ (∑ k, v k • (VS D).frame k) ∈ (VS D).L0 := by
  subst hI
  have h2 : ∀ i, ιE (v i) = v i := fun i => eq_of_heq (hId _)
  rw [← Formalism.L2.SG.InstExistsPf.mem_Lv]
  refine Iff.trans ?_ (hL v).symm
  apply iff_of_eq
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 i]
  rfl

theorem cY_mem_latS_iff (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : GlobalTheory.Core.Mi.IdE X)
    (y : (VS D).V) : GlobalTheory.Core.SBesEx.cY X h y ∈ latS D ↔ y ∈ (VS D).L0 := by
  have hs := sum_bas_mem_iff X.B.I h X.ιE hId (rank_eq X h) X.bas X.L_eq (GlobalTheory.Core.SBesEx.cY X h y)
  have hy : (∑ k, GlobalTheory.Core.SBesEx.cY X h y k • X.bas (Fin.cast (rank_eq X h) k)) = y := by
    rw [cY_eq_repr]
    conv_rhs => rw [← (X.bas.reindex (finCongr (rank_eq X h)).symm).sum_repr y]
    simp
  rw [hy] at hs
  rw [hs]
  simp only [latS, Formalism.L2.Herm.crdLat, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Formalism.L2.Herm.crd]
  constructor
  · rintro ⟨w, hw, hwe⟩
    have : w = ∑ k, GlobalTheory.Core.SBesEx.cY X h y k • (VS D).frame k := by
      rw [← hwe]; exact ((VS D).frame.sum_equivFun w).symm
    rw [← this]; exact hw
  · intro hw
    exact ⟨_, hw, by
      rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]⟩

theorem cY_smul (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (c : D.host.E) (y : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h (c • y) = c • GlobalTheory.Core.SBesEx.cY X h y := by
  rw [cY_eq_repr, cY_eq_repr, map_smul, Finsupp.coe_smul]

end GlobalTheory.Core.Mi.LatMatch.SZ

namespace GlobalTheory.Core.Mi.LatMatch.SZ

variable {D : D7}

theorem smul_zu_mem_iff (X : HidaSetting D) (u : D.what₂.Word) (c : D.host.E) :
    c • X.zu u ∈ (VS D).L0 ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  constructor
  · intro hc
    have hfix := (X.Fu_fixed u).2.2.2.2
    apply hfix c
    have hz : (X.Fu u).z = X.zu u := X.flagZVector u
    show c • (X.Fu u).z ∈ _
    rw [hz]
    have horth : c • X.zu u ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu u).X := by
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [map_smulₛₗ, ← hz, (X.Fu u).z_orth a, smul_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [LinearMap.map_smulₛₗ₂, hx, smul_zero]
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hc, horth⟩), horth⟩
  · rintro ⟨o, rfl⟩
    have hz : X.zu u ∈ (VS D).L0 := by
      rw [X.Lam_split]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.zu_Lb u))
    have := (VS D).L0.smul_mem o hz
    simpa [algebraMap_smul] using this

theorem quad {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n D.host.E) (G : Matrix m m D.host.E) (x : n → D.host.E) :
    star x ⬝ᵥ (Mᴴ * G * M) *ᵥ x = star (M *ᵥ x) ⬝ᵥ G *ᵥ (M *ᵥ x) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end GlobalTheory.Core.Mi.LatMatch.SZ

open GlobalTheory.Core.Mi.LatMatch.SZ in

theorem GlobalTheory.Core.Mi.LatMatch.sz_tied : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → (∀ t : D.host.E, t • vecB B.o B.ζ ∈ coreLat B.d (latS D) ↔ μ * t ∈ (1 : FI D)) ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(μ * star μ * (((D.mem u).A.T : ℕ) : D.host.E)) ∧ vecB B.o B.ζ ≠ 0 := by
  intro D X h u ψ A B μ lam hId hF
  have hz : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY X h (X.zu u) := hF.z
  refine ⟨fun t => ?_, ?_, ?_⟩
  · rw [mem_coreLat, Matrix.mulVec_smul, hz, smul_smul, ← cY_smul, cY_mem_latS_iff X h hId, smul_zu_mem_iff,
      FractionalIdeal.mem_one_iff, mul_comm]
  · rw [← B.o.isoB, quad, ← B.d.iso, quad]
    change star (B.d.i₀ *ᵥ vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = _
    rw [hz, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct,
      GlobalTheory.Core.SBesEx.cY_isom D X h hId, X.zu_norm]
    simp only [smul_eq_mul]
    ring
  · intro h0
    apply B.line.2
    rw [← B.o.isoB, quad]
    change star (vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (vecB B.o B.ζ) = 0
    rw [h0]
    simp

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → (∀ t : D.host.E, t • vecB B.o B.ζ ∈ coreLat B.d (latS D) ↔ μ * t ∈ (1 : FI D)) ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(μ * star μ * (((D.mem u).A.T : ℕ) : D.host.E)) ∧ vecB B.o B.ζ ≠ 0 := by
  atlas_forward_decl GlobalTheory.Core.Mi.LatMatch.sz_tied
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch.DiffInv

theorem aaD_eq_dI_pow : ∀ (D : D7) (i : Fin D.R.rS), aaD D i = dI D ^ (D.R.rS - i.1) := by
  intro D i
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  have hinv : dI D = (ddS D)⁻¹ := by
    rw [GlobalTheory.IntTerm.Conv.ddS_eq]
    exact eq_inv_of_mul_eq_one_left hP
  rw [hinv, inv_pow, aaD, ← Nat.cast_sub i.2.le, _root_.zpow_neg, _root_.zpow_natCast]

end GlobalTheory.Core.Mi.LatMatch.DiffInv
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLineIdeal_eq_inverseDifferent_pow : ∀ (D : D7) (i : Fin D.R.rS), aaD D i = dI D ^ (D.R.rS - i.1) := by
  atlas_forward_decl GlobalTheory.Core.Mi.LatMatch.DiffInv.aaD_eq_dI_pow
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportCorrection_carries_columnLattice_rowTrace : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (B : SBes X h u ψ (D.sp.X 0)) (a₀ : GA D (D.sp.X 0)), GlobalTheory.Core.Mi.IdE X → Formalism.L2.SG.ColDict.LevelMatch X tr hK → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (D.sp.X 0).rank → AE D), (∀ i, y i ∈ idAt D (· = v)) → (y ∈ latV (D.sp.X 0) (lat0 F) (· = v) ↔ B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y)) ∈ latV (D.sp.Y 0) (latS D) (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.TraceX.trace_iff | exact GlobalTheory.Core.Mi.LatMatch.TraceX.trace_iff | (intros; apply GlobalTheory.Core.Mi.LatMatch.TraceX.trace_iff <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.SeeSaw.AdaptFBIdeals

theorem primAt_lastAt_of_lines : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L : Lat S) (M : Lat S₀) (μ : D.host.E) (v : GlobalTheory.FinPl.Pl D), μ ≠ 0 → LineAt z μ M v → (∀ i : Fin ρ, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ incA D μ * a ∈ idV (dI D ^ (ρ - i.1)) v) → PrimAt ψ d L v ∧ LastAt ψ d z L M v := by
  intro D ψ hψ S S₀ ρ d z L M μ v hμ hline hcol
  have hdI : dI D ≠ 0 := (GlobalTheory.SeeSaw.ChainIdeals.host_ne_zero D).2.2.2
  have hu : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ, map_one]
  have key : ∀ 𝔞 𝔟 : FI D, 𝔞 ≠ 0 → 𝔟 ≠ 0 → 𝔟 * 𝔞⁻¹ = dI D → ∀ s ∈ idAt D (· = v),
      ((∀ a ∈ idAt D (· = v), incA D μ * a ∈ idV 𝔞 v → incA D μ * (s * a) ∈ idV 𝔟 v) ↔
        ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) := by
    intro 𝔞 𝔟 h𝔞 h𝔟 hq s hs
    rw [← GlobalTheory.SeeSaw.DiffDual.idV_dI_iff D ψ hψ v s hs, ← hq, ← GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v 𝔞 𝔟 h𝔞 h𝔟 s hs]
    constructor
    · intro h b hb
      have hbAt := idV_supp 𝔞 v hb
      have ha : incA D μ⁻¹ * b ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hbAt
      have hb' : incA D μ * (incA D μ⁻¹ * b) = b := by rw [← mul_assoc, mul_comm (incA D μ), hu, one_mul]
      have h2 := h _ ha (by rw [hb']; exact hb)
      rwa [mul_left_comm, hb'] at h2
    · intro h a _ hma
      rw [mul_left_comm]
      exact h _ hma
  constructor
  · intro i j hij s hs
    have hq : dI D ^ (ρ - i.1) * (dI D ^ (ρ - j.1))⁻¹ = dI D := by
      have he : ρ - i.1 = (ρ - j.1) + 1 := by have := j.2; omega
      rw [he, pow_succ, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hdI), one_mul]
    rw [← key (dI D ^ (ρ - j.1)) (dI D ^ (ρ - i.1)) (pow_ne_zero _ hdI) (pow_ne_zero _ hdI) hq s hs]
    constructor
    · intro h a ha hma
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).1 (h a ((hcol j a ha).2 hma))
    · intro h a ha
      have haAt := supp_of_colMul d L v j a ha
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ haAt)).2 (h a haAt ((hcol j a haAt).1 ha))
  · intro i hi s hs
    rw [← key 1 (dI D) one_ne_zero hdI (by rw [inv_one, mul_one]) s hs]
    have hρi : ρ - i.1 = 1 := by omega
    constructor
    · intro h a ha hma
      rw [GlobalTheory.SeeSaw.idV_one_eq_intAt] at hma
      have h2 := (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).1 (h a ha ((hline a ha).2 hma))
      rwa [hρi, pow_one] at h2
    · intro h a ha hz
      have h2 := h a ha ((GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 ((hline a ha).1 hz))
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).2 (by rwa [hρi, pow_one])

end GlobalTheory.Core.Mi.LatMatch

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_primitive_of_inverseDifferent_lines : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L : Lat S) (M : Lat S₀) (μ : D.host.E) (v : GlobalTheory.FinPl.Pl D), μ ≠ 0 → LineAt z μ M v → (∀ i : Fin ρ, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ incA D μ * a ∈ idV (dI D ^ (ρ - i.1)) v) → PrimAt ψ d L v ∧ LastAt ψ d z L M v := by
  atlas_forward_decl GlobalTheory.Core.Mi.LatMatch.primAt_lastAt_of_lines
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.FinPl.FrameLat

section

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_sec_w (p : SplitPt D k) {m n : ℕ} (a : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → k) :
    a *ᵥ (fun i => p.sec (y i)) = fun i => p.sec ((a.map p.pr *ᵥ y) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, sec_mul_right, mul_comm]

theorem inc_mul_sec_mem_iff (p : SplitPt D k) (α : D.host.E) (x : k) :
    incA D α * p.sec x ∈ intAt D (· = p.v) ↔ p.pr (incA D α) * x ∈ 𝒪[k] := by
  rw [mul_comm, sec_mul_right, mul_comm x]
  exact ⟨fun h => (p.int_iff _).2 h.2, sec_mem_intAt p _⟩

theorem proj_mulVec_add {R : Type} [CommRing R] {l m n : ℕ} {P : Matrix (Fin m) (Fin l) R} {J : Matrix (Fin l) (Fin m) R}
    {J' : Matrix (Fin l) (Fin n) R} (h1 : P * J = 1) (h0 : P * J' = 0) (u : Fin m → R) (v : Fin n → R) :
    P *ᵥ (J *ᵥ u + J' *ᵥ v) = u := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h0, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

end

set_option maxHeartbeats 1000000 in

theorem wShape_of_mono (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E)
    (L : Lat S) (M : Lat S₀) (N : Lat A) (α α' : Fin ρ → D.host.E) (μ : D.host.E) (g : GA D A)
    (hmono : MonoAt d L M p.v)
    (hX : ∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jX i a ∈ latV S L (· = p.v) ↔ incA D (α i) * a ∈ intAt D (· = p.v))
    (hY : ∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jY i a ∈ latV S L (· = p.v) ↔ incA D (α' i) * a ∈ intAt D (· = p.v))
    (hline : LineAt (vecB o ζ) μ M p.v) (hsplit : SplitsAt o M p.v) (htr : TraceAt o g N M p.v) :
    WShape p d o ζ L (fun i => p.pr (incA D (α i))) (fun i => p.pr (incA D (α' i))) (p.pr (incA D μ)) g N := by
  intro x x' t y
  let f : D.host.E →+* k := p.pr.comp (incA D)
  have hz : o.jB *ᵥ (fun i => p.sec ((t • (f ∘ ζ)) i)) = p.sec t • ratV (vecB o ζ) := by
    rw [mulVec_sec_w, Matrix.mulVec_smul]
    funext i
    have h := RingHom.map_mulVec f o.iB ζ i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, sec_mul_right]
    exact congrArg (fun u => p.sec (t * u)) h.symm
  obtain ⟨c, hc⟩ : ∃ c : Fin S₀.rank → AE D, c = o.jB *ᵥ (fun i => p.sec ((t • (f ∘ ζ)) i)) +
    o.jA *ᵥ (Formalism.L2.Theta.mt A g *ᵥ fun r => p.sec (y r)) := ⟨_, rfl⟩
  have hcid : ∀ i, c i ∈ idAt D (· = p.v) := fun i => by
    rw [hc, mulVec_sec_w, mulVec_sec_w, mulVec_sec_w]
    exact add_mem (sec_mem_idAt p _) (sec_mem_idAt p _)
  have hvec : (fun r => p.sec ((atW p d.e *ᵥ x + atW p d.e' *ᵥ x' + t • (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A g).map p.pr *ᵥ y)) r)) =
      d.jX *ᵥ (fun i => p.sec (x i)) + d.jY *ᵥ (fun i => p.sec (x' i)) + d.j0 *ᵥ c := by
    have h1 : (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) = d.i₀.map f *ᵥ (o.iB.map f *ᵥ (f ∘ ζ)) := by
      have h2 : o.iB.map f *ᵥ (f ∘ ζ) = f ∘ vecB o ζ := by
        funext i; exact (RingHom.map_mulVec f o.iB ζ i).symm
      rw [h2]
      funext i; exact RingHom.map_mulVec f d.i₀ _ i
    have h3 : atW p (d.i₀ * o.iA) = d.i₀.map f * o.iA.map f := Matrix.map_mul (f := f)
    rw [hc, Matrix.mulVec_add, h1, h3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul]
    have e1 : d.jX.map p.pr = atW p d.e := rfl
    have e2 : d.jY.map p.pr = atW p d.e' := rfl
    have e3 : d.j0.map p.pr = d.i₀.map f := rfl
    have e4 : o.jA.map p.pr = o.iA.map f := rfl
    have e5 : o.jB.map p.pr = o.iB.map f := rfl
    rw [mulVec_sec_w p d.jX, mulVec_sec_w p d.jY, mulVec_sec_w p o.jB, mulVec_sec_w p d.j0,
      mulVec_sec_w p (Formalism.L2.Theta.mt A g), mulVec_sec_w p o.jA, mulVec_sec_w p d.j0, e1, e2, e3, e4, e5]
    funext r
    simp only [Pi.add_apply, map_add p.sec, add_assoc]
  rw [hvec, hmono]
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, d.pX_jX, d.pX_jY, d.pX_j0, d.pY_jX, d.pY_jY, d.pY_j0, d.p0_jX,
    d.p0_jY, d.p0_j0, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  have hA : o.pA *ᵥ c = Formalism.L2.Theta.mt A g *ᵥ fun r => p.sec (y r) := by
    rw [hc, add_comm]; exact proj_mulVec_add o.pA_jA o.pA_jB _ _
  have hB : o.pB *ᵥ c = fun i => p.sec ((t • (f ∘ ζ)) i) := by
    rw [hc]; exact proj_mulVec_add o.pB_jB o.pB_jA _ _
  rw [hsplit c hcid, hA, hB, hz, hline _ (sec_mem_idAt p t), ← htr _ (fun i => sec_mem_idAt p _), inc_mul_sec_mem_iff]
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) and_comm)
  · rw [hX i _ (sec_mem_idAt p _), inc_mul_sec_mem_iff]
  · rw [hY i _ (sec_mem_idAt p _), inc_mul_sec_mem_iff]

end GlobalTheory.Core.Mi.LatMatch
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceComponent_monomialLattice_splitCore : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E) (L : Lat S) (M : Lat S₀) (N : Lat A) (α α' : Fin ρ → D.host.E) (μ : D.host.E) (g : GA D A), MonoAt d L M p.v → (∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jX i a ∈ latV S L (· = p.v) ↔ incA D (α i) * a ∈ intAt D (· = p.v)) → (∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jY i a ∈ latV S L (· = p.v) ↔ incA D (α' i) * a ∈ intAt D (· = p.v)) → LineAt (vecB o ζ) μ M p.v → SplitsAt o M p.v → TraceAt o g N M p.v → WShape p d o ζ L (fun i => p.pr (incA D (α i))) (fun i => p.pr (incA D (α' i))) (p.pr (incA D μ)) g N := by
  atlas_forward_decl GlobalTheory.Core.Mi.LatMatch.wShape_of_mono
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseDifferentPow_completion_trivial_at_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), p.UnitAA → ∀ (n : ℕ) (a : AE D), (a ∈ idV (dI D ^ n) p.v ↔ a ∈ intAt D (· = p.v)) ∧ (a ∈ idV (dI D ^ n)⁻¹ p.v ↔ a ∈ intAt D (· = p.v)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit | exact GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit | (intros; apply GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

set_option maxHeartbeats 1000000 in

theorem sMoves_of_wShape : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E) (L L' : Lat S) (N N' : Lat A) (α α' β β' : Fin ρ → k) (γ δ c₀ : k) (a₀ : GA D A), IsLineVec Ln ζ → IsSelfDualC S L → IsSelfDualC S L' → WShape p d o ζ L α α' γ 1 N → WShape p d o ζ L' β β' δ a₀ N' → latV A N (· = p.v) = latV A N' (· = p.v) → c₀ ≠ 0 → (∀ i, valuation k (β i * c₀) = valuation k (α i)) → (∀ i, valuation k (β' i * c₀) = valuation k (α' i)) → valuation k (δ * c₀) = valuation k γ → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (embA d o (a₀ * a)) L L' p.v := by
  intro D k _ _ _ _ p S S₀ A Ln ρ d o ζ L L' N N' α α' β β' γ δ c₀ a₀ hζ hL hL' hW hW' hN hc₀ hb hb' hd
  obtain ⟨c, hc, hpc⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p c₀ hc₀
  obtain ⟨c', hc', hpc'⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p c₀⁻¹ (inv_ne_zero hc₀)
  obtain ⟨a, haC, ha⟩ := GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D A p.v c' hc'
  refine ⟨a, c, haC, hc, ?_⟩
  apply GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D k p S L L' c _ hL hL' hc
  set f : D.host.E →+* k := p.pr.comp (incA D) with hf
  have hatW : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), atW p X = X.map f := fun _ => rfl
  have hrat : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), atW p X = (rat X).map p.pr := fun _ => rfl
  have hkey : ∀ {n m l : ℕ} (M : Matrix (Fin n) (Fin l) (AE D)) (R : Matrix (Fin l) (Fin m) (AE D))
      (u : Fin m → k), M.map p.pr *ᵥ (R.map p.pr *ᵥ u) = (M * R).map p.pr *ᵥ u := by
    intro n m l M R u; rw [Matrix.mulVec_mulVec, Matrix.map_mul]

  have hsum : atW p d.e * atW p d.qX + atW p d.i₀ * atW p d.q0 + atW p d.e' * atW p d.qY = 1 := by
    simp only [hatW]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add f), ← Matrix.map_add _ (map_add f), d.sum_eq_one_rat,
      Matrix.map_one _ (map_zero f) (map_one f)]
  have hsumA : atW p o.iA * atW p o.qA + atW p o.iB * atW p o.qB = 1 := by
    simp only [hatW]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add f), o.iA_qA_add, Matrix.map_one _ (map_zero f) (map_one f)]
  have hrk : Ln.rank = 1 := hζ.1
  have j0 : Fin Ln.rank := ⟨0, by omega⟩
  have huniq : ∀ j : Fin Ln.rank, j = j0 := fun j => Fin.ext (by have := j.2; have := j0.2; omega)
  have hζ0 : ζ j0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun j => by rw [huniq j, h0]; rfl
    simp [this]
  have hfζ : f (ζ j0) ≠ 0 := fun h => hζ0 (f.injective (by rw [h, map_zero]))
  set ζk : Fin Ln.rank → k := fun j => f (ζ j) with hζk
  set zv : Fin S.rank → k := fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r')) with hzv
  have hz : zv = atW p (d.i₀ * o.iB) *ᵥ ζk := by
    funext r
    simp only [hzv, vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec f (d.i₀ * o.iB) ζ r
  have hdec : ∀ x : Fin S.rank → k, ∃ (x1 x2 : Fin ρ → k) (t : k) (y : Fin A.rank → k),
      x = atW p d.e *ᵥ x1 + atW p d.e' *ᵥ x2 + t • zv +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y) := by
   intro x
   set x0 := atW p d.q0 *ᵥ x
   set w := atW p o.qB *ᵥ x0
   set y := atW p o.qA *ᵥ x0
   set t := w j0 / f (ζ j0)
   have hw : w = t • ζk := by
     funext j; rw [huniq j]; simp only [Pi.smul_apply, smul_eq_mul, hζk, t]; field_simp
   have hx : x = atW p d.e *ᵥ (atW p d.qX *ᵥ x) + atW p d.e' *ᵥ (atW p d.qY *ᵥ x) + t • zv +
       atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y) := by
     rw [mt_one, Matrix.map_one _ (map_zero p.pr) (map_one p.pr), Matrix.one_mulVec, hz, ← Matrix.mulVec_smul, ← hw]
     have hm : atW p d.i₀ * (atW p o.iA * atW p o.qA + atW p o.iB * atW p o.qB) * atW p d.q0 =
         atW p d.i₀ * atW p d.q0 := by rw [hsumA, Matrix.mul_one]
     have h0 : atW p (d.i₀ * o.iA) *ᵥ y + atW p (d.i₀ * o.iB) *ᵥ w = atW p d.i₀ *ᵥ x0 := by
       simp only [y, w, x0, hatW, Matrix.map_mul, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
       simp only [← hatW]
       rw [← hm]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
     calc x = (1 : Matrix (Fin S.rank) (Fin S.rank) k) *ᵥ x := (Matrix.one_mulVec x).symm
       _ = _ := by
         rw [← hsum, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
           ← Matrix.mulVec_mulVec, ← h0]
         abel
   exact ⟨_, _, _, _, hx⟩
  intro x
  obtain ⟨x1, x2, t, y, rfl⟩ := hdec x
  rw [hW x1 x2 t y]
  have jX : rat d.e = d.jX := rfl
  have jY : rat d.e' = d.jY := rfl
  have jA : rat (d.i₀ * o.iA) = d.j0 * o.jA := rat_mul _ _
  have jB : rat (d.i₀ * o.iB) = d.j0 * o.jB := rat_mul _ _
  have hGX : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.jX = d.jX := d.wittDecomp_anisotropicEmbedding_inclX _
  have hGY : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.jY = d.jY := d.wittDecomp_anisotropicEmbedding_inclY _
  have hG0' : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.j0 = d.j0 ⬝ Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) :=
    d.wittDecomp_anisotropicEmbedding_inclAnisotropic _
  have hG0 : ∀ {m : ℕ} (R : Matrix (Fin S₀.rank) (Fin m) (AE D)), Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ (d.j0 ⬝ R) =
      d.j0 ⬝ (Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ R) := by
    intro m R; rw [← Matrix.mul_assoc, hG0', Matrix.mul_assoc]
  have hBB : Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ o.jB = o.jB := by rw [o.emb_jB, mt_one, Matrix.mul_one]
  have hAA : Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ o.jA = o.jA ⬝ (Formalism.L2.Theta.mt A a₀ ⬝ Formalism.L2.Theta.mt A a) := by
    rw [o.emb_jA, mt_mul]
  set G := Formalism.L2.Theta.mt S (embA d o (a₀ * a)) with hG
  have T1 : G.map p.pr *ᵥ (atW p d.e *ᵥ x1) = atW p d.e *ᵥ x1 := by rw [hrat, hkey, jX, hGX]
  have T2 : G.map p.pr *ᵥ (atW p d.e' *ᵥ x2) = atW p d.e' *ᵥ x2 := by rw [hrat, hkey, jY, hGY]
  have hz' : zv = (d.j0 ⬝ o.jB).map p.pr *ᵥ ζk := by
    rw [← jB]; exact hz
  have T3 : G.map p.pr *ᵥ zv = zv := by
    rw [hz', hkey, hG0, hBB]
  have hms : ∀ {m n : ℕ} (r : AE D) (X : Matrix (Fin m) (Fin n) (AE D)), (r • X).map p.pr = p.pr r • X.map p.pr := by
    intro m n r X; ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have T4 : G.map p.pr *ᵥ (atW p (d.i₀ * o.iA) *ᵥ y) =
      c₀⁻¹ • (atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A a₀).map p.pr *ᵥ y)) := by
    rw [hrat, hkey, hkey, jA, hG0, hAA, ha, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_smul,
      hms, Matrix.smul_mulVec, hpc', Matrix.mul_assoc]
  have himg : p.pr c • (G.map p.pr *ᵥ (atW p d.e *ᵥ x1 + atW p d.e' *ᵥ x2 + t • zv +
      atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y))) =
      atW p d.e *ᵥ (c₀ • x1) + atW p d.e' *ᵥ (c₀ • x2) + (c₀ * t) • zv +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A a₀).map p.pr *ᵥ y) := by
    rw [mt_one, Matrix.map_one _ (map_zero p.pr) (map_one p.pr), Matrix.one_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, T1, T2, T3, T4, hpc]
    simp only [smul_add, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hc₀, one_smul]
  rw [himg, hW' (c₀ • x1) (c₀ • x2) (c₀ * t) y, hN]
  have hval : ∀ u u' z : k, valuation k (u * c₀) = valuation k u' → (u * (c₀ * z) ∈ 𝒪[k] ↔ u' * z ∈ 𝒪[k]) := by
    intro u u' z h
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, ← mul_assoc, map_mul, h, ← map_mul]
  refine and_congr (forall_congr' fun i => (hval _ _ _ (hb i)).symm)
    (and_congr (forall_congr' fun i => (hval _ _ _ (hb' i)).symm) (and_congr (hval _ _ _ hd).symm Iff.rfl))

end GlobalTheory.Core.Mi.LatMatch

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattices_same_splitShape_carried_by_central : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E) (L L' : Lat S) (N N' : Lat A) (α α' β β' : Fin ρ → k) (γ δ c₀ : k) (a₀ : GA D A), IsLineVec Ln ζ → IsSelfDualC S L → IsSelfDualC S L' → WShape p d o ζ L α α' γ 1 N → WShape p d o ζ L' β β' δ a₀ N' → latV A N (· = p.v) = latV A N' (· = p.v) → c₀ ≠ 0 → (∀ i, valuation k (β i * c₀) = valuation k (α i)) → (∀ i, valuation k (β' i * c₀) = valuation k (α' i)) → valuation k (δ * c₀) = valuation k γ → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (embA d o (a₀ * a)) L L' p.v := by
  atlas_forward_decl GlobalTheory.Core.Mi.LatMatch.sMoves_of_wShape
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LevChain

theorem mem_levS_iff_moves : ∀ (D : D7) (c : GlobalTheory.ChainOnto.Com D) (j : ℕ) (s : GlobalTheory.ChainOnto.PiLocalization₂ D), s.Is c j → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ c.S → ∀ κ ∈ grpAt s.V (· = v), κ ∈ levS s.V s.β s.L ↔ Moves s.V κ s.Λ s.Λ (· = v) := by
  intro D c j s hs v hv κ hκ
  haveI : Submodule.IsLattice D.host.E s.Λ := hs.selfDual.1
  have hfg : s.Λ.FG := Submodule.IsLattice.fg (A := D.host.E)
  have hGf := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff s.V (· = v) κ).1 hκ
  have hSt : Lev.finE s.V κ ∈ Formalism.L2.DIV.St s.β ↔ κ ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig s.V.gram s.Λ := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_of_fg s.V s.β s.Λ hs.frame hfg κ]
    exact GlobalTheory.AdelicU.mem_levelOpen.symm
  constructor
  · intro h
    have h2 : Lev.finE s.V κ ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L := h.2
    exact GlobalTheory.FinPl.KOpen.moves_of_levelOpen s.V s.Λ hfg _ (hSt.1 (Formalism.L2.DIV.parLev_St h2.1))
  · intro hm
    have hS := hSt.2 (GlobalTheory.FinPl.KOpen.levelOpen_of_inK s.V s.Λ hfg _ ⟨hκ, hm⟩)
    obtain ⟨hr, ξ, hL⟩ := hs.lev
    refine ⟨hGf.1, ?_⟩
    refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA _ _) hS fun PP hPP => ?_
    have hPg : PP ∈ c.Pg := by
      rw [hL] at hPP
      simpa [Lev.datY] using hPP
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β κ PP hS (hGf.2 _ ?_)
    intro he
    exact hv (Finset.mem_image.2 ⟨PP, hPg, he⟩)

end GlobalTheory.Core.Mi.LevChain

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_chainLevel_iff_carriesLattice_offLevel : ∀ (D : D7) (c : GlobalTheory.ChainOnto.Com D) (j : ℕ) (s : GlobalTheory.ChainOnto.PiLocalization₂ D), s.Is c j → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ c.S → ∀ κ ∈ grpAt s.V (· = v), κ ∈ levS s.V s.β s.L ↔ Moves s.V κ s.Λ s.Λ (· = v) := by
  atlas_forward_decl GlobalTheory.Core.Mi.LevChain.mem_levS_iff_moves
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem moves_emb0_iff_moves_of_monoAt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (γ : GA D S₀), MonoAt d L M v → (Moves S (d.emb0 γ) L L (· = v) ↔ Moves S₀ γ M M (· = v)) := by
  intro D S S₀ ρ d L M v γ hL
  have supp : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → AE D), (∀ i, y i ∈ idAt D (· = v)) →
      ∀ i, (A *ᵥ y) i ∈ idAt D (· = v) := fun A y hy i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy k)
  have hc : ∀ {n : ℕ} (x : Matrix (Fin S.rank) (Fin n) (AE D)) (i : Fin n), colMul x i 0 = 0 := fun x i => by
    funext k; simp [colMul]
  have j0iff : ∀ w : Fin S₀.rank → AE D, d.j0 *ᵥ w ∈ latV S L (· = v) ↔ w ∈ latV S₀ M (· = v) := by
    intro w
    rw [hL]
    simp only [Matrix.mulVec_mulVec, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec, Pi.zero_apply, hc,
      zero_mem, implies_true, true_and]
  constructor
  · intro h w hw
    have h1 := h (d.j0 *ᵥ w) (supp _ _ hw)
    rw [j0iff, Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, j0iff] at h1
    exact h1
  · intro h y hy
    rw [hL y, hL (mt S (d.emb0 γ) *ᵥ y)]
    simp only [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding, d.wittDecomp_projY_anisotropicEmbedding, d.wittDecomp_projAnisotropic_anisotropicEmbedding]
    rw [← Matrix.mulVec_mulVec, ← h _ (supp _ _ hy)]

end GlobalTheory.Core.Mi.LatMatch
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (γ : GA D S₀), MonoAt d L M v → (Moves S (d.emb0 γ) L L (· = v) ↔ Moves S₀ γ M M (· = v)) := by
  atlas_forward_decl GlobalTheory.Core.Mi.LatMatch.moves_emb0_iff_moves_of_monoAt
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatGlue

variable {D : D7}

theorem mt_mul (S : HSp D) (a b : GA D S) : Formalism.L2.Theta.mt S (a * b) = Formalism.L2.Theta.mt S a * Formalism.L2.Theta.mt S b := by
  first | rfl | simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_one (S : HSp D) : Formalism.L2.Theta.mt S 1 = 1 := by
  first | rfl | simp [Formalism.L2.Theta.mt]

theorem mem_congGrp {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ GlobalTheory.FinPl.congGrp V I ↔ ∀ i j, Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold GlobalTheory.FinPl.congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) h
    rw [← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem idAt_le_idOff {v w : GlobalTheory.FinPl.Pl D} (h : v ≠ w) : idAt D (· = w) ≤ GlobalTheory.FinPl.idOff D (· = v) := by
  intro a ha
  unfold idAt at ha
  unfold GlobalTheory.FinPl.idOff
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  have hu : u.1 = v := u.2
  exact ha.2 ⟨u.1, fun e => h (hu.symm.trans e)⟩

theorem mulVec_fix {S : HSp D} {v w : GlobalTheory.FinPl.Pl D} (hvw : v ≠ w) {h : GA D S} (hh : h ∈ grpAt S (· = w))
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v)) : Formalism.L2.Theta.mt S h *ᵥ y = y := by
  obtain ⟨ε, -, -, -, hA, hO⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).1
  have hh' := (mem_congGrp).1 hh
  have key : (Formalism.L2.Theta.mt S h - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 : (Formalism.L2.Theta.mt S h - 1) i j * y j ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ (hy j)
    have h2 : (Formalism.L2.Theta.mt S h - 1) i j * y j ∈ GlobalTheory.FinPl.idOff D (· = v) :=
      Ideal.mul_mem_right _ _ (idAt_le_idOff hvw (by simpa using hh' i j))
    rw [← (hA _).1 h1]
    exact (hO _).1 h2
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec] at key
  exact key

theorem scal_mulVec {n : ℕ} (c : AE D) (y : Fin n → AE D) : (c • (1 : Matrix (Fin n) (Fin n) (AE D))) *ᵥ y = c • y := by
  first | rw [Matrix.smul_mulVec, Matrix.one_mulVec] | simp [Matrix.smul_mulVec] | (ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])

end GlobalTheory.Core.Mi.LatGlue

namespace GlobalTheory.Core.Mi.LatGlue

variable {D : D7}

set_option maxHeartbeats 800000 in

theorem glue_finset {V A : HSp D} (e : GA D A →* GA D V)
    (he : ∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ grpAt A (· = v), e a ∈ grpAt V (· = v))
    (a : GlobalTheory.FinPl.Pl D → GA D A) (c : GlobalTheory.FinPl.Pl D → AE D) (z : GlobalTheory.FinPl.Pl D → GA D V)
    (ha : ∀ v, CenAt A v (a v)) (hz : ∀ v, CenAt V v (z v))
    (hzm : ∀ v, Formalism.L2.Theta.mt V (z v) = c v • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) (s : Finset (GlobalTheory.FinPl.Pl D)) :
    ∃ α ∈ GfC A, α ∈ Subgroup.center (GA D A) ∧ ∃ ζ ∈ Subgroup.center (GA D V),
      (∀ v ∈ s, ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
        Formalism.L2.Theta.mt V (e α) *ᵥ y = Formalism.L2.Theta.mt V (e (a v)) *ᵥ y ∧ Formalism.L2.Theta.mt V ζ *ᵥ y = c v • y) ∧
      (∀ v ∉ s, ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
        Formalism.L2.Theta.mt V (e α) *ᵥ y = y ∧ Formalism.L2.Theta.mt V ζ *ᵥ y = y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, one_mem _, one_mem _, 1, one_mem _, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ y _ => ?_⟩
    rw [map_one, mt_one, Matrix.one_mulVec]
    exact ⟨rfl, rfl⟩
  | insert w s hws ih =>
    obtain ⟨α, hαG, hαC, ζ, hζC, hin, hout⟩ := ih
    have hwG : a w ∈ GfC A := ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff A _ (a w)).1 (ha w).1).1
    refine ⟨a w * α, mul_mem hwG hαG, mul_mem (ha w).2 hαC, z w * ζ, mul_mem (hz w).2 hζC, ?_, ?_⟩
    · intro v hv y hy
      rcases Finset.mem_insert.1 hv with rfl | hvs
      · obtain ⟨h1, h2⟩ := hout v hws y hy
        refine ⟨?_, ?_⟩
        · rw [map_mul, mt_mul, ← Matrix.mulVec_mulVec, h1]
        · rw [mt_mul, ← Matrix.mulVec_mulVec, h2, hzm, scal_mulVec]
      · have hvw : v ≠ w := fun h => hws (h ▸ hvs)
        obtain ⟨h1, h2⟩ := hin v hvs y hy
        have ca : a w * α = α * a w := ((Subgroup.mem_center_iff.1 (ha w).2) α).symm
        have cz : z w * ζ = ζ * z w := ((Subgroup.mem_center_iff.1 (hz w).2) ζ).symm
        refine ⟨?_, ?_⟩
        · rw [ca, map_mul, mt_mul, ← Matrix.mulVec_mulVec, mulVec_fix hvw (he w _ (ha w).1) hy, h1]
        · rw [cz, mt_mul, ← Matrix.mulVec_mulVec, mulVec_fix hvw (hz w).1 hy, h2]
    · intro v hv y hy
      have hvw : v ≠ w := fun h => hv (h ▸ Finset.mem_insert_self w s)
      have hvs : v ∉ s := fun h => hv (Finset.mem_insert_of_mem h)
      obtain ⟨h1, h2⟩ := hout v hvs y hy
      refine ⟨?_, ?_⟩
      · rw [map_mul, mt_mul, ← Matrix.mulVec_mulVec, h1, mulVec_fix hvw (he w _ (ha w).1) hy]
      · rw [mt_mul, ← Matrix.mulVec_mulVec, h2, mulVec_fix hvw (hz w).1 hy]

set_option maxHeartbeats 800000 in

theorem glue : ∀ (D : D7) (V A : HSp D) (e : GA D A →* GA D V) (g : GA D V) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M → (∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ grpAt A (· = v), e a ∈ grpAt V (· = v)) → (∀ v : GlobalTheory.FinPl.Pl D, ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves V c (g * e a) L M v) → ∃ a ∈ GfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ z ∈ Subgroup.center (GA D V), Moves V (z * (g * e a)) L M (fun _ => True) := by
  intro D V A e g L M hL hM he hloc
  classical
  choose a c ha hc hs using hloc
  choose z hz hzm using fun v => GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D V v (c v) (hc v)
  obtain ⟨M', hM'sd, hgM'⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D V L hL).1 g
  obtain ⟨T, hT⟩ := GlobalTheory.FinPl.latV_eq_off_finite D V M' M hM'sd.1 hM.1
  have hoff : ∀ v ∉ T, Moves V g L M (· = v) := fun v hv y hy => by
    rw [hgM' _ y hy, hT v hv]
  obtain ⟨α, hαG, hαC, ζ, hζC, hin, hout⟩ := glue_finset e he a c z ha hz hzm T
  refine ⟨α, hαG, hαC, ζ, hζC, ?_⟩
  have comm : ζ * (g * e α) = g * e α * ζ := ((Subgroup.mem_center_iff.1 hζC) _).symm
  have hmt : ∀ y : Fin V.rank → AE D, Formalism.L2.Theta.mt V (ζ * (g * e α)) *ᵥ y =
      Formalism.L2.Theta.mt V g *ᵥ (Formalism.L2.Theta.mt V (e α) *ᵥ (Formalism.L2.Theta.mt V ζ *ᵥ y)) := fun y => by
    rw [comm, mt_mul, mt_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have loc : ∀ v, Moves V (ζ * (g * e α)) L M (· = v) := by
    intro v y hy
    rw [hmt]
    by_cases hv : v ∈ T
    · obtain ⟨h1, h2⟩ := hin v hv y hy
      rw [h2, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mt_mul]
      exact hs v y hy
    · obtain ⟨h1, h2⟩ := hout v hv y hy
      rw [h2, h1]
      exact hoff v hv y hy
  intro y hy
  rw [GlobalTheory.FinPlLoc.part_lat _ V L y hL.1, GlobalTheory.FinPlLoc.part_lat _ V M _ hM.1]
  have hsupp : ∀ i, (Formalism.L2.Theta.mt V (ζ * (g * e α)) *ᵥ y) i ∈ idAt D (fun _ => True) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  refine and_congr (iff_of_true hy hsupp) (forall_congr' fun v => imp_congr_right fun _ =>
    forall_congr' fun x => forall_congr' fun hx => ?_)
  have hxy : ∀ i, (x • y) i ∈ idAt D (· = v) := fun i => by
    rw [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hx.1
  rw [← Matrix.mulVec_smul]
  exact loc v (x • y) hxy

end GlobalTheory.Core.Mi.LatGlue

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_glue_localHomotheties : ∀ (D : D7) (V A : HSp D) (e : GA D A →* GA D V) (g : GA D V) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M → (∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ grpAt A (· = v), e a ∈ grpAt V (· = v)) → (∀ v : GlobalTheory.FinPl.Pl D, ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves V c (g * e a) L M v) → ∃ a ∈ GfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ z ∈ Subgroup.center (GA D V), Moves V (z * (g * e a)) L M (fun _ => True) := by
  atlas_forward_decl GlobalTheory.Core.Mi.LatGlue.glue
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrame_finitePart_mul_of_carries_lattice : ∀ (D : D7) (V : HSp D) (t : GA D V) (Λ M : Lat V) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)), Moves V t Λ M (fun _ => True) → Formalism.L2.DIV.IsFrame β Λ → Formalism.L2.DIV.IsFrame (finE V t * β) M := by
  first | exact @GlobalTheory.Core.Mi.FrameMove.isFrame_of_moves | exact GlobalTheory.Core.Mi.FrameMove.isFrame_of_moves | (intros; apply GlobalTheory.Core.Mi.FrameMove.isFrame_of_moves <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

theorem ratV_vecB {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    ratV (vecB o ζ) = o.jB *ᵥ ratV ζ :=
  funext fun i => RingHom.map_mulVec (incA D) o.iB ζ i

theorem mt_one' (S : HSp D) : Formalism.L2.Theta.mt S 1 = 1 := GlobalTheory.FinPlLoc.mt_one S

theorem emb_mem_grpAt {S A B : HSp D} (o : OrthDec S A B) {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D A} (ha : a ∈ grpAt A P) :
    o.emb (a, 1) ∈ grpAt S P := by
  have ha' := (GlobalTheory.IwaPlace.mem_congGrp_iff A (idAt D P) a).1 ha
  refine (GlobalTheory.IwaPlace.mem_congGrp_iff S (idAt D P) _).2 fun i j => ?_
  have e : Formalism.L2.Theta.mt S (o.emb (a, 1)) - 1 = HMul.hMul (HMul.hMul o.jA (Formalism.L2.Theta.mt A a - 1)) o.pA := by
    rw [o.mt_emb, ← o.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, mt_one', Matrix.mul_one, Matrix.mul_one]
    abel
  rw [← Matrix.sub_apply, e, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (by rw [Matrix.sub_apply]; exact ha' l k)

theorem embA_mem_grpAt {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {P : GlobalTheory.FinPl.Pl D → Prop}
    {a : GA D A} (ha : a ∈ grpAt A P) : embA d o a ∈ grpAt S P :=
  GlobalTheory.IwaPlace.wittCoreEmbedding_preserves_supportedUnitarySubgroup d (emb_mem_grpAt o ha)

theorem emb_fix {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (a : GA D A) :
    Formalism.L2.Theta.mt S (o.emb (a, 1)) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
  rw [ratV_vecB, Matrix.mulVec_mulVec]
  have := o.emb_jB a 1
  rw [mt_one', Matrix.mul_one] at this
  exact congrArg (· *ᵥ ratV ζ) this

theorem j_zero_mul_mem_lattice_iff {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D)
    (hL : MonoAt d L M v) (w : Fin S₀.rank → AE D) : d.j0 *ᵥ w ∈ latV S L (· = v) ↔ w ∈ latV S₀ M (· = v) := by
  have hc : ∀ {n : ℕ} (x : Mx D S.rank n) (i : Fin n), colMul x i 0 = 0 := fun x i => by
    funext k; simp [colMul]
  rw [hL]
  simp only [Matrix.mulVec_mulVec, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec, Pi.zero_apply, hc,
    zero_mem, implies_true, true_and]

theorem line_loc {S : HSp D} {L : Lat S} {x : Fin S.rank → D.host.E} (hL : IsSelfDualC S L) (hx : x ≠ 0) {c : D.host.E}
    (hc : c ≠ 0) {𝔟 : FI D} (h : ∀ t : D.host.E, t • x ∈ L ↔ c * t ∈ 𝔟) (v : GlobalTheory.FinPl.Pl D) :
    ∀ a ∈ idAt D (· = v), a • ratV x ∈ latV S L (· = v) ↔ incA D c * a ∈ idV 𝔟 v := by
  obtain ⟨𝔞, -, h1, h2⟩ := GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D S L x hL hx
  have e : 𝔞 = FractionalIdeal.spanSingleton _ c⁻¹ * 𝔟 := by
    ext t
    rw [← h1, h, FractionalIdeal.mem_singleton_mul]
    constructor
    · intro ht
      exact ⟨c * t, ht, by field_simp⟩
    · rintro ⟨y, hy, rfl⟩
      rwa [mul_inv_cancel_left₀ hc]
  intro a ha
  rw [h2 v a ha, e, GlobalTheory.SeeSaw.idV_spanSingleton_mul_iff D v 𝔟 c⁻¹ (inv_ne_zero hc), inv_inv]
  exact and_iff_left ha

theorem col_e_ne {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) : (fun r => d.e r i) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun d.e'e i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have : ∀ r, d.e r i = 0 := fun r => congrFun h r
  simp [this] at h1

theorem col_e'_ne {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) : (fun r => d.e' r i) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun d.e'e i) i
  rw [Matrix.mul_assoc, Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have : ∀ r, d.e' r i = 0 := fun r => congrFun h r
  simp [this] at h1

theorem nat_mul_mem_iff {N : ℕ} {v : GlobalTheory.FinPl.Pl D} (hN : (N : 𝓞 D.host.F) ∉ v.asIdeal) (𝔟 : FI D) (a : AE D) :
    incA D (N : D.host.E) * a ∈ idV 𝔟 v ↔ a ∈ idV 𝔟 v := by
  have h0 : (N : D.host.E) ≠ 0 := by
    intro h
    have : N = 0 := by exact_mod_cast h
    exact hN (by rw [this, Nat.cast_zero]; exact zero_mem _)
  constructor
  · intro h
    have := GlobalTheory.SeeSaw.idV_natInv_mul_le D 𝔟 N v hN (GlobalTheory.SeeSaw.idV_incA_mul ((N : D.host.E)⁻¹) 𝔟 v h)
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul] at this
  · intro h
    rw [map_natCast, ← nsmul_eq_mul]
    exact nsmul_mem h N

theorem pow_mul_mem_iff {N : ℕ} {v : GlobalTheory.FinPl.Pl D} (hN : (N : 𝓞 D.host.F) ∉ v.asIdeal) {lam : D.host.E}
    (hl : lam = (N : D.host.E) ∨ lam = -(N : D.host.E)) (𝔟 : FI D) (n : ℕ) (a : AE D) :
    incA D (lam ^ n) * a ∈ idV 𝔟 v ↔ a ∈ idV 𝔟 v := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul, mul_assoc, ih]
    rcases hl with rfl | rfl
    · exact nat_mul_mem_iff hN 𝔟 a
    · rw [map_neg, neg_mul, neg_mem_iff]; exact nat_mul_mem_iff hN 𝔟 a

theorem val_nat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    {N : ℕ} (hN : (N : 𝓞 D.host.F) ∉ p.v.asIdeal) : valuation k (p.pr (incA D (N : D.host.E))) = 1 := by
  obtain ⟨PP, hP⟩ := GlobalTheory.SeeSaw.LevelTest.exists_prime p
  obtain ⟨ε, hε, he⟩ := p.above
  have hu := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP _ ε hP hε he
  have h1 := GlobalTheory.SeeSaw.LevelTest.val_le_one p (N : 𝓞 D.host.E)
  have h2 := GlobalTheory.SeeSaw.LevelTest.val_lt_one_iff p hP (N : 𝓞 D.host.E)
  have e : ((N : 𝓞 D.host.E) : D.host.E) = N := by simp
  rw [e] at h1 h2
  refine le_antisymm h1 (not_lt.1 fun h => hN ?_)
  rw [← hu]
  have := h2.1 h
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (N : 𝓞 D.host.F) ∈ PP.asIdeal
  rwa [map_natCast]

section Rows

variable {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {B : SBes X h u ψ (D.sp.X 0)} {μ lam : D.host.E}

theorem g_ne (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : ((X.B.g : ℕ) : D.host.E) ≠ 0 := by
  rw [X.g_eq]
  exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

theorem lam_ne (hF : B.FrameAt μ lam) : lam ≠ 0 := by
  rcases hF.sign with hl | hl <;> rw [hl]
  · exact g_ne X
  · exact neg_ne_zero.2 (g_ne X)

theorem scl_ne (hF : B.FrameAt μ lam) (i : Fin D.R.rS) : GlobalTheory.Core.SBesEx.scl μ lam i ≠ 0 :=
  mul_ne_zero hF.ne (pow_ne_zero _ (lam_ne hF))

theorem rows_shape (hE : GlobalTheory.Core.Mi.IdE X) (hF : B.FrameAt μ lam) :
    IsSelfDualC (D.sp.Y 0) (latS D) ∧ IsSelfDualC B.V₀ (coreLat B.d (latS D)) ∧
    (∀ v, MonoAt B.d (latS D) (coreLat B.d (latS D)) v) ∧
    (∀ v (i : Fin D.R.rS), ∀ a ∈ idAt D (· = v), colMul B.d.jX i a ∈ latV (D.sp.Y 0) (latS D) (· = v) ↔
      incA D (GlobalTheory.Core.SBesEx.scl μ lam i) * a ∈ idV (dI D ^ (D.R.rS - i.1)) v) ∧
    (∀ v (i : Fin D.R.rS), ∀ a ∈ idAt D (· = v), colMul B.d.jY i a ∈ latV (D.sp.Y 0) (latS D) (· = v) ↔
      incA D (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * a ∈ idV (dI D ^ (D.R.rS - i.1))⁻¹ v) ∧
    ∀ v, LineAt (vecB B.o B.ζ) μ (coreLat B.d (latS D)) v := by
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.rowLattice_selfDual_components_rescaled_word_frame D X h u ψ _ B μ lam hE hF
  obtain ⟨h5, h6⟩ := GlobalTheory.T.selfDual_lineStable_lattice_splitsAlongWitt_selfDualCore D _ _ _ B.d (latS D) h1 h2
  obtain ⟨h7, -, h8⟩ := GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm D X h u ψ _ B μ lam hE hF
  refine ⟨h1, h5, h6, fun v i => ?_, fun v i => ?_, fun v a ha => ?_⟩
  · rw [← GlobalTheory.T.rowLineIdeal_eq_inverseDifferent_pow D i]
    exact line_loc h1 (col_e_ne B.d i) (scl_ne hF i) (h3 i) v
  · rw [← GlobalTheory.T.rowLineIdeal_eq_inverseDifferent_pow D i]
    exact line_loc h1 (col_e'_ne B.d i) (inv_ne_zero (star_ne_zero.2 (scl_ne hF i))) (h4 i) v
  · rw [line_loc h5 h8 hF.ne h7 v a ha, GlobalTheory.SeeSaw.idV_one_eq_intAt]

variable {F : Formalism.L2.Forms.Forms0 D u} {tr : Formalism.L2.SG.ColDict.Transport X u F} {hK : X.LevelSubgroupCharacter} {a₀ : GA D (D.sp.X 0)}

theorem rows_trace (hE : GlobalTheory.Core.Mi.IdE X) (hF : B.FrameAt μ lam) (hM : Formalism.L2.SG.ColDict.LevelMatch X tr hK)
    (hA : B.Adapted tr.wt) (h0 : IsTransportAdelicCorrection tr a₀) (v : GlobalTheory.FinPl.Pl D) {N : Lat (D.sp.X 0)}
    (hN : latV (D.sp.X 0) N (· = v) = latV (D.sp.X 0) (lat0 F) (· = v)) : TraceAt B.o a₀ N (coreLat B.d (latS D)) v := by
  intro y hy
  rw [hN, GlobalTheory.T.transportCorrection_carries_columnLattice_rowTrace D X h u ψ F tr hK B a₀ hE hM hA h0 v y hy, j_zero_mul_mem_lattice_iff B.d _ _ v ((rows_shape hE hF).2.2.1 v)]

theorem loc_of_core (hψ : IsStdChar D ψ (-1)) (hE : GlobalTheory.Core.Mi.IdE X) (hF : B.FrameAt μ lam) {v : GlobalTheory.FinPl.Pl D}
    (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) {L : Lat (D.sp.Y 0)} {M : Lat B.V₀}
    (hL : IsSelfDualC (D.sp.Y 0) L) (hM : IsSelfDualC B.V₀ M) (h1 : MonoAt B.d L M v) (h2 : PrimAt ψ B.d L v)
    (h3 : LastAt ψ B.d (vecB B.o B.ζ) L M v)
    (hc : ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) v a ∧ NormOneAt v c ∧
      SMoves B.V₀ c (B.o.emb (a₀ * a, 1)) M (coreLat B.d (latS D)) v) :
    ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) v a ∧ NormOneAt v c ∧
      SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) L (latS D) v := by
  obtain ⟨a, c, ha, hc, hm⟩ := hc
  obtain ⟨s1, s2, s3, s4, -, s6⟩ := rows_shape hE hF
  have hl : lam = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E) ∨ lam = -((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E) := by
    rw [← X.g_eq]; exact hF.sign
  obtain ⟨p1, p2⟩ := GlobalTheory.T.psi_primitive_of_inverseDifferent_lines D ψ hψ _ _ _ B.d (vecB B.o B.ζ) (latS D) _ μ v hF.ne (s6 v) (fun i x hx => by
    rw [s4 v i x hx, GlobalTheory.Core.SBesEx.scl, mul_comm μ, map_mul, mul_assoc, pow_mul_mem_iff hg hl])
  exact ⟨a, c, ha, hc, GlobalTheory.T.sMoves_emb0_of_sMoves_selfDual D ψ _ _ _ B.d (vecB B.o B.ζ) L (latS D) M _ v c _ hL s1 hM
    (GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm D X h u ψ _ B μ lam hE hF).2.2 h1 (s3 v) h2 p1 h3 p2 hc (emb_fix _ _ _) hm⟩

theorem loc_level (hE : GlobalTheory.Core.Mi.IdE X) (hF : B.FrameAt μ lam) (hM : Formalism.L2.SG.ColDict.LevelMatch X tr hK)
    (hA : B.Adapted tr.wt) (h0 : IsTransportAdelicCorrection tr a₀) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (hp : p.UnitAA) (ϖ : k)
    (hϖ : valuation k (p.pr (incA D ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))) = valuation k ϖ)
    (hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ p.v.asIdeal)
    (hz : valuation k (p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = 1) {L : Lat (D.sp.Y 0)} {N : Lat (D.sp.X 0)}
    (hL : IsSelfDualC (D.sp.Y 0) L) (hN : latV (D.sp.X 0) N (· = p.v) = latV (D.sp.X 0) (lat0 F) (· = p.v))
    (hW : WShape p B.d B.o B.ζ L (fun i => (ϖ ^ (i.1 + 1))⁻¹) (fun i => (ϖ ^ (2 * D.R.rS - i.1 + 1))⁻¹) ((ϖ ^ (D.R.rS + 1))⁻¹)
      1 N) :
    ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) p.v a ∧ NormOneAt p.v c ∧
      SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) L (latS D) p.v := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := rows_shape hE hF
  obtain ⟨-, z2, -⟩ := GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm D X h u ψ _ B μ lam hE hF
  have hS := GlobalTheory.T.splitPlaceComponent_monomialLattice_splitCore D k p _ _ _ _ _ B.d B.o B.ζ (latS D) _ N (fun i => GlobalTheory.Core.SBesEx.scl μ lam i)
    (fun i => (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹) μ a₀ (s3 _)
    (fun i x hx => by rw [s4 _ i x hx, (GlobalTheory.T.inverseDifferentPow_completion_trivial_at_splitPlace D k p hp _ _).1]) (fun i x hx => by rw [s5 _ i x hx, (GlobalTheory.T.inverseDifferentPow_completion_trivial_at_splitPlace D k p hp _ _).2])
    (s6 _) (GlobalTheory.T.selfDualLattice_splitsOff_unitNormLine_at_place D _ _ _ B.o B.ζ _ μ _ _ B.line s2 hF.ne (s6 _) z2 hT) (rows_trace hE hF hM hA h0 _ hN)
  set f : D.host.E →+* k := p.pr.comp (incA D) with hf
  have hfe : ∀ x, p.pr (incA D x) = f x := fun _ => rfl
  have vg : valuation k (f lam) = valuation k ϖ := by
    rw [← hϖ, ← X.g_eq, hfe]
    rcases hF.sign with hl | hl <;> rw [hl]
    rw [map_neg, Valuation.map_neg]
  have vg' : valuation k (f (star lam)) = valuation k ϖ := by
    rw [← vg]
    rcases hF.sign with hl | hl <;> rw [hl] <;> simp
  have hϖ0 : valuation k ϖ ≠ 0 := by
    rw [← vg]; exact (Valuation.ne_zero_iff _).2 ((map_ne_zero f).2 (lam_ne hF))
  have hμ0 : valuation k (f μ) ≠ 0 := (Valuation.ne_zero_iff _).2 ((map_ne_zero f).2 hF.ne)
  have hμ : valuation k (f (star μ)) = (valuation k (f μ))⁻¹ := by
    have hT' := val_nat p hT
    rw [z2, hfe, map_neg, Valuation.map_neg, map_mul, map_mul, map_mul, map_mul, ← hfe (Nat.cast _), hT', mul_one] at hz
    exact eq_inv_of_mul_eq_one_right hz
  refine GlobalTheory.T.lattices_same_splitShape_carried_by_central D k p _ _ _ _ _ B.d B.o B.ζ L (latS D) N N _ _ _ _ _ _ (ϖ ^ (D.R.rS + 1) * f μ)⁻¹ a₀ B.line hL s1 hW hS rfl
    (inv_ne_zero (mul_ne_zero (pow_ne_zero _ ((Valuation.ne_zero_iff _).1 hϖ0)) ((map_ne_zero f).2 hF.ne))) (fun i => ?_)
    (fun i => ?_) ?_
  · have e : D.R.rS + 1 = (D.R.rS - i.1) + (i.1 + 1) := by have := i.2; omega
    simp only [hfe, GlobalTheory.Core.SBesEx.scl, map_mul, map_pow, map_inv₀, vg]
    rw [e, pow_add _ (D.R.rS - i.1)]
    field_simp
  · have e : 2 * D.R.rS - i.1 + 1 = (D.R.rS - i.1) + (D.R.rS + 1) := by have := i.2; omega
    simp only [hfe, GlobalTheory.Core.SBesEx.scl, star_mul', star_pow, map_mul, map_pow, map_inv₀, vg', hμ]
    rw [e, pow_add _ (D.R.rS - i.1)]
    field_simp
  · simp only [hfe, map_mul, map_pow, map_inv₀]
    field_simp

end Rows

theorem mem_GfC_of_grpAt {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D S} (ha : a ∈ grpAt S P) : a ∈ GfC S := by
  rw [GlobalTheory.Core.Mi.CenAct.mem_GfC_iff]
  ext i j
  have h1 := GlobalTheory.FinPlLoc.infPart_of_idAt ((GlobalTheory.IwaPlace.mem_congGrp_iff S (idAt D P) a).1 ha i j)
  rw [RingHom.map_sub, sub_eq_zero] at h1
  rw [Matrix.map_apply]
  refine Eq.trans h1 ?_
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

theorem conj_mem_grpAt {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D S} (ha : a ∈ grpAt S P) (t : GA D S) :
    t⁻¹ * a * t ∈ grpAt S P := by
  have := (MonoidHom.normal_ker _).conj_mem a ha t⁻¹
  rwa [inv_inv] at this

theorem moves_trans {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {g g' : GA D S} {L M N : Lat S} (h : Moves S g L M P)
    (h' : Moves S g' M N P) : Moves S (g' * g) L N P := by
  intro y hy
  rw [h y hy, h' _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy), Matrix.mulVec_mulVec, GlobalTheory.FinPlLoc.mt_mul]

theorem moves_symm {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S} {L M : Lat S} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  rw [h _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy), Matrix.mulVec_mulVec, ← GlobalTheory.FinPlLoc.mt_mul, mul_inv_cancel, mt_one',
    Matrix.one_mulVec]

theorem moves_conj {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {t : GA D S} {L M : Lat S} (h : Moves S t L M P) (κ : GA D S) :
    Moves S (t⁻¹ * κ * t) L L P ↔ Moves S κ M M P := by
  constructor
  · intro h1
    have := moves_trans (moves_trans (moves_symm h) h1) h
    rwa [show t * (t⁻¹ * κ * t * t⁻¹) = κ by group] at this
  · intro h1
    have := moves_trans (moves_trans h h1) (moves_symm h)
    rwa [← mul_assoc] at this

theorem mem_St_mul {n : ℕ} (g β x : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) : x ∈ St (g * β) ↔ g⁻¹ * x * g ∈ St β := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy ⊢
    rw [show x = g * (g⁻¹ * x * g) * g⁻¹ by group, ← hy]
    group

section Chain

variable {u : D.what₂.Word} {d : GlobalTheory.SeeSaw.Dat D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1)
  (F : Formalism.L2.Forms.Forms0 D u)

def ChainFacts (L : Lat (D.sp.Y 0)) (b : GlobalTheory.SeeSaw.BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS) : Prop :=
  ∃ M : Lat b.V₀,
    (∀ v, v ∉ d.c.S → IsSelfDualC b.V₀ M ∧ MonoAt b.d L M v ∧ PrimAt d.c.ψ b.d L v ∧ LastAt d.c.ψ b.d (vecB b.o b.ζ) L M v) ∧
    (∀ v, v ∉ d.c.S → ¬ o.atT v → ∃ LL, IsSelfDualC b.L LL ∧ OrthAt b.o M (d.x 0).L LL v) ∧
    (∀ i, ∃ β₀ : GlobalTheory.FinPl.Frame (o.p i) b.V₀ (Fin (D.sp.X 0).rank ⊕ Fin 1), IsSumFrame b.o b.ζ (o.β 0 i) β₀ ∧
      β₀.IsLat M (GlobalTheory.LatPair.gluedS o.q 1 (o.Q 0 i).ker (o.Q 0 i).vec)) ∧
    (∀ PP, valuation (G PP).k ((G PP).q.pr (incA D (star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ))) = 1 ∧
      WShape (G PP).q b.d b.o b.ζ L (fun i => ((((G PP).S.ϖ : (G PP).kˣ) : (G PP).k) ^ (i.1 + 1))⁻¹)
        (fun i => ((((G PP).S.ϖ : (G PP).kˣ) : (G PP).k) ^ (2 * D.R.rS - i.1 + 1))⁻¹)
        (((((G PP).S.ϖ : (G PP).kˣ) : (G PP).k) ^ (D.R.rS + 1))⁻¹) 1 (d.x 0).L) ∧
    ∀ v, v ∉ d.c.S → ∀ a ∈ grpAt (D.sp.X 0) (· = v), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = y.1.1 →
      ((y : GL _ _) ∈ F.cls0.lev.U ↔ Moves (D.sp.Y 0) (embA b.d b.o a) L L (· = v))

theorem good_zero (hO : GlobalTheory.FinPl.PinOff o) (ρ : ℕ) (h0 : 0 + 2 * ρ + 2 = D.R.m) :
    (∀ v, v ∉ d.c.S → GoodBF d.c.ψ (d.B 0 ρ h0) ((d.jac 0 ρ h0).lev (d.x (0 + 1)).vol) (o.L 0) (o.M 0 ρ h0) (o.L (0 + 1))
      (d.x (0 + 1)).L v) ∧
    ∀ i, GluedCore (d.B 0 ρ h0) (o.M 0 ρ h0) o.q (o.β 0 i) (o.β₀ 0 ρ h0 i) (o.Q 0 i) := by
  cases ρ with
  | zero => exact ⟨fun v hv => (hO.goodLast 0 h0 v hv).1, hO.gluedLast 0 h0⟩
  | succ σ => exact ⟨(hO.shape 0 σ h0).good, (hO.shape 0 σ h0).gl⟩

theorem chainFacts (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hB : d.Base) (hO : GlobalTheory.FinPl.PinOff o) (hLev : LevX F d h0) :
    ChainFacts o G F (o.L 0) (d.bes 0 D.R.rS h0) := by
  have hm : 0 < D.R.m := by omega
  obtain ⟨g1, g2⟩ := good_zero o hO _ h0
  refine ⟨o.M 0 _ h0, fun v hv => ⟨(g1 v hv).sdV₀, (g1 v hv).monoV, (g1 v hv).prim,
    GlobalTheory.T.lastWittLine_of_besselJacobiLatticesGood D _ hB.com.std _ _ _ _ _ _ _ v (g1 v hv)⟩, fun v hv hT => hO.core 0 _ h0 v hv hT,
    fun i => ⟨_, (g2 i).sum, (g2 i).lat⟩, fun PP => ⟨(G PP).hz_unit 0 _ h0,
      GlobalTheory.T.weil_shape_of_frame_moves D u d o.τ PP.1 (G PP) _ h0 (o.L 0) (hB.st 0 hm).frame ((hO.moves 0 hm).2 _)⟩, fun v hv a ha y hy => ?_⟩
  rw [(hLev a (mem_GfC_of_grpAt ha) y hy).1]
  exact (GlobalTheory.T.mem_chainLevel_iff_carriesLattice_offLevel D d.c 0 (d.st 0) (hB.st 0 hm) v hv _ (conj_mem_grpAt (embA_mem_grpAt _ _ ha) _)).trans
    (moves_conj ((hO.moves 0 hm).2 _) _)

end Chain

def toBes {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : SBes X h u ψ (D.sp.X 0)) : GlobalTheory.SeeSaw.BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS :=
  ⟨B.V₀, B.L, B.d, B.o, B.ζ, B.line, B.cpt, B.vN⟩

theorem eq_toBes {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : SBes X h u ψ (D.sp.X 0)) (b : GlobalTheory.SeeSaw.BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS)
    (v : Vol (D.sp.X 0)) (e : B.lev = b.lev v) : b = toBes B := by
  obtain ⟨V₀, L, dd, o, ζ, line, cpt, vN⟩ := b
  obtain ⟨V₀', L', dd', o', ζ', line', cpt', vA', vN', t1, t2, t3⟩ := B
  cases e
  rfl

theorem stab_read (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (β : GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β (latS D)) (κ : GA D (D.sp.Y 0)) :
    ((iotaX X h κ).1 = 1 ↔ κ ∈ GfC (D.sp.Y 0)) ∧ ((iotaX X h κ).2 ∈ X.B.I.Kset ↔ finE (D.sp.Y 0) κ ∈ St β) :=
  ⟨(GlobalTheory.SeeConjReadIota.read_iota X h β hβ κ).1, (GlobalTheory.SeeConjReadIota.read_iota X h β hβ κ).2.1⟩

theorem kset_conj (I : AutInst) {x : I.Gf} (hx : x ∈ I.Kset) (y : I.Gf) : x * y * x⁻¹ ∈ I.Kset ↔ y ∈ I.Kset := by
  have hm : ∀ {a b : I.Gf}, a ∈ I.Kset → b ∈ I.Kset → a * b ∈ I.Kset := fun {a b} ha hb => by
    show ((a * b : I.Gf) : GL _ _) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_mul]
    exact mul_mem ha hb
  have hi : ∀ {a : I.Gf}, a ∈ I.Kset → a⁻¹ ∈ I.Kset := fun {a} ha => by
    show ((a⁻¹ : I.Gf) : GL _ _) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_inv]
    exact inv_mem ha
  refine ⟨fun h => ?_, fun h => hm (hm hx h) (hi hx)⟩
  have := hm (hm (hi hx) h) hx
  rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this

theorem stab_of_frame (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word)
    (β : GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) (g t z : GA D (D.sp.Y 0))
    (hz : z ∈ Subgroup.center (GA D (D.sp.Y 0))) (hβ : Formalism.L2.DIV.IsFrame (finE (D.sp.Y 0) (z * g * t) * β) (latS D))
    (κ : GA D (D.sp.Y 0)) :
    (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX X h).symm (1, X.xu u))⁻¹ * g * t) * β)) ↔
      ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset) := by
  have hR := stab_read X h _ hβ
  have e3 : (iotaX X h ((iotaX X h).symm (1, X.xu u) * κ * ((iotaX X h).symm (1, X.xu u))⁻¹)).2 =
      X.xu u * (iotaX X h κ).2 * (X.xu u)⁻¹ := by
    rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]
    rfl
  generalize (iotaX X h).symm (1, X.xu u) = x at e3 ⊢
  have e1 : finE (D.sp.Y 0) (x⁻¹ * g * t) * β = finE (D.sp.Y 0) (z * x)⁻¹ * (finE (D.sp.Y 0) (z * g * t) * β) := by
    have e0 : (z * x)⁻¹ * (z * g * t) = x⁻¹ * g * t := by group
    rw [← mul_assoc, ← map_mul, e0]
  have e2 : (finE (D.sp.Y 0) (z * x)⁻¹)⁻¹ * finE (D.sp.Y 0) κ * finE (D.sp.Y 0) (z * x)⁻¹ = finE (D.sp.Y 0) (x * κ * x⁻¹) := by
    have := Subgroup.mem_center_iff.1 hz (x * κ * x⁻¹)
    have e0 : z * x * κ * (z * x)⁻¹ = x * κ * x⁻¹ :=
      calc z * x * κ * (z * x)⁻¹ = z * (x * κ * x⁻¹) * z⁻¹ := by group
        _ = x * κ * x⁻¹ := by rw [← this]; group
    rw [← map_inv, ← map_mul, ← map_mul, inv_inv, e0]
  rw [e1, mem_St_mul, e2, ← (hR _).2, e3, kset_conj _ (X.xu_K u), (hR κ).1]

set_option maxHeartbeats 1000000 in

theorem stab_match : ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.Core.Mi.IdE S.X → d.Base → IsTypePlaces d.c.Pg → GlobalTheory.FinPl.PinOff o → GlobalTheory.LocMod.PinGBy G o.cG → (∀ v : GlobalTheory.FinPl.Pl D, o.atT v ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) → (∀ v : GlobalTheory.FinPl.Pl D, ¬ o.atT v → GlobalTheory.FinPl.latV (D.sp.X 0) (d.x 0).L (· = v) = GlobalTheory.FinPl.latV (D.sp.X 0) ((F₀ u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) (· = v)) → LevX (F₀ u) d h0 → ∀ (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)), B.lev = d.B 0 D.R.rS h0 → B.Adapted (S.tr u).wt → B.FrameTied → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (S.tr u) a₀ → ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β)) ↔ ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset) := by
  intro D u F₀ S d k _ _ _ _ ι o G h0 hE hB hT hO hG hA hL hLev B hBl hBa hBf a₀ ha₀
  obtain ⟨μ, lam, hF⟩ := hBf
  have hm : 0 < D.R.m := by omega
  have hC := chainFacts o G (F₀ u) h0 hB hO hLev
  have hb : (show GlobalTheory.SeeSaw.BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS from d.bes 0 D.R.rS h0) = toBes B := eq_toBes B _ _ hBl
  replace hC : ChainFacts o G (F₀ u) (o.L 0) (toBes B) := hb ▸ hC
  obtain ⟨M, c1, c2, c3, c4, c5⟩ := hC
  have hL0 : IsSelfDualC (D.sp.Y 0) (o.L 0) := (hO.moves 0 hm).1
  obtain ⟨s1, s2, s3, -, -, s6⟩ := rows_shape hE hF
  obtain ⟨-, z2, -⟩ := GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm D S.X S.inst u d.c.ψ _ B μ lam hE hF
  have hg : ∀ v : GlobalTheory.FinPl.Pl D, v ∉ d.c.S → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    intro v hv h
    obtain ⟨PP, ⟨h1, h2⟩, -⟩ := hT.2 v h
    exact hv (Finset.mem_image.2 ⟨PP, h1, h2⟩)
  have loc : ∀ v : GlobalTheory.FinPl.Pl D, ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) v a ∧ NormOneAt v c ∧
      SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) (o.L 0) (latS D) v := by
    intro v
    by_cases hv : v ∈ d.c.S
    · obtain ⟨PP, hP, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨ε, hε, he⟩ := (G ⟨PP, hP⟩).q.above
      have hu := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP _ ε (G ⟨PP, hP⟩).idem hε he
      have hnT : ¬ o.atT (G ⟨PP, hP⟩).q.v := by
        rintro ⟨i, hi⟩
        exact hO.off i (hi ▸ hu ▸ hv)
      obtain ⟨q⟩ : Nonempty (GlobalTheory.LatPair.Unif (G ⟨PP, hP⟩).k) := inferInstance
      have hϖ := (GlobalTheory.SeeSaw.LevelTest.val_eq_unif (G ⟨PP, hP⟩).q (G ⟨PP, hP⟩).idem q (hT.1 PP hP)
        (GlobalTheory.SeeSaw.LevelTest.g_notMem_sq PP)).trans (GlobalTheory.SeeSaw.LevelTest.unif_val q (G ⟨PP, hP⟩).S.unif)
      rw [hu]
      exact loc_level hE hF (S.lev u) hBa ha₀ (G ⟨PP, hP⟩).q (G ⟨PP, hP⟩).unit _ (by simpa using hϖ)
        (fun h => hnT ((hA _).2 h)) (c4 ⟨PP, hP⟩).1 hL0 (hL _ hnT) (c4 ⟨PP, hP⟩).2
    · obtain ⟨d1, d2, d3, d4⟩ := c1 v hv
      refine loc_of_core hB.com.std hE hF (hg v hv) hL0 d1 d2 d3 d4 ?_
      by_cases hvT : o.atT v
      · have hTv := (hA v).1 hvT
        obtain ⟨i, rfl⟩ := hvT
        obtain ⟨β₀, e1, e2⟩ := c3 i
        have hr : 3 ≤ Fintype.card (Fin (D.sp.X 0).rank) := by
          have h1 := D.R.m_add_three_le_k
          rw [Fintype.card_fin, D.sp.X_rank 0 (Nat.zero_le _), Ranks.N]
          omega
        refine GlobalTheory.T.exists_central_element_homothetic_gluedCores D k (o.p i) _ _ _ B.o B.ζ _ (o.β 0 i) β₀ M _ μ _ o.q (o.Q 0 i) a₀ hr e1 d1 s2 e2 hF.ne (s6 _) z2
          (GlobalTheory.SeeSaw.LevelTest.unifT_of _ _ hTv) fun a ha => ?_
        obtain ⟨y, hy, hU⟩ := GlobalTheory.T.columnLevel_iff_rowLattice_kept_at_place D S.X S.inst u d.c.ψ (F₀ u) (S.tr u) S.Y.hK B a₀ hE (S.lev u) hBa ha₀ _ (hg _ hv) a ha
        exact ((GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises D _ _ _ B.d _ _ _ _ d2).symm.trans ((c5 _ hv a ha y hy).symm.trans hU)).trans
          (GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises D _ _ _ B.d _ _ _ _ (s3 _))
      · obtain ⟨LL, e1, e2⟩ := c2 v hv hvT
        have hTv : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := fun h => hvT ((hA v).2 h)
        exact GlobalTheory.T.orthogonalSumCores_homothetic_off_level D _ _ _ B.o B.ζ M _ (d.x 0).L LL μ _ v a₀ B.line e1 e2
          (rows_trace hE hF (S.lev u) hBa ha₀ v (hL v hvT))
          (GlobalTheory.T.selfDualLattice_splitsOff_unitNormLine_at_place D _ _ _ B.o B.ζ _ μ _ v B.line s2 hF.ne (s6 v) z2 hTv) hF.ne (s6 v) z2 hTv
  obtain ⟨a, haf, hac, z, hz, hmv⟩ := GlobalTheory.T.exists_central_glue_localHomotheties D (D.sp.Y 0) (D.sp.X 0) (embA B.d B.o) (embA B.d B.o a₀) (o.L 0) (latS D) hL0 s1
    (fun v a ha => embA_mem_grpAt _ _ ha) (fun v => by simpa only [map_mul] using loc v)
  rw [← map_mul] at hmv
  exact ⟨a, haf, hac, stab_of_frame S.X S.inst u d.bot.β _ _ z hz
    (GlobalTheory.T.isFrame_finitePart_mul_of_carries_lattice D (D.sp.Y 0) _ d.bot.Λ (latS D) d.bot.β (moves_trans ((hO.moves 0 hm).2 _) hmv) (hB.st 0 hm).frame)⟩

end GlobalTheory.Core.Mi.LatMatch

end
end
