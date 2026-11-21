import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentSemilinearOfBasis
import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationFreeStageTrueGroupColumnChoiceStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FittingLaterStagesRowIsConstructionState

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

def bkMk {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE)
    (b : ∀ u, (C.fm u).ramSub → (Fin m → B.LL) → B.LL)
    (hb : ∀ u φ x, B.embLL (b u φ x) = W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x))
    (u : B.Word) : (C.fm u).ramSub →ₗ[B.LL] Module.Dual B.LL (Fin m → B.LL) :=
  LinearMap.mk₂ B.LL (b u)
    (fun φ ψ x => B.embLL.injective (by
      rw [map_add, hb, hb, hb, map_add, (W.Bu_linL u _).map_add]))
    (fun a φ x => B.embLL.injective (by
      rw [smul_eq_mul, map_mul, hb, hb, map_smulₛₗ, (W.Bu_linL u _).map_smul, smul_eq_mul]))
    (fun φ x y => B.embLL.injective (by
      rw [map_add, hb, hb, hb, map_add, (W.Bu_linR u _).map_add]))
    (fun a φ x => B.embLL.injective (by
      rw [smul_eq_mul, map_mul, hb, hb, map_smulₛₗ, (W.Bu_linR u _).map_smul, smul_eq_mul]))

open Classical in

def bkOf {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE) (u : B.Word) :
    (C.fm u).ramSub →ₗ[B.LL] Module.Dual B.LL (Fin m → B.LL) :=
  if H : ∀ u (φ : (C.fm u).ramSub) (x : Fin m → B.LL),
      W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) ∈ Set.range B.embLL then
    bkMk W c (fun u φ x => (H u φ x).choose) (fun u φ x => (H u φ x).choose_spec) u
  else 0

theorem bkOf_spec {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE)
    (H : ∀ u (φ : (C.fm u).ramSub) (x : Fin m → B.LL),
      W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) ∈ Set.range B.embLL)
    (u : B.Word) (φ : (C.fm u).ramSub) (x : Fin m → B.LL) :
    W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) = B.embLL (bkOf W c u φ x) := by
  classical
  unfold bkOf
  rw [dif_pos H]
  exact (H u φ x).choose_spec.symm

end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

def prescribedRowLat {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (jE : (Fin m → B.LL) →ₛₗ[B.embLL] W.EE) :
    Submodule (𝓞 B.LL) (Fin m → B.LL) where
  carrier := {x | ∀ w : W.what₂.places.Pl, ∃ d : 𝓞 B.LL, d ∉ (w : HeightOneSpectrum (𝓞 B.LL)).asIdeal ∧
    d • x ∈ Submodule.span (𝓞 B.LL) {y | jE y ∈ W.what₂.RRset (W.what₂.muAt w)}}
  add_mem' := by
    intro x y hx hy w
    obtain ⟨a, ha, hax⟩ := hx w
    obtain ⟨b, hb, hby⟩ := hy w
    refine ⟨a * b, fun h => ((w : HeightOneSpectrum (𝓞 B.LL)).isPrime.mem_or_mem h).elim ha hb, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hax
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hby
  zero_mem' := fun w => ⟨1, (Ideal.ne_top_iff_one _).1 (w : HeightOneSpectrum (𝓞 B.LL)).isPrime.ne_top, by simp⟩
  smul_mem' := by
    intro s x hx w
    obtain ⟨a, ha, hax⟩ := hx w
    exact ⟨a, ha, by rw [smul_comm]; exact Submodule.smul_mem _ _ hax⟩
end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

theorem exists_divStage_of_pk : ∀ (B : Base) (C : Cols B) (G : Type) [Group G] (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) (n : Nums p W₀) (η : ℕ → B.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w), (∀ v, IsUnit (p.Xo v).det) → ∀ (Ln : ∀ u, Submodule (𝓞 B.LL) ((C.fm u).lat 0).V) (h : B.Word → ℝ) (etaF : ℝ), ∃ V : DivStage B C (p.what₂ e W₀ n η hη), DivIs p V ∧ (∀ u x, x ∈ (V.div.Nu u).L ↔ V.nuIn u x ∈ Ln u) ∧ V.div.h = h ∧ V.div.etaF = etaF ∧ V.div.HH = sFrame V.div.Nu V.div.h + V.div.RR.muMax ∧ ((∀ u φ x, n.Bu u (V.jN u φ) (V.jEE x) ∈ Set.range B.embLL) → ∀ u φ x, n.Bu u (V.jN u φ) (V.jEE x) = B.embLL (V.div.Bk u φ x)) := by
  intro B C G _ p e W₀ n η hη hXo Ln h etaF
  classical
  obtain ⟨X0, hX0, hX0n⟩ := GlobalTheory.exists_frames_normAt_eq_norm B.LL B.embLL (p.what₂ e W₀ n η hη).EE p.nR p.cR ⊥
  choose m bN XN hXN hXNn using fun u : B.Word =>
    GlobalTheory.Mem.exists_restricted_frames B.LL ((C.fm u).lat 0) (C.fm u).ramSub ⊥ ((C.fm u).lat_good 0).1
  let X : InfinitePlace B.LL → Matrix (Fin p.nR) (Fin p.nR) ℂ := fun v =>
    if v = InfinitePlace.mk B.embLL then X0 v else p.Xo v
  let Lr : Submodule (𝓞 B.LL) (Fin p.nR → B.LL) :=
    prescribedRowLat (p.what₂ e W₀ n η hη) (GlobalTheory.Mem.coordForm B.embLL p.cR)
  let RR : HLat B.LL :=
    { V := Fin p.nR → B.LL, ι := Fin p.nR, b := Pi.basisFun B.LL (Fin p.nR), X := X, L := Lr }
  let Nu : B.Word → HLat B.LL := fun u =>
    { V := (C.fm u).ramSub, ι := Fin (m u), b := bN u, X := XN u,
      L := (Ln u).comap ((C.fm u).ramSub.subtype.restrictScalars (𝓞 B.LL)) }
  let Dd : DivData B.LL B.Word :=
    { RR := RR, Nu := Nu, Bk := bkOf (p.what₂ e W₀ n η hη) p.cR, h := h,
      HH := sFrame Nu h + RR.muMax, HH_ge := le_rfl, etaF := etaF, Dall := p.Dall, delP := p.delp,
      delP_le_one := p.delp_le_one }
  let V : DivStage B C (p.what₂ e W₀ n η hη) :=
    { div := Dd
      div_good := ⟨fun v => by
        show IsUnit (if v = InfinitePlace.mk B.embLL then X0 v else p.Xo v).det
        split_ifs
        · exact hX0 v
        · exact hXo v, fun u v => hXN u v⟩
      jEE := GlobalTheory.Mem.coordForm B.embLL p.cR
      jEE_basis := by
        have : (fun i => GlobalTheory.Mem.coordForm B.embLL p.cR (Pi.basisFun B.LL (Fin p.nR) i)) = p.cR :=
          funext (GlobalTheory.Mem.coordForm_basisFun B.embLL p.cR)
        show LinearIndependent ℂ (fun i => GlobalTheory.Mem.coordForm B.embLL p.cR (Pi.basisFun B.LL (Fin p.nR) i)) ∧
          Submodule.span ℂ (Set.range (fun i => GlobalTheory.Mem.coordForm B.embLL p.cR (Pi.basisFun B.LL (Fin p.nR) i))) = ⊤
        rw [this]
        exact ⟨p.cR.linearIndependent, p.cR.span_eq⟩
      jN := GlobalTheory.Mem.ramForm (p.what₂ e W₀ n η hη)
      jN_basis := fun u => GlobalTheory.Mem.ramForm_basis (p.what₂ e W₀ n η hη) u (bN u)
      Dall_eq := rfl
      delP_eq := rfl
      nuIn := fun u => (C.fm u).ramSub.subtype
      nuIn_inj := fun u => (C.fm u).ramSub.injective_subtype
      nuIn_range := fun u => Submodule.range_subtype _
      nuIn_jN := fun u x => GlobalTheory.Mem.eMu_ramForm (p.what₂ e W₀ n η hη) u x
      nuIn_norm := fun u v x => hXNn u v x
      jEE_norm := fun x => by
        refine Eq.trans ?_ (hX0n x)
        show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin p.nR)) X _ x = _
        simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_true] }
  refine ⟨V, ⟨⟨LinearEquiv.refl _ _, fun x => rfl, fun v hv x y => ?_⟩, fun S N G' => ?_⟩,
    fun u x => Iff.rfl, rfl, rfl, rfl, fun H u φ x => bkOf_spec (p.what₂ e W₀ n η hη) p.cR H u φ x⟩
  · show Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin p.nR)) X v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin p.nR)) p.Xo v x y
    simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, X, if_neg hv]
  · intro x
    simp only [Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_RRset]
    exact Iff.rfl

end GlobalTheory.Mem.R3.Rw

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localizationFreeStage_trueGroup_columnChoiceStep : StepW (pinAnd HasPk) fun K B f T w => ∀ (P : Pre2 K w), ∃ N : NStage B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl), IsEmpty N.nd.Loc ∧ GrpTrue N f ∧ ∀ V S G, GrpAt (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.px eR → CenIs P.q.p N eR := by
  first | exact @GlobalTheory.Mem.R3.Rw.Bare.stepW_bare | exact GlobalTheory.Mem.R3.Rw.Bare.stepW_bare | (intros; apply GlobalTheory.Mem.R3.Rw.Bare.stepW_bare <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Bare

set_option maxHeartbeats 2000000 in

theorem rows_le {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {y : Hd R.toRealDat}
    {mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G} {p : PkD D G} (t : PkT F y mA p) : (p.ch true).n ≤ p.Dall := by
  rcases Nat.eq_zero_or_pos p.Dall with h0 | hpos
  · have h := p.D_eq
    rw [h0, Nat.cast_zero, mul_zero] at h
    have h' : (p.ch true).n = 0 := by exact_mod_cast h
    omega
  · rw [t.dall] at hpos ⊢
    have hF := Module.finite_of_finrank_pos hpos
    have h1 := LinearMap.finrank_range_of_inj (t.ch true).jE_inj
    have h2 := Module.finrank_eq_card_basis (p.ch true).bs.toBasis
    rw [Fintype.card_fin] at h2
    rw [← h2, ← h1, (t.ch true).jE_range]
    have hle := Mult.goodPart_le R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0
    have hf := Submodule.finiteDimensional_of_le hle
    refine le_trans ?_ (Submodule.finrank_mono hle)
    exact Submodule.finrank_map_le (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap
      (Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0)

set_option maxHeartbeats 2000000 in

theorem frames_unit {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {y : Hd R.toRealDat}
    {mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G} {p : PkD D G} (t : PkT F y mA p) (v) : IsUnit (p.Xo v).det := by
  obtain ⟨_, -, h⟩ := t.rr
  exact (h v).2

end GlobalTheory.Mem.R3.Rw.Bare
end
