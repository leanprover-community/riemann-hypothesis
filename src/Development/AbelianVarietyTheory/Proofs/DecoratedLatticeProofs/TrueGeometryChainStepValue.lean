import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndex
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinColTOfPinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToBlocksMulFinZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryStepRelationStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.PenVol

section Gen

open ValuativeRel

variable {k n : Type} [Field k] [ValuativeRel k] [Fintype n] [DecidableEq n]

theorem mulVec_mem_box_of_int (A : Matrix n n k) (hA : ∀ i j, valuation k (A i j) ≤ 1) {c : kˣ} {y : n → k}
    (hy : y ∈ GlobalTheory.StepData.box n c) : A *ᵥ y ∈ GlobalTheory.StepData.box n c := by
  intro i
  show valuation k ((A *ᵥ y) i) ≤ valuation k (c : k)
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  calc valuation k (A i j) * valuation k (y j) ≤ 1 * valuation k (c : k) := mul_le_mul' (hA i j) (hy j)
    _ = valuation k (c : k) := one_mul _

theorem val_le_one_of_mem_KO {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (i j : n ⊕ Fin 0) :
    valuation k (g.val i j) ≤ 1 := by
  obtain ⟨h, rfl⟩ := hg
  exact (h.val i j).2

theorem toBlocks₁₁_mulVec_mem_box {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) {c : kˣ}
    {y : n → k} (hy : y ∈ GlobalTheory.StepData.box n c) : g.val.toBlocks₁₁ *ᵥ y ∈ GlobalTheory.StepData.box n c :=
  mulVec_mem_box_of_int _ (fun i j => val_le_one_of_mem_KO hg (Sum.inl i) (Sum.inl j)) hy

def boxQ {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ) :
    ((n → k) ⧸ GlobalTheory.StepData.box n c) →ₗ[𝒪[k]] ((n → k) ⧸ GlobalTheory.StepData.box n c) :=
  Submodule.mapQ _ _ ((Matrix.mulVecLin g.val.toBlocks₁₁).restrictScalars 𝒪[k])
    (fun _ hy => toBlocks₁₁_mulVec_mem_box hg hy)

theorem boxQ_mk {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ) (y : n → k) :
    boxQ hg c (Submodule.Quotient.mk y) = Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) := rfl

def boxAct (J : Subgroup (GL (n ⊕ Fin 0) k)) (hJ : J ≤ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ) :
    MulAction J ((n → k) ⧸ GlobalTheory.StepData.box n c) where
  smul g q := boxQ (hJ g.2) c q
  one_smul q := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show boxQ _ c _ = _
    rw [boxQ_mk, show ((1 : J) : GL (n ⊕ Fin 0) k).val = 1 from rfl, toBlocks_one_fin_zero, Matrix.one_mulVec]
  mul_smul g h q := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show boxQ _ c _ = boxQ _ c (boxQ _ c _)
    rw [boxQ_mk, boxQ_mk, boxQ_mk, show ((g * h : J) : GL (n ⊕ Fin 0) k).val = g.val.val * h.val.val from rfl,
      toBlocks_mul_fin_zero, Matrix.mulVec_mulVec]

theorem relIndex_cosStab_box (J : Subgroup (GL (n ⊕ Fin 0) k)) (hJ : J ≤ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ)
    (x : (n → k) ⧸ GlobalTheory.StepData.box n c) :
    (cosStab J (GlobalTheory.StepData.box n c) x).relIndex J = Nat.card {yb | GlobalTheory.QPl.SameOrb J (GlobalTheory.StepData.box n c) x yb} := by
  letI := boxAct J hJ c
  have smk : ∀ (g : J) (y : n → k), g • (Submodule.Quotient.mk y : (n → k) ⧸ GlobalTheory.StepData.box n c) =
      Submodule.Quotient.mk (g.val.val.toBlocks₁₁ *ᵥ y) := fun _ _ => rfl
  have hst : (cosStab J (GlobalTheory.StepData.box n c) x).subgroupOf J = MulAction.stabilizer J x := by
    ext g
    rw [Subgroup.mem_subgroupOf, mem_cosStab, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [smk]
      exact (h y).2 rfl
    · intro h
      refine ⟨g.2, fun y => ?_⟩
      rw [← smk]
      constructor
      · intro h'
        rw [← h] at h'
        exact smul_left_cancel g h'
      · intro h'
        rw [h', h]
  have horb : MulAction.orbit J x = {yb | GlobalTheory.QPl.SameOrb J (GlobalTheory.StepData.box n c) x yb} := by
    ext yb
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq, GlobalTheory.QPl.SameOrb]
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact ⟨g.1, g.2, y, rfl, (smk g y).symm⟩
    · rintro ⟨g, hg, y, rfl, h⟩
      exact ⟨⟨g, hg⟩, by rw [smk]; exact h⟩
  rw [Subgroup.relIndex, hst, MulAction.index_stabilizer, horb, Nat.card_coe_set_eq]

end Gen

end GlobalTheory.PenVol

end

namespace GlobalTheory.PenVol

theorem relIndex_cosStab_eq_wt {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E}
    (G : QGeo v B PP) {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) (y : E.Ch (G.s + 1)) :
    (((GlobalTheory.PenVol.cosStab ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (GlobalTheory.StepData.box _ (G.ϖ ^ E.M)) (E.cos y)).relIndex
      (GlobalTheory.SplitWeil.KO G.k _) : ℕ) : ℂ) = E.wt (G.s + 1) y := by
  have hJ := E.le (G.s + 1) 0 rfl
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (cosStab_le _ _ _) hJ, relIndex_cosStab_box _ hJ, E.wt_pen y,
    E.idx_mid (G.s + 1) 0 rfl]
  push_cast
  ring

end GlobalTheory.PenVol
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_couplingCosetStabilizer_eq_chartWeight : ∀ {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : QGeo v B PP) {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) (y : E.Ch (G.s + 1)), (((GlobalTheory.PenVol.cosStab ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (GlobalTheory.StepData.box _ (G.ϖ ^ E.M)) (E.cos y)).relIndex (GlobalTheory.SplitWeil.KO G.k _) : ℕ) : ℂ) = E.wt (G.s + 1) y := by
  atlas_forward_decl GlobalTheory.PenVol.relIndex_cosStab_eq_wt
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PenVol

theorem relIndex_ne_zero_of_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K U U0 : Subgroup G)
    (hU0 : U0 ≤ K) (hc : IsCompact (U0 : Set G)) (ho : IsOpen ((U.subgroupOf K : Subgroup K) : Set K)) :
    U.relIndex U0 ≠ 0 := by
  haveI : CompactSpace U0 := isCompact_iff_compactSpace.1 hc
  have hcont : Continuous (fun x : U0 => (⟨x.1, hU0 x.2⟩ : K)) := Continuous.subtype_mk continuous_subtype_val _
  have ho' : IsOpen ((U.subgroupOf U0 : Subgroup U0) : Set U0) := ho.preimage hcont
  haveI : Finite (U0 ⧸ U.subgroupOf U0) := (U.subgroupOf U0).quotient_finite_of_isOpen ho'
  haveI : (U.subgroupOf U0).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.FiniteIndex.index_ne_zero

theorem wt_cast (C : ℕ → Type) (w : ∀ j, C j → ℂ) {j j' : ℕ} (h : j = j') (x : C j) :
    w j' (cast (congrArg C h) x) = w j x := by
  subst h; rfl

end GlobalTheory.PenVol

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.PenVol.pen_vol : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j, j + 1 = B.R.m → ∃ v : ℂ, v ≠ 0 ∧ ∀ t (J : QJ a t), J.Reads → ∀ α, (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj
  obtain ⟨U0, hU0le, hU0c, hU0⟩ := GlobalTheory.T.true_geometry_step_relation W hW u a ha haT j hj
  have hI : I.Ok := hW.tr.ok
  have hP : TC.Pins B X := hW.tr.pins.some
  have hjm : j ≤ B.R.m := by omega
  have key : ∀ t (J : QJ a t), J.Reads → ∀ α,
      GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) * ((J.A.U j (J.ι j α)).relIndex U0 : ℝ) =
        GlobalTheory.SeeSaw.volLev (a.g.x j).vol U0 ∧
      ((J.A.U j (J.ι j α)).relIndex U0 : ℂ) = J.wt j α ∧
      GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) ≠ 0 ∧ (J.A.U j (J.ι j α)).relIndex U0 ≠ 0 := by
    intro t J hR α
    obtain ⟨hle, hidx⟩ := hU0 t J hR α
    have hrep := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hP l Z u (W.P.I.tup t) J.Ch₀ J.A hR.is j hjm (J.ι j α)).1
    refine ⟨GlobalTheory.T.archimedeanLevelVolume_mul_relIndex (I.rec7 l Z) ((I.rec7 l Z).sp.X j) (a.g.x j).vol _ _ hle hU0le hU0c hrep.opn, ?_,
      GlobalTheory.AdForm.PinInhab.volLev_ne_zero hI haT.pinX.inf j (a.g.x j).vol (J.ι j α) hrep,
      GlobalTheory.PenVol.relIndex_ne_zero_of_open (GfC _) _ _ hU0le hU0c hrep.opn⟩
    rw [hidx, Nat.cast_prod, QJ.wt]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [GlobalTheory.T.relIndex_couplingCosetStabilizer_eq_chartWeight (J.G i) (J.E i)]
    exact GlobalTheory.PenVol.wt_cast _ (J.E i).wt (by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega) (α i)
  by_cases hex : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j)
  · obtain ⟨t0, J0, hR0, ⟨α0⟩⟩ := hex
    obtain ⟨h1, -, h3, h4⟩ := key t0 J0 hR0 α0
    refine ⟨(GlobalTheory.SeeSaw.volLev (a.g.x j).vol U0 : ℂ), ?_, fun t J hR α => ?_⟩
    · rw [← h1]; exact_mod_cast mul_ne_zero h3 (Nat.cast_ne_zero.2 h4)
    · obtain ⟨e1, e2, -, -⟩ := key t J hR α
      rw [← e2, ← e1]; push_cast; ring
  · exact ⟨1, one_ne_zero, fun t J hR α => absurd ⟨t, J, hR, ⟨α⟩⟩ hex⟩

end
end
