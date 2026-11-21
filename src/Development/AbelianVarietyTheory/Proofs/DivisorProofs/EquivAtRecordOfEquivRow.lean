import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.ProjectiveLattices.FnDefC
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelEquivCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.FieldBC GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ}

theorem isBC_rulBC {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    IsBC hle (rulBC hle f) (fun _ : Fin 1 => (1 : c'.F)) (fun _ => f) := by
  intro S _ _ _ h y
  rw [((GlobalTheory.T.ruleBaseChange_section_values_semilinear E H Dw l Xo c c' hle).1 a n f hf).2 S h y]
  simp

theorem mem_cusp_of_isBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {a : (E →+* ℂ) × ℕ → ℕ} {n m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (hf' : f' ∈ sec Xo c' a n) (hfs : ∀ i, fs i ∈ cusp Xo c U a n)
    (h : IsBC hle f' as fs) : f' ∈ cusp Xo c' (unfBC hle U) a n := by
  rw [mem_cusp]
  refine ⟨hf', fun σ' hσ' => ?_⟩
  rw [rdU_unfBC hle U σ' h, laU_unfBC]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (((mem_cusp _ _ _ _ _ _).1 (hfs i)).2 _ hσ')

theorem mem_cusp_of_isBC_one (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f' : Rul Xo c'}
    {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (hf' : f' ∈ cusp Xo c' (unfBC hle U) a n)
    (h : IsBC hle f' (fun _ : Fin 1 => (1 : c'.F)) (fun _ => f)) : f ∈ cusp Xo c U a n := by
  rw [mem_cusp] at hf' ⊢
  refine ⟨hf, fun σ hσ => ?_⟩
  obtain ⟨σ', rfl⟩ := exists_emb_ext hle σ
  have := hf'.2 σ' (goodEmb_ext hle hσ rfl)
  rw [rdU_unfBC hle U σ' h, laU_unfBC, Fin.sum_univ_one, map_one, one_smul] at this
  exact this

end Field

section Action

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ} {G : Type} [Group G]
  {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}

theorem actLev_mem_sec (hL : ActLev (Xo := Xo) c lev) (g : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) : actLev c lev g f ∈ sec Xo c a n :=
  actL_mem _ _ _ _ hL.total hL.nat hL.bor _ g hf

theorem keeps_iff (hL : ActLev (Xo := Xo) c lev) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (g : G)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    (∀ f ∈ cusp Xo c U a n, actLev c lev g f ∈ cusp Xo c U a n) ↔
      ∀ f' ∈ cusp Xo c' (unfBC hle U) a n, actLev c' lev g f' ∈ cusp Xo c' (unfBC hle U) a n := by
  obtain ⟨hL', hB⟩ := actLev_and_actBC D H Dw l Xo c c' hle G lev hL
  constructor
  · intro h f' hf'
    obtain ⟨m, as, fs, hfs, hBC⟩ := GlobalTheory.SecFieldChange.cuspBC_holds hle U a n f' hf'
    exact mem_cusp_of_isBC hle U (actLev_mem_sec hL' g hf'.1) (fun i => h _ (hfs i))
      (hB a n g m as fs f' hf'.1 (fun i => (hfs i).1) hBC)
  · intro h f hf
    have h1 := ((rulBC_cusp _ H Dw l Xo c c' hle r U a n f hf.1).2).2 hf
    exact mem_cusp_of_isBC_one hle U (actLev_mem_sec hL g hf.1) (h _ h1)
      (hB a n g 1 _ _ _ h1.1 (fun _ => hf.1) (isBC_rulBC hle hf.1))

theorem reading_iff (hL : ActLev (Xo := Xo) c lev) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (g : G)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (Φ Ψ : FDSec (U (σ'.comp (incF c c' hle))).X →ₗ[ℂ] ℂ) :
    (∀ f ∈ cusp Xo c U a n, Φ (rdU (U _) (actLev c lev g f)) = Ψ (rdU (U _) f)) ↔
      ∀ f' ∈ cusp Xo c' (unfBC hle U) a n,
        Φ (rdU (unfBC hle U σ') (actLev c' lev g f')) = Ψ (rdU (unfBC hle U σ') f') := by
  obtain ⟨hL', hB⟩ := actLev_and_actBC D H Dw l Xo c c' hle G lev hL
  constructor
  · intro h f' hf'
    obtain ⟨m, as, fs, hfs, hBC⟩ := GlobalTheory.SecFieldChange.cuspBC_holds hle U a n f' hf'
    rw [rdU_unfBC hle U σ' hBC, rdU_unfBC hle U σ' (hB a n g m as fs f' hf'.1 (fun i => (hfs i).1) hBC), map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, h _ (hfs i)]
  · intro h f hf
    have h1 := ((rulBC_cusp _ H Dw l Xo c c' hle r U a n f hf.1).2).2 hf
    have h2 := h _ h1
    have hBC := isBC_rulBC hle hf.1
    rw [rdU_unfBC hle U σ' hBC, rdU_unfBC hle U σ' (hB a n g 1 _ _ _ h1.1 (fun _ => hf.1) hBC), Fin.sum_univ_one,
      Fin.sum_univ_one, map_one, one_smul, one_smul] at h2
    exact h2

theorem levR_iff (hA : l.A = 1) {g g' : (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)} (h : g.1 = g'.1)
    {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) : levR g y y' ↔ levR g' y y' := by
  have h1 : ∀ a, Xo.univ.etaA (g.2 a) = Xo.univ.etaA (g'.2 a) := fun a => by
    have e := Xo.univ.etaA_ker (g.2 a)
    have e' := Xo.univ.etaA_ker (g'.2 a)
    rw [hA, one_smul] at e e'
    exact e.trans e'.symm
  unfold levR IsLevMove
  simp only [h, h1]

theorem levActR_eq (hA : l.A = 1) {lev' : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (h : ∀ g, (lev g).1 = (lev' g).1) :
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g y y') =
      fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev' g y y' := by
  funext S _ _ g y y'
  exact propext (levR_iff hA (h g) y y')

theorem actLev_congr (hA : l.A = 1) {lev' : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (h : ∀ g, (lev g).1 = (lev' g).1) : actLev (Xo := Xo) c lev = actLev c lev' := by
  funext g
  unfold actLev
  rw [levActR_eq hA h]

theorem actLaws_congr (hA : l.A = 1) {lev' : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (h : ∀ g, (lev g).1 = (lev' g).1) : ActLev (Xo := Xo) c lev ↔ ActLev (Xo := Xo) c lev' := by
  unfold ActLev
  rw [levActR_eq hA h]

end Action

section Weights

variable {D : D7}


def wtOf (j : ℕ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (ha : Dom a n) : WeightFamilies.Wt D j where
  aP t i := a (DV.tauEmb D t, i)
  aM t i := a (ComplexEmbedding.conjugate (DV.tauEmb D t), i)
  aPlus_antitone _ _ _ hik := ha.1 _ hik
  aM_anti _ _ _ hik := ha.1 _ hik
  n := n
  n_even := ha.2


end Weights

section Compare

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} {i : Fin D.R.m}

theorem inR (i : Fin D.R.m) : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

section Second

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Y : RowDat T G i) (R : RealDat D A Ks)

def ClauseBig (cc : Y.U.Comp → ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ g : G, ∀ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) Y.c' Y.U' a n, Y.act' g f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) Y.c' Y.U' a n ∧
    ∀ κ, IsLift R i g κ → ∀ x, Y.phi cc (Y.act' g f) x = chiDetW R i g * Y.phi cc f (x * κ)

def phiSmall (cc : Y.U.Comp → ℂ) (f : T.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  adel (Wc D i) Y.dict (muPin (Wc D i) Y.dict Y.mu cc) (rdU Y.U f)

def ClauseSmall (cc : Y.U.Comp → ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ g : G, ∀ f ∈ T.cuspA ((i : ℕ) + 1) a n, actLev T.Q.c Y.lev g f ∈ T.cuspA ((i : ℕ) + 1) a n ∧
    ∀ κ, IsLift R i g κ → ∀ x, phiSmall Y cc (actLev T.Q.c Y.lev g f) x = chiDetW R i g * phiSmall Y cc f (x * κ)




end Second

variable [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {Tp : Type} {tup : Tp → T0}

def Match (O : OMDat T.toCore R i Tp tup) (Y : RowDat T G i) : Prop := ∀ g, (Y.lev g).1 = O.lev g

def rowOf (O : OMDat T.toCore R i Tp tup) : RowDat T G i where
  c' := O.c'
  hle := O.hle
  lev := O.lev2
  hV := O.hV


def bigCoeff {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} (c : Coeff l) : Coeff l where
  F := c.F ⊔ D.what₂.embLL.toRatAlgHom.fieldRange
  fin := by
    haveI := c.fin
    haveI : FiniteDimensional ℚ D.what₂.embLL.toRatAlgHom.fieldRange :=
      (AlgEquiv.ofInjectiveField D.what₂.embLL.toRatAlgHom).toLinearEquiv.finiteDimensional
    infer_instance
  conj τ a := (le_sup_left : c.F ≤ _) (c.conj τ a)
  zeta_mem := (le_sup_left : c.F ≤ _) c.zeta_mem
  le := c.le.trans le_sup_left

variable (R) in

def omOf (Y : RowDat T G i) : OMDat T.toCore R i Empty Empty.elim where
  c' := bigCoeff Y.c'
  hle := Y.hle.trans le_sup_left
  jL := D.what₂.embLL.codRestrict (bigCoeff Y.c').F fun x =>
    (le_sup_right : D.what₂.embLL.toRatAlgHom.fieldRange ≤ _) ⟨x, rfl⟩
  hV := Y.hV
  c0' := 0
  lev g := (Y.lev g).1
  dδ t := t.elim
  Cl' t := t.elim
  fCl t := t.elim
  bad t := t.elim
  Lh t := t.elim
  La t := t.elim
  Nc t := t.elim
  gam t := t.elim
  vol t := t.elim
  ep t := t.elim
  B t := t.elim
  epF t := t.elim
  io := 0
  hw := 0
  φ t := t.elim
  w t := t.elim
  U₂ t := t.elim
  dict₂ t := t.elim
  xi t := t.elim
  thAd t := t.elim
  Plc t := t.elim


variable {O : OMDat T.toCore R i Tp tup} {Y : RowDat T G i}

theorem phi_eq (cc : Y.U.Comp → ℂ) (f : T.R ((i : ℕ) + 1)) : O.phi cc f = phiSmall Y cc f := rfl




variable (O) in

def TiesFirst (F : Face D A) : Prop :=
  LawsJ T ∧ R.Char F ∧ VStd D i ∧ T.chiW ((i : ℕ) + 1) T.σ₀ = R.mu0 ((i : ℕ) + 1) ∧
    IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) ∧ T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧
    LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) O.lev ∧ ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c O.lev2





end Compare

def RowFirst : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0)
    (O : OMDat T.toCore R i Tp tup), TiesFirst O F →
      ∃ cc, CUnit cc ∧ ∀ κ : WeightFamilies.Wt D ((i : ℕ) + 1), κ.n = (Vc D i).rank → O.EquivAt κ cc

def RowFirstFrame : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0)
    (O : OMDat T.toCore R i Tp tup), TiesFirst O F →
      ∃ cc, CUnit cc ∧ (rowOf O).FrameConst R cc ∧ ∀ κ : WeightFamilies.Wt D ((i : ℕ) + 1), κ.n = (Vc D i).rank → O.EquivAt κ cc

def RowSecond : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (i : Fin D.R.m) (Y : RowDat T G i),
    Y.Ties R F → Y.EquivAt R

def RowSecondFrame : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (i : Fin D.R.m) (Y : RowDat T G i),
    Y.Ties R F → Y.EquivFrameAt R







end GlobalTheory.LevelEquivCompare
