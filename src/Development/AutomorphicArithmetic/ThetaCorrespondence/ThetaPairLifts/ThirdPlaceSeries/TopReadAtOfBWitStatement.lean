import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingBundleStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColsStdOfBWit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopValueWitnessStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopValueWitness
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfVal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopValueVanishingUniformStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopValueVanishingUniform
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupReferenceTupleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupReferenceTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffTwistedClassStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffTwistedClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTruePackB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTwistedClassStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTwistedClass
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneFormExistsHeqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneFormExistsHeq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurScalarLemmaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurScalarLemma

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Col GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top GlobalTheory.TopVal
namespace GlobalTheory.TopVal
set_option maxHeartbeats 1000000 in
theorem pkVal_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → q.x.what₂.r.z.Std → ∃ cv, _root_.GlobalTheory.TopVal.ValEqvAlt (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv ∧ _root_.GlobalTheory.TopVal.PackageValuation (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv := by
  intro hL p K q c b hw hs
  obtain ⟨x, a, ax, y, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  have h0 := datVal_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a hs
  have h1 : DatVal q.w.I q.w.l q.Z (aK := x.alg) x.R.toRealDat x.Y.tup := by
    subst hx
    exact h0
  have h2 : (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => DatVal q.w.I q.w.l q.Z (aK := k.B.alg) k.B.Q.Rl.toRealDat k.P.I.tup) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := by
    rw [y.eq]
    exact h1
  obtain ⟨cv, h3, h4⟩ := h2
  exact ⟨cv, h3, h4⟩
end GlobalTheory.TopVal
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valEqv_of_bWit_std : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → q.x.what₂.r.z.Std → ∃ cv, _root_.GlobalTheory.TopVal.ValEqvAlt (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv ∧ _root_.GlobalTheory.TopVal.PackageValuation (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv := by
  atlas_forward_decl _root_.GlobalTheory.TopVal.pkVal_of_bWit_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal.Inj
open NumberField IsDedekindDomain
open scoped TensorProduct
theorem eq_zero_of_pkAt_eq_zero_uni {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : Col2.TC B X} {l : I.Laws} {Z : Col2.TC.Later B (I.cols l)}
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
    (gP : Formalism.L2.Forms.gramP (I.rec7 l Z) = 1) (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t)
    (hz : ∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → IsUni B y → _root_.GlobalTheory.TopVal.packageAtPoint W t x g = 0) : x = 0 := by
  exact eq_zero_of_hasMat (_root_.GlobalTheory.Fam.pk_z W) W.Q.charW.base.models.jX gP t x hz
set_option maxHeartbeats 1000000 in
theorem eq_zero_of_isRes_pkAt_eq_zero : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) (x : (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A.fam.amb.FR t), GlobalTheory.TopVal.IsRes φ x → (∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → GlobalTheory.TopVal.IsUni q.B y → _root_.GlobalTheory.TopVal.packageAtPoint (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) t x g = 0) → ∀ d, GlobalTheory.TopVal.val φ d = 0 := by
  intro hL p K q c b hw t φ x hx hz d
  have hx0 : x = 0 := _root_.GlobalTheory.TopVal.Inj.eq_zero_of_pkAt_eq_zero_uni (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b)
    (Col2.TC.spaces_in_coordinates q.w.I q.w.ok q.w.pins q.w.l q.Z).2.1 t x hz
  subst hx0
  obtain ⟨x, a, ax, y, -⟩ := hw
  have e : a.x = x := eq_of_heq ax
  subst e
  have h0 := eq_zero_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y →
      ∀ (s : k.P.T) (φ : Frm q.w.I (k.P.I.tup s)), IsRes φ (0 : k.P.A3.A.fam.amb.FR s) → φ = 0 := by
    intro k hk
    subst hk
    exact h0
  rw [key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq t φ hx]
  rfl
end GlobalTheory.TopVal.Inj
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pk_at_vanishing_of_is_uni : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) (x : (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A.fam.amb.FR t), GlobalTheory.TopVal.IsRes φ x → (∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → GlobalTheory.TopVal.IsUni q.B y → _root_.GlobalTheory.TopVal.packageAtPoint (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) t x g = 0) → ∀ d, GlobalTheory.TopVal.val φ d = 0 := by
  atlas_forward_decl _root_.GlobalTheory.TopVal.Inj.eq_zero_of_isRes_pkAt_eq_zero
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.BaseLevel
open NumberField IsDedekindDomain GlobalTheory.Mem.Col2 Formalism.L2.Forms GlobalTheory.SeeSaw GlobalTheory.SeeSaw.TopLevel
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
set_option maxHeartbeats 2000000 in
theorem topLev_of_btw_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) (y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x)
    {u : D.what₂.Word} (K₀ : ClsPTied u) (h : PairDataBaseTupleLevelEqualsClassLevel x K₀) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (ht : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = D.what₂.mu0) :
    GlobalTheory.Core.Rk.Top.TopLev K₀ (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t))
      (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y → ∀ t : k.P.T, k.P.I.tup t = D.what₂.mu0 →
      letI := k.B.alg
      GlobalTheory.Core.Rk.Top.TopLev K₀
        (levS _ k.B.Q.Rl.toRealDat.βX (datXP k.B.Q.Rl.toRealDat (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true) t))
        (levChi _ k.B.Q.Rl.toRealDat.βX (datXP k.B.Q.Rl.toRealDat (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true) t)) := by
    intro k hk
    subst hk
    exact h
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq t ht
set_option maxHeartbeats 2000000 in
theorem pairDataBaseTupleLevel_eq_classLevel_of_stdF {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K)
    (a : R3.TwArgs q.O.ex q.x.what₂) (v : q.B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((q.w.D q.Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (q.w.D q.Z) v Ch chOf) (hF : TC.StdF q.w.I q.w.l q.Z v F) : PairDataBaseTupleLevelEqualsClassLevel (O := q.O) a.x F.clsP := by
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F' cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  intro t ht
  have hT' : Y.tup = q.x.what₂.r.Y.tup := eq_of_heq htup
  have z := q.x.what₂.r.z.lev
  have hix : R3.ixOf q.w.I _ t = q.w.I.mu0 :=
    (q.x.what₂.r.tup_ix t).symm.trans ((congrFun hT' t).symm.trans ht)
  have hQ : q.x.what₂.r.z.R.Q t = ∅ := (z.Q t).trans ((congrArg q.w.I.Q hix).trans q.w.I.twistPrimes_reference_tuple_eq_empty)
  have hc := z.is.chi
  rw [z.C] at hc
  exact topLev_levPOf q.w.I q.w.l q.Z q.w.ok q.w.pins v F hF r_le_X q.x.what₂.r.z.R.Pg (q.x.what₂.r.z.R.Q t) q.x.what₂.r.z.R.βX
    z.Pg hQ z.beta.2 q.x.what₂.r.z.R.eG q.x.what₂.r.z.idG q.x.what₂.r.z.R.chi (q.x.what₂.r.z.R.xiR t) hc
set_option maxHeartbeats 2000000 in
theorem levG_base_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T), (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = (q.w.D q.Z).what₂.mu0 → LevG ((_root_.GlobalTheory.Fam.packB_alt b).R.T.cols.forms u).clsP.toG 1 (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  intro hL p K q c b hw u t ht
  obtain ⟨-, -, -, ⟨hC⟩, -⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hw
  have hx : hw.a.x = hw.x := eq_of_heq hw.ax
  exact (levG_one_iff _ _ _).2 (_root_.GlobalTheory.Fam.BaseLevel.topLev_of_btw_alt b hw.x hw.y _ (hx ▸ _root_.GlobalTheory.Fam.BaseLevel.pairDataBaseTupleLevel_eq_classLevel_of_stdF q hw.a u _ (hC u)) t ht)
end GlobalTheory.Fam.BaseLevel
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_group_reference_tuple_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T), (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = (q.w.D q.Z).what₂.mu0 → LevG ((_root_.GlobalTheory.Fam.packB_alt b).R.T.cols.forms u).clsP.toG 1 (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.BaseLevel.levG_base_of_bWit_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TopVal.TwSet
section Gen
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.SeeSaw.TopLevel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end Gen
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Args
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
end Args
set_option maxHeartbeats 2000000 in
theorem data_of_bWit_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (hw : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX = 1 ∧ (∀ t, (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Q t = q.w.I.Q ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) ∧
      ∀ g, g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)).H ↔ ∀ PP (h : PP ∈ (q.B.primes q.w.px).vGs) (h' : PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Pg),
        g ⟨PP, h'⟩ ∈ (GlobalTheory.Mem.Col2.TC.Ps q.w.I ⟨PP, h⟩).H := by
  have hu := _root_.GlobalTheory.MiS.Check.used_all_alt (_root_.GlobalTheory.Fam.packB_alt b)
  obtain ⟨x, a, ax, y, -, -, -, -, -, -, -, -, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  subst hx
  obtain ⟨-, -, hl, -⟩ := GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y → (∀ t, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) (k.P.I.tup t)) →
      (letI := k.B.alg
      k.B.Q.Rl.toRealDat.βX = 1 ∧ (∀ t, k.B.Q.Rl.toRealDat.Q t = q.w.I.Q (k.P.I.tup t)) ∧
      ∀ g, g ∈ (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true).H ↔
        ∀ PP (h : PP ∈ (q.B.primes q.w.px).vGs) (h' : PP ∈ k.B.Q.Rl.toRealDat.Pg),
        g ⟨PP, h'⟩ ∈ (GlobalTheory.Mem.Col2.TC.Ps q.w.I ⟨PP, h⟩).H) := by
    intro k hk
    subst hk
    intro hu
    letI := a.x.grp
    letI := a.x.fin
    letI := a.x.alg
    refine ⟨a.x.pins.keep.beta.2, fun t => ?_, fun g => ?_⟩
    · have h1 := eq_of_heq (hl _ (hu t)).1
      exact (congrArg a.x.R.Q (a.x.Y.tupT_tup t)).symm.trans h1
    · exact (by with_unfolding_all exact (lev_twArgs a g :))
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq hu
set_option maxHeartbeats 2000000 in
theorem levS_iff_cls_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X'), g ∈ (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) ↔ ∃ κ : ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1 := by
  intro hL p K q c b hw u t h g
  obtain ⟨hOk, ⟨hPins⟩, -, -, l0, tw, he, ht, -, -, s⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hw
  obtain ⟨hβ, hQ, hH⟩ := _root_.GlobalTheory.TopVal.TwSet.data_of_bWit_alt q b hw
  have hPg : (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Pg = (q.B.primes q.w.px).vGs := Finset.ext (_root_.GlobalTheory.Fam.BundleLev.levTrue_packB_of_bWit q b hw).2.1
  have key : ∀ (Tw : TwForms (q.w.D q.Z)) (t' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes (_root_.GlobalTheory.Fam.packB_alt b).R.T.n.tp (_root_.GlobalTheory.Fam.packB_alt b).R.T.cols Tw),
      Tw = GlobalTheory.Mem.Col2.TC.tw q.w.I q.w.l l0 q.Z → HEq t' tw →
      (g ∈ (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) ↔
        ∃ κ : (t'.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1) := by
    rintro _ t' rfl rfl
    exact mem_levS_of_reads q.w.I hOk hPins q.w.l q.Z _ _ (s.what₂ u _ h) _ hβ _ _ hPg (hQ t) _ hH _ _ _ g
  exact key _ _ he ht
end GlobalTheory.TopVal.TwSet
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_iff_twisted_class_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X'), g ∈ (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) ↔ ∃ κ : ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1 := by
  atlas_forward_decl _root_.GlobalTheory.TopVal.TwSet.levS_iff_cls_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TopVal.LevTw
section Gen
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
end Gen
section Cols
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.AdT Matrix GlobalTheory.EX
open Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
variable {B : Base} {X : PreX B.toPre} (I : TC B X)
end Cols
section Pack
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem levRead_packB_of_bWit {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (hw : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    LevRead q.w.I q.w.l q.Z (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).toLevCh (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup := by
  obtain ⟨x, a, ax, y, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  have h0 := levRead_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a
  have h1 : LevRead q.w.I q.w.l q.Z x.R.toLevCh (x.R.toRealDat.levR x.F.lv2 true) x.Y.tup := by
    subst hx
    exact h0
  have h2 : (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => LevRead q.w.I q.w.l q.Z k.B.Q.Rl.toRealDat.toLevCh
      (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true) k.P.I.tup) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := by
    rw [y.eq]
    exact h1
  exact h2
set_option maxHeartbeats 1000000 in
theorem levIs_of_bWit_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (hw : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T)
    (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) :
    LevIs ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev
      (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t))
      (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  have hxi : b.R.T.n.tp.xi = q.w.I.xi := (congrArg (fun s => s.2.xi) hw.recPin.s.chr).trans q.x.n.xi
  obtain ⟨l0, s, he, hs, -, -, hP⟩ := (_root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hw).2.2.2.2
  have key : ∀ (Tw : TwForms (q.w.D q.Z)) (s' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes b.R.T.n.tp b.R.T.cols Tw), Tw = TC.tw q.w.I q.w.l l0 q.Z →
      HEq s' s → LevIs (s'.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev
        (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t))
        (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
    rintro _ s' rfl rfl
    refine _root_.GlobalTheory.TopVal.LevTw.levRead_packB_of_bWit q b hw t h _ _ _ _ _ (fun v hv => hv.imp id fun hv => ?_) (s'.pt.chi_fin u _ h) (hP.what₂ u _ h)
    have h1 := (s'.ch.Q_iff _ v).1 hv
    unfold Formalism.L2.Host.TupTied.InQ' at h1
    rw [hxi] at h1
    exact underQ_of_ram q.w.ok _ v h1
  exact key _ _ he hs
theorem levChi_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X') (κ : ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U), GlobalTheory.Core.Rk.Top.HasMat g κ.1 → (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) g = star ((((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.chi κ : ℂˣ) : ℂ) :=
  fun q _ b hw u t h g κ hm => (_root_.GlobalTheory.TopVal.LevTw.levIs_of_bWit_alt q b hw u t h).2 g κ hm
end Pack
end GlobalTheory.TopVal.LevTw
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_character_twisted_class_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X') (κ : ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U), GlobalTheory.Core.Rk.Top.HasMat g κ.1 → (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) g = star ((((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.chi κ : ℂˣ) : ℂ) := by
  atlas_forward_decl _root_.GlobalTheory.TopVal.LevTw.levChi_of_bWit_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix
noncomputable section
namespace GlobalTheory.TopVal.OneForm
section Generic
variable {D : D7} {O : Obj D} {c : ℝ}
set_option maxHeartbeats 800000 in
theorem row_of_btw_alt (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) (y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T)
    (F : Fin (((_root_.GlobalTheory.Fam.packB_alt b).P.A3.side3 (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs (_root_.GlobalTheory.Fam.packB_alt b).P.Zs).nV t) → D.what₂.LL)
    (F' : Fin (((_root_.GlobalTheory.Fam.packB_alt b).Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs).Df1.nV t) → D.what₂.LL) (hF : HEq F F') :
    ∃ (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL), (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = x.Y.tup s ∧
      HEq ((_root_.GlobalTheory.Fam.packB_alt b).Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs t F') (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
      HEq ((_root_.GlobalTheory.Fam.packB_alt b).P.I.jA t ((rV0 D (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs t).mulVec F)) (x.Y.jA s v) := by
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y → ∀ (t : k.P.T)
      (F : Fin ((k.P.A3.side3 k.P.Ps k.P.ψs k.P.Zs).nV t) → D.what₂.LL)
      (F' : Fin ((k.B.Q.F.fc (k.B.Q.Rl.toCx3 k.B.Q.F).zs).Df1.nV t) → D.what₂.LL), HEq F F' →
      ∃ (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL), k.P.I.tup t = x.Y.tup s ∧
        HEq (k.B.Q.F.eV (k.B.Q.Rl.toCx3 k.B.Q.F).zs t F') (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
        HEq (k.P.I.jA t ((rV0 D k.P.A3.A k.P.Ps k.P.ψs t).mulVec F)) (x.Y.jA s v) := by
    intro k hk
    subst hk
    intro t F F' hF
    have e : F = F' := eq_of_heq hF
    subst e
    refine ⟨t, (rV0 D x.A3.A x.F.P1 x.F.ψ1 t).mulVec F, rfl, heq_of_eq ?_, HEq.rfl⟩
    have hOk := y.intersectionNumber_baseChange.ok
    have hb : BlockHyp (x.A3.A.fam.R t) (x.A3.A.fam.lvl x.F.P1 x.F.ψ1) x.A3.A.fam.v0 1 :=
      ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ t⟩
    have key := BlockDat.lf_lvl_vE hb
    unfold R3.rowForm rV0
    show (x.A3.A.fam.R t).S.basis.equivFun.symm (((x.A3.A.fam.R t).vE (x.A3.A.fam.lvl x.F.P1 x.F.ψ1)) *ᵥ F) = _
    congr 1
    conv_lhs => rw [← key]
    rw [Matrix.mul_assoc]
    exact (Matrix.mulVec_mulVec _ _ _).symm
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq t F F' hF
end Generic
section Rows
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl
end Rows
set_option maxHeartbeats 800000 in
theorem exists_frm_isRes_recVal {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) (x : R3.TwIn q.O.ex)
    (a : R3.TwArgs q.O.ex q.x.what₂) (ax : HEq a.x x) (rx : Bl.RXs q.x.what₂) (s : x.T)
    (v : Fin (rDim (q.w.D q.Z) x.A3.A x.F.P1 x.F.ψ1 s) → (q.w.D q.Z).what₂.LL) :
    ∃ φ : Frm q.w.I (x.Y.tup s), IsRes φ (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
      ∀ u, RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u (x.Y.tup s) φ (x.Y.jA s v) := by
  have e : a.x = x := eq_of_heq ax
  subst e
  obtain ⟨s', v', k1, k2, k3⟩ := row_of_args (w := q.w) (Z := q.Z) (ex := q.O.ex) (t := q.x.what₂) a s v
  exact one_form_congr (I := q.w.I) (l := q.w.l) (Z := q.Z) k1 k2 k3 (one_form_rows rx s' v')
set_option maxHeartbeats 800000 in
theorem recVal_packB_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (F : Fin (((_root_.GlobalTheory.Fam.packB_alt b).P.A3.side3 (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs (_root_.GlobalTheory.Fam.packB_alt b).P.Zs).nV t) → (q.w.D q.Z).what₂.LL) (F' : Fin (((_root_.GlobalTheory.Fam.packB_alt b).Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs).Df1.nV t) → (q.w.D q.Z).what₂.LL), HEq F F' → ∃ φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t), GlobalTheory.TopVal.IsRes φ ((_root_.GlobalTheory.Fam.packB_alt b).Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs t F') ∧ ∀ u, GlobalTheory.TopVal.RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) φ ((_root_.GlobalTheory.Fam.packB_alt b).P.I.jA t ((rV0 (q.w.D q.Z) (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs t).mulVec F)) := by
  intro hL p K q c b hb hR t F F' hF
  obtain ⟨rx⟩ := hR
  obtain ⟨s, v, h1, h2, h3⟩ := _root_.GlobalTheory.TopVal.OneForm.row_of_btw_alt b hb.x hb.y t F F' hF
  exact one_form_congr (I := q.w.I) (l := q.w.l) (Z := q.Z) h1 h2 h3 (_root_.GlobalTheory.TopVal.OneForm.exists_frm_isRes_recVal q hb.x hb.a hb.ax rx s v)
end GlobalTheory.TopVal.OneForm
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_form_exists_heq_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (F : Fin (((_root_.GlobalTheory.Fam.packB_alt b).P.A3.side3 (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs (_root_.GlobalTheory.Fam.packB_alt b).P.Zs).nV t) → (q.w.D q.Z).what₂.LL) (F' : Fin (((_root_.GlobalTheory.Fam.packB_alt b).Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs).Df1.nV t) → (q.w.D q.Z).what₂.LL), HEq F F' → ∃ φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t), GlobalTheory.TopVal.IsRes φ ((_root_.GlobalTheory.Fam.packB_alt b).Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs t F') ∧ ∀ u, GlobalTheory.TopVal.RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) φ ((_root_.GlobalTheory.Fam.packB_alt b).P.I.jA t ((rV0 (q.w.D q.Z) (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs t).mulVec F)) := by
  atlas_forward_decl _root_.GlobalTheory.TopVal.OneForm.recVal_packB_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TopVal.Scalar
section Alg
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms Matrix GlobalTheory.CoefSpace
variable {ι : Type} [Fintype ι] {n : ℕ}
end Alg
section Group
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Forms Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.DefLift GlobalTheory.CoefSpace GlobalTheory.DefiniteMult Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {θ : InfFam D} {c : CoefA V}
  {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ}
end Group
end GlobalTheory.TopVal.Scalar
end
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.TopVal.exists_jVal_smul_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws} {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), Formalism.L2.Forms.gramP (I.rec7 l Z) = 1 → ∀ (u : B.Word) (cv : GlobalTheory.TopVal.Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W), _root_.GlobalTheory.TopVal.ValEqvAlt W cv → cv ≠ 0 → ∀ j₀, GlobalTheory.Core.Rk.Top.IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j₀ → ∃ a : ℂ, a ≠ 0 ∧ _root_.GlobalTheory.TopVal.ValuationCompatible W cv (a • j₀) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u cv hcv h0 j₀ hJ
  have hm := W.Q.charW.base.models
  have hr := hJ.range
  rw [GlobalTheory.Core.Rk.Top.sgT_eq_perIn_sgT I l Z u I.mu0] at hr
  have e : (fun τ => ((GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  obtain ⟨a, ha, h⟩ := GlobalTheory.TopVal.Scalar.exists_scalar (D := I.rec7 l Z) (M := (_root_.GlobalTheory.Fam.pk_z W).MX) (θ := (_root_.GlobalTheory.Fam.pk_z W).θ) (c := (_root_.GlobalTheory.Fam.pk_z W).cX)
    (pr := (_root_.GlobalTheory.Fam.pk_z W).prX) hm.inf (GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) _) hm.cX hm.prX
    (Formalism.L2.Forms.rankP (I.rec7 l Z)) B.wts.sgTrue B.embLL B.fields.emb
    (fun τ x => DFunLike.congr_fun (B.fields_embC τ) x) cv hcv h0 _ _ _ e j₀ hJ.inj hr hJ.eqv
  refine ⟨a, ha, fun w v => (h w v).trans ?_⟩
  unfold GlobalTheory.TopVal.pairVal
  rw [LinearMap.smul_apply]
  erw [map_smul, map_smul, LinearMap.smul_apply]
  rfl
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_gram_family_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws} {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), Formalism.L2.Forms.gramP (I.rec7 l Z) = 1 → ∀ (u : B.Word) (cv : GlobalTheory.TopVal.Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W), _root_.GlobalTheory.TopVal.ValEqvAlt W cv → cv ≠ 0 → ∀ j₀, GlobalTheory.Core.Rk.Top.IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j₀ → ∃ a : ℂ, a ≠ 0 ∧ _root_.GlobalTheory.TopVal.ValuationCompatible W cv (a • j₀) := by
  atlas_forward_decl _root_.GlobalTheory.TopVal.exists_jVal_smul_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal
section True
open GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
theorem to_map_pr_x_eq_pk_at (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t) (g : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (hg : g ∈ GfC (I.rec7 l Z).sp.X')
    (v : SmT (_root_.GlobalTheory.Fam.pk_z W).MX) :
    (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t x)) v g = (_root_.GlobalTheory.Fam.pk_z W).prX (_root_.GlobalTheory.TopVal.packageAtPoint W t x g) v := by
  have h1 : (_root_.GlobalTheory.Fam.pk_z W).cX.ρ g⁻¹ = 1 := W.Q.charW.base.models.cX.1 _ (inv_mem hg)
  show (_root_.GlobalTheory.Fam.pk_z W).prX ((_root_.GlobalTheory.Fam.pk_z W).cX.ρ g⁻¹ (_root_.GlobalTheory.TopVal.packageAtPoint W t x g)) v = _
  rw [h1]
  rfl
set_option maxHeartbeats 1000000 in
theorem exists_is_j_pair_val_of_vanishing (hg : Formalism.L2.Forms.gramP (I.rec7 l Z) = 1) (u : B.Word) (cv : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) (hE : _root_.GlobalTheory.TopVal.ValEqvAlt W cv)
    (hP : _root_.GlobalTheory.TopVal.PackageValuation W cv)
    (hi : ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x →
      (∀ g y, HasMat g y → IsUni B y → _root_.GlobalTheory.TopVal.packageAtPoint W t x g = 0) → ∀ d, val φ d = 0) :
    ∃ j, IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j ∧ ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x → ∀ d v,
      (_root_.GlobalTheory.Fam.pk_z W).prX (cv (val φ d)) v = pairVal B (j v) (val φ d) := by
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.SeeSaw.exists_isJ_of_par (GlobalTheory.SeeSaw.sg_trueColumns I l Z u) (_root_.GlobalTheory.Fam.pk_z W).MX rfl
  by_cases h0 : cv = 0
  · refine ⟨j₀, hj₀, fun t φ x hx d v => ?_⟩
    have hz := hi t φ x hx (fun g y h1 h2 => (hP t φ x hx g y h1 h2).trans (by rw [h0]; rfl)) d
    rw [hz, map_zero, map_zero, LinearMap.zero_apply]
    unfold pairVal
    rw [Submodule.coe_zero, map_zero, map_zero]
  · obtain ⟨a, ha, hJ⟩ := _root_.GlobalTheory.T.unit_gram_family_property_alt W hg u cv hE h0 j₀ hj₀
    exact ⟨a • j₀, isJ_smul hj₀ ha, fun t φ x _ d v => hJ _ v⟩
set_option maxHeartbeats 1000000 in
theorem reads_pk_alt (hOk : I.Ok) (hC : I.StdC l Z W.R.T.cols) (hW : _root_.GlobalTheory.AdForm.TwStdAlt W) (u : B.Word)
    (cv : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) (hP : _root_.GlobalTheory.TopVal.PackageValuation W cv) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ))
    (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t) (hx : IsRes φ x)
    (hV : ∀ d v, (_root_.GlobalTheory.Fam.pk_z W).prX (cv (val φ d)) v = pairVal B (j v) (val φ d))
    (G : (I.rec7 l Z).what₂.Amb (W.P.I.tup t)) (hG : RecVal u (W.P.I.tup t) φ G) :
    _root_.GlobalTheory.Fam.ReadsCoefficients W u j 1 (W.P.I.tup t) G ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t x))) := by
  refine _root_.GlobalTheory.TopVal.reads_of_pairVal W hC hW u j _ φ G hG _ fun g y pt v hy hp => ?_
  refine (_root_.GlobalTheory.TopVal.to_map_pr_x_eq_pk_at W t x g hy.1 v).trans ?_
  rw [hP t φ x hx g y hy hp.uni, GlobalTheory.T.decoratedLatticeOfAdelicMatrix_eq_rowPoint I hOk _ y pt hp]
  exact hV _ v
end True
set_option maxHeartbeats 2000000 in
theorem exists_read_at_pack_b_of_b_wit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ u, ∃ j, _root_.GlobalTheory.Fam.LeadingReadAt (_root_.GlobalTheory.Fam.packB_alt b) u j 1 := by
  intro hL p K q c b hW ⟨rx⟩ u
  obtain ⟨hOk, ⟨hPins⟩, -, ⟨hC⟩, hTS⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hW
  have hg := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords q.w.I hOk hPins q.w.l q.Z).2.1
  obtain ⟨cv, hE, hP⟩ := _root_.GlobalTheory.T.exists_valEqv_of_bWit_std q b hW rx.std
  obtain ⟨j, hJ, hV⟩ := _root_.GlobalTheory.TopVal.exists_is_j_pair_val_of_vanishing (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) hg u cv hE hP (_root_.GlobalTheory.T.pk_at_vanishing_of_is_uni q b hW)
  refine ⟨j, hJ, one_mem _, fun t => ⟨⟨fun h => _root_.GlobalTheory.T.level_group_reference_tuple_alt q b hW u t h,
    fun h => levG_one _ (_root_.GlobalTheory.T.mem_level_iff_twisted_class_alt q b hW u t h) (_root_.GlobalTheory.T.level_character_twisted_class_alt q b hW u t h)⟩, fun F F' hF => ?_⟩⟩
  obtain ⟨φ, hφ, hR⟩ := _root_.GlobalTheory.T.one_form_exists_heq_alt q b hW ⟨rx⟩ t F F' hF
  exact _root_.GlobalTheory.TopVal.reads_pk_alt (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) hOk hC hTS u cv hP j t φ _ hφ (hV t φ _ hφ) _ (hR u)
end GlobalTheory.TopVal
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_read_at_packB_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ u, ∃ j, _root_.GlobalTheory.Fam.LeadingReadAt (_root_.GlobalTheory.Fam.packB_alt b) u j 1 := by
  atlas_forward_decl _root_.GlobalTheory.TopVal.exists_read_at_pack_b_of_b_wit
end
end
