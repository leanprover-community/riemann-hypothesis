module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Formalism.LocalToGlobal.IndefiniteReal.IsFDiagIffDiagonal
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsRowOfEigensystemIndexGoodCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodGenericRowsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MjReadRealizationEqual
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScalRowsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3.RecInAt

private theorem tupTied_xi_eq {D : D7} {nch : NChoice D} {c₁ c₂ : CharFrame D}
    {t₁ : TupTied D c₁ nch} {t₂ : TupTied D c₂ nch} (hc : c₁ = c₂) (ht : HEq t₁ t₂) :
    t₁.xi = t₂.xi := by
  cases hc
  exact congrArg (fun t : TupTied D c₁ nch => t.xi) (eq_of_heq ht)

theorem recIn_parts_exists_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R (sS.toRealSpectralMatching R)), ∃ r : _root_.GlobalTheory.Mem.R3.RecursiveInput y, (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r).PartsRow := by
  intro hGC hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM R hR sP sS hP hS a x hax
  obtain rfl := eq_of_heq hax
  intro y
  have hlev := GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z q.x.Wt
    q.O.L q.O.gatT q.O.Gx q.O.Gy q.O.K q.O.X q.O.cX q.O.ex q.x.what₂ a
  have hmt := _root_.GlobalTheory.Mem.R3.Reads.mt_mj_read_alt
    (q.w.D q.Z) q.O.L q.O.gatT q.O.Gx q.O.Gy q.O.K q.O.X q.O.cX
    q.O.ex a.x R (sS.toRealSpectralMatching R) y a.intersectionNumber_baseChange
  have hFr : Top.Fr.at (q.w.st q.Z) q.f = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z :=
    (congrArg (Top.Fr.at (q.w.st q.Z)) q.w.C_eq.symm).trans rfl
  have hchr := Sigma.mk.inj_iff.1 hR.s.chr
  have hC : R.T.n.cf = a.x.R.C := hchr.1.trans (hFr.symm.trans (eq_of_heq hlev.1).symm)
  let tp := cast (congrArg (fun c => TupTied (q.w.D q.Z) c q.O.ex.nch) hC) R.T.n.tp
  have htp : HEq tp R.T.n.tp := cast_heq _ _
  have hxi : tp.xi = q.w.I.xi :=
    (tupTied_xi_eq hC.symm htp).trans ((tupTied_xi_eq hchr.1 hchr.2).trans q.x.n.xi)
  have hgen := _root_.GlobalTheory.T.geometric_parameter_of_reciprocity_alt
    hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM a
  have hlam := _root_.GlobalTheory.T.parameter_of_discrete_series_reciprocity_alt
    hGC hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM a
  have heig := @GlobalTheory.T.partsRow_of_eigensystemIndex_goodCharacters
    hW hDS hHC hCR (q.w.D q.Z) a.x.G a.x.grp a.x.fin a.x.Pl0 a.x.I0 a.x.T a.x.A3
    a.x.core.Q.c.F inferInstance inferInstance a.x.alg
    a.x.R a.x.F a.x.cG q.O.ex.p0 a.x.Y a.x.Z q.O.X a.x.pins a.intersectionNumber_baseChange
    (hH (q.w.st q.Z) q.x.isOver).1 hgen hlam
  refine heig.elim fun E hE => hE.elim fun labPi hLab => hLab.elim fun piOf hparts => ?_
  let r : RecursiveInput y := {
    E := E
    labPi := labPi
    piOf := piOf
    Tp := tp
    tpEq := htp
    tupXi := fun μ hμ => (eq_of_heq (hlev.2.2.1 μ hμ).2).trans (congrFun hxi.symm μ)
    mtRead := hmt.1
    mjRead := hmt.2 }
  exact ⟨r, hparts⟩
end GlobalTheory.Mem.R3.RecInAt
end
end
