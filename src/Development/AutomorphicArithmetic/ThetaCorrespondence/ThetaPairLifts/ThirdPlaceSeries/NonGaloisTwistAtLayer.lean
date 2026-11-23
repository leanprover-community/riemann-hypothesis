module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwJoin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeOperatorsAdelicReadingStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvLgGFieldOfSmallField
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalLocTripleWithLocalization
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonemptyTwOf
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
section
noncomputable section
namespace GlobalTheory.TwInputs.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.TwInputs.JoinModel
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


section General
variable {D : D7}
end General
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch}
  {xd : ThData (w.D Z)} {c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n}
end Rows
end GlobalTheory.TwInputs.AtLayer
namespace GlobalTheory.TwInputs.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
theorem nonempty_twOf_of_law_rx_colPin : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) → EvLgG fun K B f T => KPx B f → T = TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RX K B f T w Z Wt p0 t) → ColPin w → Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c) := by
  intro hP hS hL _
  have e1 := (evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
  have e2 := EvG.inter (_root_.GlobalTheory.T.exists_galSide_cf_eq_cgTrue_at_members hP hS hL) (_root_.GlobalTheory.TwInputs.SmallField.fieldOk_and_exists_lamDat_ok_teich_valuesIn hP)
  refine (e1.inter e2).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hV, hH⟩, hG, hF⟩ := H
  refine (hG.inter hF).imp fun B f T hO G hK _ w Z Wt p0 t nch n xd c ⟨e⟩ hR hC => ?_
  exact _root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_hecke_stable_reads (hH := (hH (w.st Z) hO).1) (hV := (hV (w.st Z) hO).1) (hs := (hV (w.st Z) hO).2) e.1
    ((G.2 hK T w Z).1 _ t.r.z.lev.C) (G.1 hK w Z Wt p0 t nch n xd c ⟨e.1⟩ hR hC) (GlobalTheory.T.exists_rationalHeckeOperators_adelicReading hP.decay hS.hkTr hS.hkRead)
end GlobalTheory.TwInputs.AtLayer
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.nonempty_twOf_of_extensionWithLaw : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) → EvLgG fun K B f T => KPx B f → T = TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RX K B f T w Z Wt p0 t) → ColPin w → Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c) := by
  first | exact @_root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_law_rx_colPin | exact _root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_law_rx_colPin | (intros; apply _root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_law_rx_colPin <;> assumption)
end
end
