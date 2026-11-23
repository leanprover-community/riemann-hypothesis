module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalRepresentationTheoryHypotheses
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalLanglandsOfHyp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsCombined
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGL
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Mem.LiteralAutomorphy
theorem localLanglandsGL_and_purity_at_member_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LocalRepresentationTheoryHypothesesAlt → _root_.GlobalTheory.Mem.LiteralAutomorphy.GlobalAutomorphicGaloisHypotheses' → _root_.UpperTheory.Zero.LLC.RecTExists ∧ _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt := by
  intro L A
  have hL : _root_.UpperTheory.Zero.LLC.RecTExists :=
    _root_.GlobalTheory.T.recTExists_of_published_inputs L.llc L.conv L.dzi L.brauer L.chev A.art L.exh L.multi L.cos L.zel L.geo L.bz
  refine ⟨hL, ?_⟩
  have hG : GlobalTheory.GLq.Green := GlobalTheory.GreenBridge.green_of_regular L.green
  exact
    { what₂ := _root_.GlobalTheory.T.published_inputs_combined_alt_alt L.bz L.bern L.geo L.disj L.mp A.js A.fin L.temp L.seg A.gk A.gal A.car
        A.pur A.coh A.art A.chA A.chW A.berger GlobalTheory.Published.chebotarevDegreeOne' hL
      decay := A.decay
      hc := A.hc
      greenC := hG
      green := hG
      zel := L.zel
      ray := A.ray
      rayF := A.ray
      rayA := GlobalTheory.Published.GlobalArtinReciprocity.rayCharacterArtin A.art
      bc := _root_.UpperTheory.BaseChangeIdentities.bridge A.bc L.bern
      gen := _root_.PositivityTheory.Gud.generic_unitary_dual_GL trivial L.sq L.gen L.multi L.cos
      std := L.cos
      cheb := GlobalTheory.Published.cheb_holds
      howe := GlobalTheory.Hk3.howeUnram_holds }
end GlobalTheory.Mem.LiteralAutomorphy
end
end
