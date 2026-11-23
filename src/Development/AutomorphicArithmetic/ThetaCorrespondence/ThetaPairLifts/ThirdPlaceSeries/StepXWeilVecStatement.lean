module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepXWeilVec
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.base_chain_top_weil_datum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), IsWeilDatumO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V ((_root_.GlobalTheory.BaseChain.com_z W).chS (j + 1 + 1)) ((_root_.GlobalTheory.BaseChain.com_z W).chT (j + 1 + 1)) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω ∧ ∃ ξ f₀, IsStepVecOf (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M) (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).M) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).β (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).L ((_root_.GlobalTheory.BaseChain.com_z W).chi (j + 1 + 1)) ∅ ξ f₀ (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).f := by
  first | exact @_root_.GlobalTheory.BaseChain.stepX_weil_vec_alt | exact _root_.GlobalTheory.BaseChain.stepX_weil_vec_alt | (intros; apply _root_.GlobalTheory.BaseChain.stepX_weil_vec_alt <;> assumption)
end
