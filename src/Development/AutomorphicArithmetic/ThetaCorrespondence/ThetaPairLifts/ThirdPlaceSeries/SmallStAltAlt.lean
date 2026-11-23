module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallStatement
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
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
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
namespace GlobalTheory.ExpTie
theorem smallSt_alt : _root_.GlobalTheory.ExpTie.SmallnessCondition := by
  unfold _root_.GlobalTheory.ExpTie.SmallnessCondition _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt
  refine Formalism.MainNotions.Closed.of_all fun Fm CH => ?_
  refine _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p hR _ => ?_
  intro j P W hD hN w _ hWR
  have hC := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hR.ok hR.sep p.charW hR.prim
  have hst := DefFam3.toSub2_stable hC.stable
  have hin := DefFam3.toSub2_inBlock hR.prim.block
  refine ⟨Formalism.EigenvalueLevelCeiling.plc_prime w, ?_, ?_, fun k => DefFam.stable_lifts hst j _ k, DefFam.inBlock_lifts hin j _⟩
  · exact (Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsLargePrime_holds P hN.1 hN.2.1 _ hWR.1).2.2.2.2.2.1
  · refine not_dvd_discr_host _ (Formalism.EigenvalueLevelCeiling.plc_prime w) ?_
    rw [← hD.special]
    exact hWR.2.2.2
end GlobalTheory.ExpTie
end
