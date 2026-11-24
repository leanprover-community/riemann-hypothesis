module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStOfFrames
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

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.model_statement_of_crystalline_chebotarev_frame_gal : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.ChebotarevDegreeOne → _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.ExpTie.FrameStatement' → _root_.GlobalTheory.ExpTie.GaloisStatement → _root_.GlobalTheory.ExpTie.ModelStatement := by
  first | exact @_root_.GlobalTheory.ExpModel.modelSt_of_small_frame_gal | exact _root_.GlobalTheory.ExpModel.modelSt_of_small_frame_gal | (intros; apply _root_.GlobalTheory.ExpModel.modelSt_of_small_frame_gal <;> assumption)
end
