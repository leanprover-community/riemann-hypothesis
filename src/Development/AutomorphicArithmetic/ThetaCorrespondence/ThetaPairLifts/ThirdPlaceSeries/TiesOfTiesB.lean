module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PathCoreConditionsOfParametersFreeConditionsStatement
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
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
theorem ties_of_tiesB_alt : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c), TiesB D O c b →
    GlobalTheory.FinalJoin2.FieldSmall D O.L → b.RealisedCondition → GlobalTheory.EX.DQ.TwAllAt D O.ex.nch O.ex.xd → b.CompatibilityConditions := by
  intro D O c b h hF hR htw
  obtain ⟨hc, hpb, -, hL, hD⟩ := GlobalTheory.T.pathCoreConditions_of_intrinsicConditions D O c b h hF
  obtain ⟨hT, hRay⟩ := h
  exact
    { real := hR, core := hc, pb := hpb, types := hT.types, series := hT.series, level := hL, data := hD,
      psiVal := hT.psiVal, ray := hT.small.ray, roots := hT.small.roots, rayQ := hRay, twist := htw }
end GlobalTheory.PlugPt
end
