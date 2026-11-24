module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfMemBadPrimes
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet

@[expose] public section



section
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.BadLog
variable {D : D7} {L : SizeData₂ D}
theorem logSum_badPrimes_le_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p _ Y _ C => logSum (badPrimes p.T.Q.H Y.d.l₂) ≤ C * zBase (Fm.L x ι) :=
  fun h => Closed.imp h fun Fm _ _ _ => ⟨2 * |Fm.CYL| + 17, by positivity, 0, fun x hx _ ι p _ i _ Y hY => by
    obtain ⟨a, b⟩ := log_level_le (Fm.params x hx ι)
    rw [Fm.params_CYL] at b
    exact (logSum_le_log a fun q hq => dvd_of_mem_badPrimes p.fw.laws.pins hY.1 hq).trans b⟩
end GlobalTheory.BadLog
end
end
