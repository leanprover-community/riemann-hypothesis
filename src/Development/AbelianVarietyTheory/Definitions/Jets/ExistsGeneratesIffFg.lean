module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PlusRec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

abbrev NormDatum (B : WeightFamilies.Prov D) := GlobalTheory.RunIn.SecNorm B

def NormDatum.sup (B : WeightFamilies.Prov D) : NormDatum B := GlobalTheory.RunIn.SecNorm.sup B
namespace NormDatum
variable (n : NormDatum B)

abbrev B' : WeightFamilies.Prov D := GlobalTheory.RunIn.SecNorm.base n

abbrev X' (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) : PJ D n.B' P j := xplusN n.N n.h0 n.h1 n.h2 n.h3 n.h4 X E hM

end NormDatum

end GlobalTheory.PlusRec
