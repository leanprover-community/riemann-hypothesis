module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfEtSide
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HodgeTateSpectral.HTSpecGood
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HtBijOfParts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.SpecOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.SqCore
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.FinalC
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HodgeTateComparisonSmoothProjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HtBijOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace UpperTheory.Gal.Seam.HT

open UpperTheory.Gal.Seam

open CrystallineSemistableComparison UpperTheory.Gal.KunnethLefschetz

theorem etSideS : EtSideS := fun l _ K _ => Top.etSide_sm_holds l K

theorem hodgeTate_comparison_smooth_projective : CrystallineSemistableComparison.HT.HodgeTateMapExists := CrystallineSemistableComparison.HT.hodgeTate_of_etale_side etSideS

theorem htBij : Onto.HTBij := Onto.htBij_of hodgeTate_comparison_smooth_projective G.sqEx3 Top.diagEt3_holds Top.etFin_holds

theorem htSpecGood : HTSpecB.HTSpecGood := Spec.htSpecGood_of htBij CrystallineSemistableComparison.Om.Nt2F.hodge_iso_natural_cech Top.etFin_holds

end UpperTheory.Gal.Seam.HT
