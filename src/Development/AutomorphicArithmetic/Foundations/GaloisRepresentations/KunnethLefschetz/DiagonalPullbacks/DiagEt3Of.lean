module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.UntwZero
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.CupOneRight
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.FirstChernClassIsBaseChange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PClear
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PDiagSq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PGeoPB
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PPBLim
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PPBQOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PPowRoot
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PRootNat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProperOfProjOver
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowBC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.EtaleChart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.LineUnitCm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PRingL
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

namespace UpperTheory.Gal.KunnethLefschetz.Di

theorem steps : Steps :=
  ⟨ringL_holds, geoPB_holds, geoM_holds, first_chern_class_isBaseChange, rootNat_holds, powRoot_holds, untw_holds, pBLim_holds, pBQOf_holds,
    diagSq_holds, clear_holds, G.blowBC, G.blowE, G.pBE⟩

theorem diagEt2_of (hI : In) (hQ : QDiag) : CrystallineSemistableComparison.Onto.DiagEt2 := steps.diagEt2 hI hQ

theorem diagEt3_of (hI : In) (hQ : QDiag) : CrystallineSemistableComparison.Onto.DiagEt3 := CrystallineSemistableComparison.Onto.diagEt3_of (diagEt2_of hI hQ)

end UpperTheory.Gal.KunnethLefschetz.Di
