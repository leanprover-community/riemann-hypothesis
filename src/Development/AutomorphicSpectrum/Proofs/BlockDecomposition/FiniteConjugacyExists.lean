module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.CjEx

open PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjAbove {v : PlF E} (w : Above v) : Above v :=
  ⟨conjSrc (IsCMField.complexConj E).toRingEquiv w.1,
    (GlobalTheory.DefU.LocRet.under_conjSrc (E := E) w.1).trans w.2⟩

def cj (v : PlF E) : Av v →+* Av v :=
  RingHom.pi fun w => (conjLoc (IsCMField.complexConj E).toRingEquiv w.1 : _ →+* _).comp
    (Pi.evalRingHom (fun u : Above v => u.1.adicCompletion E) (conjAbove w))

theorem continuous_cj (v : PlF E) : Continuous (cj v) :=
  continuous_pi fun w => (conjLoc_spec (IsCMField.complexConj E).toRingEquiv w.1).1.comp (continuous_apply (conjAbove w))

theorem projv_conjFin (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj v (projv v x) :=
  funext fun _ => pLoc_conjFin _ _ _

end GlobalTheory.CompanionTheory.CjEx

theorem GlobalTheory.CompanionTheory.CjEx.cjEx : PositivityTheory.Rg.BcB.G8.Fin.CjEx := fun _ _ _ _ v =>
  ⟨GlobalTheory.CompanionTheory.CjEx.cj v, GlobalTheory.CompanionTheory.CjEx.continuous_cj v, GlobalTheory.CompanionTheory.CjEx.projv_conjFin v⟩

end
