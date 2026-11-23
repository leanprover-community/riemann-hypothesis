module

public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.ConeIntegralFactorisation
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FinStmt
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PureIte
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ConeFactorisationOfCodimensionTwo
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FinSpan
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FubMain
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.IdealId0
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.KAtCompact
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ExtendByZeroOnSubsetApplyCoe

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF

theorem vacShift_of (h : FinCone2) : VacShift := fun F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev a b v =>
  (h F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev a b v).1

theorem finM_of (h : FinCone2) : FinM := fun F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev a b v =>
  (h F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev a b v).2.2

theorem coneFac_all (hA : ActsEx) (hSt : StabEx) (hO : ArchOp) (hU : ArchUniq) (hPS : PositivityTheory.Mix.PureSt) (hAr : ArchCone) (v : VacFixX) :
    PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation ∧ ConeFacA ∧ ConeFacB := by
  have f := Fin.finCone2_of ideleFub Id.idealId0 hSt
  have p := pureFac_of hA hO hU v (vacShift_of f) hPS
  have a := coneIntegralFactorisation_of hA ideleFub (kFub_of hSt) v (vacShift_of f) hAr (finM_of f) p Fin.schSpan Id.idealId'
  exact ⟨a, coneFactorisation_of_codimension_two a, coneFacB_of hA ideleFub (kFub_of hSt) v (vacShift_of f) hAr (finM_of f) p Fin.schSpan Id.idealId'⟩

end PositivityTheory.ThKG.Loc.Cone

end
