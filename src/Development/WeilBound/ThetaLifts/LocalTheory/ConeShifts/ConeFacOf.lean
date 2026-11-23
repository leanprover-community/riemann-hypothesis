module

public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.ConeIntegralFactorisation
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PureSt
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ArchCone
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ContinuousFc
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PresOfHat
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.VacShiftOf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF

theorem coneFac_of (hA : ActsEx) (hSt : StabEx) (hO : ArchOp) (hU : ArchUniq) (hPS : PositivityTheory.Mix.PureSt) (hAr : ArchCone) :
    MeasEx ∧ PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation ∧ ConeFacA ∧ ConeFacB :=
  ⟨measEx_of hSt, coneFac_all hA hSt hO hU hPS hAr (vacFixX_of hSt)⟩

end PositivityTheory.ThKG.Loc.Cone

end
