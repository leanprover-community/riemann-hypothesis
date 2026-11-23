module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.NotApartOfOverPair
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearIndependentSimulEigen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.ExistsEllType
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.LacunaryBaseWeightAntitone
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW

namespace UpperTheory.Gal.Int.Cong

theorem ellSt_holds : EllSt := fun _ _ _ _ _ _ _ ha w₀ hl N hN m₀ => exists_ellType ha w₀ hl N hN m₀

theorem congFinG_of_step (H : StepSt) : CongFinG := congUWG_of H finU_holds DGen dGen_ne_zero

theorem congFinG_of_ex (H : WtLacEx) : CongFinG := congFinG_of_step (stepSt_of_ex ellSt_holds H)

theorem congFinOdd_of_ex (H : WtLacEx) : CongFinOdd := CongUWG.congUW4 (congFinG_of_ex H) Odd

end UpperTheory.Gal.Int.Cong
