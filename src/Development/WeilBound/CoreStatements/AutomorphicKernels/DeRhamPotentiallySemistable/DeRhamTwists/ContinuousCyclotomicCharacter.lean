module

public import Development.WeilBound.CoreStatements.HeckeCharacterDeRham.DeRhamHeckeResults.PotentiallySemistableDeRham.SemistableDeRhamStatement.Second
import GroundTheory.PAdicHodge.ACrisBdRGalois
public import GroundTheory.PAdicHodge.ThetaBDeRhamPlusFieldCycloUnitBdRZpow
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace DeRhamTwist.Twist

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

variable {l : ℕ} [Fact l.Prime]

def chi0 (l : ℕ) [Fact l.Prime] : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (PadicAlgCl l) l).comp
    (MulSemiringAction.toRingAut (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (PadicAlgCl l))

theorem tQ_eq : tQ l = algebraMap (BdRp l) (BdR l) (tBdR l) := by
  show algebraMap (BdRp l) (BdR l) (ACris.iota ℂ_[l] l (tA l)) = _
  exact congrArg (algebraMap (BdRp l) (BdR l))
    (ACris.iota_periodT (untilt_epsilon (p := l)))

theorem tQ_ne : tQ l ≠ 0 := by
  rw [tQ_eq]
  exact algebraMap_tBdR_ne_zero

end DeRhamTwist.Twist
