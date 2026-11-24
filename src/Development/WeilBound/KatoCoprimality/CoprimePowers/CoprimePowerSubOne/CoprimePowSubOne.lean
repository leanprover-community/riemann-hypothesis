module

public import GroundTheory.PAdicHodge.GaloisOnCp
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import GroundTheory.LocalFields.FilteredSurj

@[expose] public section

noncomputable section

namespace GaloisFrobeniusFixed

open GroundTheory.PAdicHodge GroundTheory.LocalField

variable (l : ℕ) [Fact l.Prime]

abbrev GQ : Type := PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l

def chi0 : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (PadicAlgCl l) l).comp
    (MulSemiringAction.toRingAut (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (PadicAlgCl l))

variable {l}

def toBot (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) :
    PadicAlgCl l ≃ₐ[(⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))] PadicAlgCl l :=
  { g.toRingEquiv with
    commutes' := fun x => by
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 x.2
      change g (x : PadicAlgCl l) = (x : PadicAlgCl l)
      rw [← hq, AlgEquiv.commutes] }

def σC (g : GQ l) : ℂ_[l] ≃+* ℂ_[l] := galCp (toBot g)

def χ (g : GQ l) : ℚ_[l] := ((chi0 l g : ℤ_[l]) : ℚ_[l])

end GaloisFrobeniusFixed

end
