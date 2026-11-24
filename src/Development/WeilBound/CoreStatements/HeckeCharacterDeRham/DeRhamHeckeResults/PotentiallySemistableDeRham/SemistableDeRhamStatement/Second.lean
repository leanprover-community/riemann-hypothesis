module

public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
public import GroundTheory.PAdicHodge.BStPeriod
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

namespace DeRhamPotentiallySemistable.DRPst

open Formalism.Per6 GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

def qQ : ℚ_[l] →+* BdR l := (algebraMap (BdRp l) (BdR l)).comp (algebraMap ℚ_[l] (BdRp l))

def iC : ACris.ACris ℂ_[l] l →+* BdR l :=
  (algebraMap (BdRp l) (BdR l)).comp (ACris.iota ℂ_[l] l)

def tQ : BdR l := iC l (tA l)

def uQ : BdR l := algebraMap (BdRp l) (BdR l) (uBdR l)

def Bst : Subring (BdR l) :=
  Subring.closure (Set.range (iC l) ∪ {((l : BdR l))⁻¹, (tQ l)⁻¹, uQ l})

variable {l}

def IsAdm (S : Set (BdR l)) {d : ℕ} (G : Subgroup (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l))
    (r : G → Matrix (Fin d) (Fin d) ℚ_[l]) : Prop :=
  ∃ P Q : Matrix (Fin d) (Fin d) (BdR l), (∀ i j, P i j ∈ S ∧ Q i j ∈ S) ∧ P * Q = 1 ∧
    ∀ σ : G, (r σ).map (qQ l) * P.map (σD σ.1) = P

end DeRhamPotentiallySemistable.DRPst

