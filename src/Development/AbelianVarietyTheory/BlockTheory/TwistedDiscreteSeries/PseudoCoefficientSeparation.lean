module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory
open Formalism.REAL (UJ)
open Formalism.MainNotions.S (IsURepOn UJset allPos)
open GlobalTheory.Dec (HasInfChar IsSqIntIrr UEquiv)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open GlobalTheory.OpTrace (HasTrace repOp)
open GlobalTheory.RealInd (IsIrrAdm groupRep)

namespace GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation

def HasWideGaps {r : ℕ} (lam : Fin r → ℤ) : Prop :=
  StrictAnti lam ∧ ∀ i j : Fin r, (j : ℕ) = i + 1 → (r : ℤ) ≤ lam i - lam j

def IsDiscreteWithInfChar {r : ℕ} (ε : Fin r → Bool) (lam : Fin r → ℤ) {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X)) : Prop :=
  IsSqIntIrr ε D ∧ HasInfChar ε (fun a => (lam a : ℂ)) D

def PseudoCoeffSeparation : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ), HasWideGaps lam →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
      (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X)) (hD : IsDiscreteWithInfChar ε lam D)
      (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ (ujRep hD.1.2.2.1) f →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (π : Matrix (Fin r) (Fin r) ℂ → (V →L[ℂ] V)) (hπ : IsIrrAdm ε π) (c : ℂ),
      HasTrace (repOp (groupRep ε hπ.2.1.1) μ f) c → c ≠ 0 →
        HasInfChar ε (fun a => (lam a : ℂ)) π ∧ (IsURepOn (UJset ε) π → UEquiv ε π D ∧ c = 1)

end GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation

end
