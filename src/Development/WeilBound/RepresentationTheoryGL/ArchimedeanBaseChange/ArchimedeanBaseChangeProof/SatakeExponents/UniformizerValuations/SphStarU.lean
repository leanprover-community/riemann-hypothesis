module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
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

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.F.Eig

def SphStarU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (w : Pl E) (σ : SmIrr (UL n w)),
  GlobalTheory.SmGL.IsUnitarisable σ.ρ → Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1 → ∀ h₁ h₂, IsHecke (KL n w) h₁ → IsHecke (KL n w) h₂ →
    twTr σ.ρ (KL n w) (KL n w) (lconv h₁ h₂) LinearMap.id =
      twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id * twTr σ.ρ (KL n w) (KL n w) h₂ LinearMap.id ∧
    twTr σ.ρ (KL n w) (KL n w) (lstar h₁) LinearMap.id = starRingEnd ℂ (twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id) ∧
    twTr σ.ρ (KL n w) (KL n w) ((KL n w : Set (UL n w)).indicator 1) LinearMap.id = 1

end PositivityTheory.Rg.BcB.F.Eig

end
