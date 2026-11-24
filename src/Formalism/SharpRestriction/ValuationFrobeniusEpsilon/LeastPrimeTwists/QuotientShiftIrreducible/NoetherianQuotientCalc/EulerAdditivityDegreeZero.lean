module

public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension
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

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

def GMod.quots {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] :
    List (Deg k × R) → GMod B R k → GMod B R k
  | [], F => F
  | (_, s) :: ts, F => GMod.quots ts (F.quot s)

def RulePos : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod), Valid X.𝒜 ts → F.IsGr X.𝒜 →
    admitted X.𝒜 ts F.Ann → ∀ᶠ m in atTop, 0 ≤ chi ts F m

def RuleUB : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts us : List (Deg k × X.R)) (F : X.Mod), Valid X.𝒜 (ts ++ us) →
    F.IsGr X.𝒜 → admitted X.𝒜 (ts ++ us) F.Ann →
    ∀ᶠ m in atTop, chi (ts ++ us) F m ≤ chi us (F.quots ts) m

def RuleMono : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F' F F'' : X.Mod), Valid X.𝒜 ts →
    F'.IsGr X.𝒜 → F.IsGr X.𝒜 → F''.IsGr X.𝒜 → SES F' F F'' → admitted X.𝒜 ts F.Ann →
    ∀ᶠ m in atTop, chi ts F'' m ≤ chi ts F m

def RuleSmall : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod), Valid X.𝒜 ts → F.IsGr X.𝒜 →
    admitted X.𝒜 [] F.Ann → ∀ᶠ m in atTop,
      chi ts F m = ∑ I ∈ (Finset.univ : Finset (Fin ts.length)).powerset,
        (-1 : ℤ) ^ I.card * ((Module.length X.B (F.gr (m - ∑ i ∈ I, (ts.get i).1))).toNat : ℤ)

def EulerAdditivityDegreeZero : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod) (d : Deg k) (s s' : X.R),
    Valid X.𝒜 ((0, s) :: (d, s') :: ts) → F.IsGr X.𝒜 → admitted X.𝒜 ((d, s * s') :: ts) F.Ann →
    ∀ᶠ m in atTop, chi ((d, s * s') :: ts) F m = chi ((0, s) :: ts) F m + chi ((d, s') :: ts) F m

end Formalism.MainNotions.V.Pf.V2.Calc
