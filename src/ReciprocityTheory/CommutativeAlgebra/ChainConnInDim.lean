module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Spectrum.Prime.Topology
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.CA

open PrimeSpectrum

variable (R : Type*) [CommRing R]

def ConnInDim (k : WithBot ℕ∞) : Prop :=
  ∀ I : Ideal R, ringKrullDim (R ⧸ I) < k → IsConnected ((zeroLocus (I : Set R))ᶜ : Set (PrimeSpectrum R))

def Linked (k : WithBot ℕ∞) (p q : Ideal R) : Prop := k ≤ ringKrullDim (R ⧸ (p ⊔ q))

def AraLE {R : Type*} [CommRing R] (a : Ideal R) (r : ℕ) : Prop :=
  ∃ s : Finset R, s.card ≤ r ∧ (Ideal.span (s : Set R)).radical = a.radical

def DepthGE [IsLocalRing R] (n : ℕ) : Prop :=
  ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧ RingTheory.Sequence.IsRegular R rs

def IsCM [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ ∃ n : ℕ, ringKrullDim R = n ∧ DepthGE R n

end ReciprocityTheory.CA
