module

public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.TorusIndex
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

section DiffLat

variable {Em : Type} [Field Em] [NumberField Em] {K : Type} [Field K] [NumberField K] {N : ℕ}

def diffLat (s : Em →+* K) (I : Submodule (𝓞 Em) (Fin N → Em)) : Submodule (𝓞 K) (Fin N → K) :=
  Submodule.span (𝓞 K) ((fun u i => s (u i)) ''
    {u | ∃ x ∈ differentIdeal ℤ (𝓞 Em), ∃ y ∈ I, u = (x : Em) • y})

end DiffLat

def EigenLatDifferent.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ),
    (∀ σ : Em →+* ℂ, ∃ t : Em →+* K, ι.comp t = σ) →
    ∀ (N : ℕ) (I : Submodule (𝓞 Em) (Fin N → Em)), I.FG → ∀ s : Em →+* K,
      eigenLat I s = diffLat s I

end GroundTheory.Heights₂.Heights.NineStatements
