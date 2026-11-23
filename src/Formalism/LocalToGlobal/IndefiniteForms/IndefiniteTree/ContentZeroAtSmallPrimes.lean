module

public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCondPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain

namespace Formalism.L2.Indef.Tree.DepthCond

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}

theorem content_zero_at_small_primes (N : IndefNum Bs) (O : OnObj S P c) (Nd : NumDatum) (ι : Bs.J → ℕ)
    (hPg : LeafPage O) (tF : ContentEqualsDatumContent N Nd ι) (tP : TiePrimes O Nd) :
    ∀ w : HeightOneSpectrum (𝓞 K), plc w ∈ O.sm → ∀ j, N.F0 w j = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg1t, hg2t, -, -, -⟩ := hPg
  obtain ⟨hg1, hg2, -, -, hsm⟩ := tP
  intro w h2 j
  rw [tF w j]
  show Nd.FjP (ι j) (plc w) = 0
  apply (content_prime_condition_holds Nd (ι j) (plc w)).2.1
  · rw [← hg1]; exact fun h => hg1t (h ▸ h2)
  · rw [← hg2]; exact fun h => hg2t (h ▸ h2)
  · exact Or.inl (hsm ▸ h2)

end Formalism.L2.Indef.Tree.DepthCond
