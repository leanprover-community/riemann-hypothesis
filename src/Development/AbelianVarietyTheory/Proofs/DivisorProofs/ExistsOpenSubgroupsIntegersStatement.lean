module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsIntegers
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

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.exists_open_subgroups_integers : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (B v : Set (v.adicCompletion F))) ∧
      (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) ∧
      (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      ∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y := by
  exact @GlobalTheory.SBBox.exists_box_invariant
