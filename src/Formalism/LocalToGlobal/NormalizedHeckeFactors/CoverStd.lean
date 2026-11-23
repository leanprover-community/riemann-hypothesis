module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2

def HeckeStdPlain : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
    (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B →
    ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ),
      s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n →
      (∀ f ∈ NG.TypeSp a.ρ J χ, NG.tN J s ϖ k f ∈ NG.TypeSp a.ρ J χ) ∧
      (∀ f ∈ NG.TypeSp a.ρ J χ, ∀ f' ∈ NG.TypeSp a.ρ J χ, ∀ c : ℂ,
        NG.tN J s ϖ k (c • f + f') = c • NG.tN J s ϖ k f + NG.tN J s ϖ k f') ∧
      (∀ (s' : SplitPlace L) (ϖ' : s'.v.adicCompletion (maximalRealSubfield L)) (k' : ℕ),
        s'.v ∉ B → IsUnif L s'.v ϖ' → 1 ≤ k' → k' ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ,
          NG.tN J s ϖ k (NG.tN J s' ϖ' k' f) = NG.tN J s' ϖ' k' (NG.tN J s ϖ k f)) ∧
      (∀ f ∈ NG.TypeSp a.ρ J χ, f ≠ 0 → ∀ μ : ℂ, NG.tN J s ϖ k f = μ • f →
        ∀ l : ℕ, l.Prime → ¬ s.Above l → ∃ d : ℕ, ¬ l ∣ d ∧ IsIntegral ℤ ((d : ℂ) * μ))

end Formalism.L2
