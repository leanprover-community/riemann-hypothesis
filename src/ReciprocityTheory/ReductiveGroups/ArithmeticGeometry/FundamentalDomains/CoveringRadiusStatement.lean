module

public import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Matrix ReciprocityTheory.MultiplicativeHeights

noncomputable def d5mu (f r : ℕ) (d laStar : ℝ) : ℝ := 4 * ((f : ℝ) * r) ^ 3 * d / laStar

def CoveringRadiusStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Type) [Fintype ι] [Nonempty ι]
    (r p : ℕ) (S : HermForm K r) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (laStar : ℝ),
    Function.Injective σ →
    (∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) →
    p ≤ r → 0 < laStar → (∀ i, (Q i).det ≠ 0) →
    (∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y)) →
    IsLattice L → IsSelfDual S L →
    (∀ v ∈ L, v ≠ 0 → ∃ i, laStar ^ 2 ≤ normSq (Q i *ᵥ embVec (σ i) v)) →
    let μ := d5mu (Fintype.card ι) r |(NumberField.discr K : ℝ)| laStar
    (∀ w : ι → Fin r → ℂ, ∃ l ∈ L, ∑ i, normSq (Q i *ᵥ embVec (σ i) l - w i) ≤ μ ^ 2) ∧
    ∃ v : Fin r → Fin r → K, (∀ j, v j ∈ L) ∧ LinearIndependent K v ∧ ∀ j, majSq σ Q (v j) ≤ μ ^ 2

end ReciprocityTheory.ChartRestriction.G.FD
