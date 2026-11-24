module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlAdaptedBasisMonotoneSubspaceChain
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_gl_adaptedBasis_monotoneSubspaceChain : ∀ {K : Type} [Field K] {n m : ℕ} (Y : Fin (m + 1) → Submodule K (Fin n → K)), Monotone Y → Y 0 = ⊥ → Y (Fin.last m) = ⊤ →
    ∃ (d : Fin m → ℕ) (h : ∑ j, d j = n) (g : GL (Fin n) K), ∀ (j : Fin (m + 1)) (y : Fin n → K),
      y ∈ Y j ↔ ∀ i : Fin n, (j : ℕ) ≤ ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) i : Fin m) : ℕ) →
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) i = 0 := by
  first | exact @GlobalTheory.Flag.exists_gl_adapted_chain | exact GlobalTheory.Flag.exists_gl_adapted_chain | (intros; apply GlobalTheory.Flag.exists_gl_adapted_chain <;> assumption)
