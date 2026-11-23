module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Formalism.RealPlaceAnalysis.StatementE
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GlRelationsDerivativePreserved
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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


theorem _root_.GlobalTheory.T.gl_relations_triangular_annihilation : ∀ (W Q : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup Q] [Module ℂ Q] (c N : ℕ) (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (Xf : Fin N → Fin N → Module.End ℂ W), Formalism.REAL.GlRel Xf → ∀ Wn : Submodule ℂ W, (∀ p q, ∀ F ∈ Wn, Xf p q F ∈ Wn) →
    ∀ L : W →ₗ[ℂ] Q, (∀ p q, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q → ∀ F ∈ Wn, L (Xf p q F) = 0) →
    ∀ W₀ : Set W, W₀ ⊆ Wn → (∀ v : ℂ, ∃ s : ℂ, ∀ F ∈ W₀, Formalism.REAL.qdet Xf v F = s • F) →
    ∀ (i : Fin c) (w : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀,
      L (Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) w) q F) = 0 := by
  exact @GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks.monic_relations_along_block
