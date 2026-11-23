module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
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
import Mathlib.Tactic.Linter.HaveILetI
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormInf

theorem infPlace_norm_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) (y : E) (c : ℝ≥0) (h : ∀ τ : GlobalTheory.AdelicU.EmbOver E w, ‖τ.1 y‖₊ ≤ c) :
    w (Algebra.norm F y) ≤ (c : ℝ) ^ Module.finrank F E := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  rw [← InfinitePlace.norm_embedding_eq]
  have e : w.embedding (Algebra.norm F y) = ∏ σ : E →ₐ[F] ℂ, σ y := Algebra.norm_eq_prod_embeddings F ℂ y
  rw [e, norm_prod, ← AlgHom.card F E ℂ]
  calc ∏ σ : E →ₐ[F] ℂ, ‖σ y‖ ≤ ∏ _σ : E →ₐ[F] ℂ, (c : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun σ _ => by
          exact_mod_cast h ⟨σ.toRingHom, RingHom.ext σ.commutes⟩
    _ = (c : ℝ) ^ Fintype.card (E →ₐ[F] ℂ) := by rw [Finset.prod_const, Finset.card_univ]

theorem main : ∀ (D : D7) (w : InfinitePlace D.host.F) (y : D.host.E) (c : ℝ≥0), (∀ τ : GlobalTheory.AdelicU.EmbOver D.host.E w, ‖τ.1 y‖₊ ≤ c) → w (Algebra.norm D.host.F y) ≤ (c : ℝ) ^ Module.finrank D.host.F D.host.E :=
  fun D w y c h => infPlace_norm_le w y c h

end GlobalTheory.NormInf
