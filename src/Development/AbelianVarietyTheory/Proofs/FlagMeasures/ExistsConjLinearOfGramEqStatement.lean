module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearOfGramEq
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

theorem _root_.GlobalTheory.T.exists_conjLinear_of_gram_eq' : ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Type) [AddCommGroup M] [Module ℂ M] (N : M → M → ℂ) (I : Type) (a : I → W) (b : I → M), (∀ p p' q, N (p + p') q = N p q + N p' q) → (∀ (c : ℂ) p q, N (c • p) q = c * N p q) → (∀ p q, N q p = star (N p q)) → (∀ p, N p p = 0 → p = 0) → Submodule.span ℂ (Set.range a) = ⊤ → (∀ i j, N (b j) (b i) = ⟪a j, a i⟫_ℂ) → ∃ Jm : W →ₗ⋆[ℂ] M, (∀ i, Jm (a i) = b i) ∧ ∀ ξ η, N (Jm η) (Jm ξ) = ⟪η, ξ⟫_ℂ := by
  first | exact @GlobalTheory.exists_conjLinear_of_gram_eq | exact GlobalTheory.exists_conjLinear_of_gram_eq | (intros; apply GlobalTheory.exists_conjLinear_of_gram_eq <;> assumption)
