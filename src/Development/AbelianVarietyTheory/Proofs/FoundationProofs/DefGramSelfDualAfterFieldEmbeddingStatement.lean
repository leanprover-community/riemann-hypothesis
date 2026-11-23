module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefGramSelfDualAfterFieldEmbedding
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
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.defGram_selfDual_after_field_embedding : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) → ∀ (ι : Type) (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) → ∀ τ, IsDefGram (gramK emb J τ) ∧ IsDefGram (gramKd emb J τ) ∧ ∀ L : Submodule (𝓞 E) (Fin n → E), IsSelfDualE cE J L → IsSelfDualK (gramK emb J τ) (tauLat emb τ L) ∧ IsSelfDualK (gramKd emb J τ) (dualFr (tauLat emb τ L)) := by
  first | exact @GlobalTheory.TestLat.defGram_selfDual_of_embedding | exact GlobalTheory.TestLat.defGram_selfDual_of_embedding | (intros; apply GlobalTheory.TestLat.defGram_selfDual_of_embedding <;> assumption)
