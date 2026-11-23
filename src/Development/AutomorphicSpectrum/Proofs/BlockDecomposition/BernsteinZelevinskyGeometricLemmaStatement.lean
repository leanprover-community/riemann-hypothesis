module

public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BernsteinZelevinskyGeometricLemma
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.bernstein_zelevinsky_geometric_lemma : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (β γ : Fin n → ℕ), ∃ (K : ℕ) (w : Fin K → Equiv.Perm (Fin n)), (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W), GroundTheory.Automorphic.IsSmooth σ → ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)), V 0 = ⊥ ∧ V K = ⊤ ∧ Monotone V ∧ ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m), ∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1))) (indRep (cellLeviSub F β γ (w j)) (normInducing σ γ (w j))), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  first | exact @GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform | exact GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform | (intros; apply GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform <;> assumption)
