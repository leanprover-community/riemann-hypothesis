module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeTranslationInvariant
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

theorem _root_.GlobalTheory.T.scaled_lattice_translation_invariant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
    (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
      ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        (∀ x, f' x = f (x + fun i => mixedEmbedding F (ξ i))) → T f' = T f) →
    (∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
      ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        (∀ x, f' x = Complex.exp (-(2 * Real.pi * Complex.I) *
          ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (b i)) : ℝ) : ℂ)) * f x) →
        T f' = T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      T f = c * ∑' ξ : κ → F, {ξ : κ → F | (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈
        GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun ξ => f (fun i => mixedEmbedding F (ξ i))) ξ := by
  first | exact @GlobalTheory.LatUniq.main_lat | exact GlobalTheory.LatUniq.main_lat | (intros; apply GlobalTheory.LatUniq.main_lat <;> assumption)
