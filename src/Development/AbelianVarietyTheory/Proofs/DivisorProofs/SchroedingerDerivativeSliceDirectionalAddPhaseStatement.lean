module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhase
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

open IsDedekindDomain NumberField
open scoped Classical


theorem _root_.GlobalTheory.T.schroedingerDerivative_slice_directional_add_phase : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      Differentiable ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.dS F ψ h Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          fderiv ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x h.1 +
            2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
  first | exact @GlobalTheory.WeilL2Words.dS_adeleJoin_eq | exact GlobalTheory.WeilL2Words.dS_adeleJoin_eq | (intros; apply GlobalTheory.WeilL2Words.dS_adeleJoin_eq <;> assumption)
