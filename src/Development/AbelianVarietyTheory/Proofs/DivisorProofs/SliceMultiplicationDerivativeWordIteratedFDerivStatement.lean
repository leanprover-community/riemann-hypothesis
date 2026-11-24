module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceMultiplicationDerivativeWordIteratedFDeriv
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


theorem _root_.GlobalTheory.T.slice_multiplicationDerivativeWord_iteratedFDeriv : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (u : κ → mixedEmbedding.mixedSpace F) (i : ℕ) (vs : List (κ → mixedEmbedding.mixedSpace F))
        (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
            vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x := by
  first | exact @GlobalTheory.WeilL2Words.slice_word_mul_fderivs | exact GlobalTheory.WeilL2Words.slice_word_mul_fderivs | (intros; apply GlobalTheory.WeilL2Words.slice_word_mul_fderivs <;> assumption)
