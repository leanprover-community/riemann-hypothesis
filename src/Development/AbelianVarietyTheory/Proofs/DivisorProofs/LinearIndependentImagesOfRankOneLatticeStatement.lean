module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentImagesOfRankOneLattice
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

open NumberField

theorem _root_.GlobalTheory.T.linearIndependent_images_of_iSupIndep_rankOne : ∀ {K : Type} [Field K] [NumberField K] {p m n : ℕ} (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (v : Fin m → K), v ≠ 0 → ∀ (𝔟 : Submodule (𝓞 K) K),
    𝔟 ≠ ⊥ → (∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K
      ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    LinearIndependent K (fun a => M a v) := by
  first | exact @GlobalTheory.linearIndependent_images_of_rankOne_lattice | exact GlobalTheory.linearIndependent_images_of_rankOne_lattice | (intros; apply GlobalTheory.linearIndependent_images_of_rankOne_lattice <;> assumption)
