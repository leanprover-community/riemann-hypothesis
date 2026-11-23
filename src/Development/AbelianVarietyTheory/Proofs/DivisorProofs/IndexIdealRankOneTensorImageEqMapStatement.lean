module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealRankOneTensorImageEqMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.indexIdeal_rankOne_tensor_image_eq_map : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K),
    (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p m n : ℕ) (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (Λ : Submodule (𝓞 E) (Fin p → E)),
    ell.FG → ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    Λ.FG → (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) →
    GlobalTheory.FlatCM.idx K p (Submodule.span (𝓞 K) {w | ∃ c ∈ Λ, ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e})
                 (⨆ a, ell.map ((M a).restrictScalars (𝓞 K))) =
      (GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))).map τ := by
  first | exact @GlobalTheory.IdxTensor.idx_image_eq_map | exact GlobalTheory.IdxTensor.idx_image_eq_map | (intros; apply GlobalTheory.IdxTensor.idx_image_eq_map <;> assumption)
