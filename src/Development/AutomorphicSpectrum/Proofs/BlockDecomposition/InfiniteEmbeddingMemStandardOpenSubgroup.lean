module

public import GroundTheory.GlobalFields.TateThesis.EulerFactors
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsInverse
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem infiniteEmbedding_mem_standardOpenSubgroup {F : Type*} [Field F] [NumberField F]
    (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ standardOpenSubgroup F := by
  refine (mem_standardOpenSubgroup F).2 fun v ↦ ?_
  have h1 : ((infiniteEmbedding w a : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [coe_infiniteEmbedding]
    rfl
  have h2 : (((infiniteEmbedding w a)⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [← map_inv, coe_infiniteEmbedding]
    rfl
  rw [h1, h2]
  exact ⟨one_mem _, one_mem _⟩

theorem infiniteParams_eq_zero {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (hχ : standardOpenSubgroup F ≤ χ.toIdele.ker) (w : InfinitePlace F) :
    χ.infiniteParams w = (0, 0) := by
  refine (χ.infiniteParams_unique w (p := (0, 0)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
  have h : χ.toIdele (infiniteEmbedding w a) = 1 :=
    hχ (infiniteEmbedding_mem_standardOpenSubgroup w a)
  simp [HeckeCharacter.infiniteComponent_apply, h]

theorem gammaFactor_eq_of_unramified : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (χ : HeckeCharacter F), standardOpenSubgroup F ≤ χ.toIdele.ker →
    ∀ s : ℂ, χ.gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F := by
  intro F _ _ _ χ hχ s
  have hw : ∀ w : InfinitePlace F, χ.infiniteGamma w s = Complex.Gammaℝ s := fun w ↦ by
    have hr : w.IsReal := IsTotallyReal.isReal w
    have hp := infiniteParams_eq_zero χ hχ w
    simp [HeckeCharacter.infiniteGamma, hr, HeckeCharacter.infiniteTau,
      HeckeCharacter.infiniteWeight, hp]
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h3 := IsTotallyReal.nrComplexPlaces_eq_zero F
    omega
  rw [HeckeCharacter.gammaFactor, Finset.prod_congr rfl fun w _ ↦ hw w, Finset.prod_const,
    Finset.card_univ, hcard]

end GlobalTheory.CompanionTheory.PartialZeta
