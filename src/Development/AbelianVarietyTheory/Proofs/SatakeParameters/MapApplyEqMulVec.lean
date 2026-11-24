module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

namespace GlobalTheory.TwV

open NumberField
open scoped Matrix

theorem map_apply_eq_mulVec {E K : Type} [Field E] [Field K] (ρ : E →+* K) {N n : ℕ}
    (f : (Fin N → E) →ₗ[E] (Fin n → E)) (x : Fin N → E) :
    (fun k => ρ (f x k)) = ((LinearMap.toMatrix' f).map ρ) *ᵥ (fun k => ρ (x k)) := by
  funext k
  rw [← LinearMap.toMatrix'_mulVec f x]

  simp [Matrix.mulVec, dotProduct, map_sum]

theorem locSp_map {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N n : ℕ} (f : (Fin N → E) →ₗ[E] (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    locSp W ρ (Λ.map (f.restrictScalars (𝓞 E))) =
      (locSp W ρ Λ).map ((((LinearMap.toMatrix' f).map ρ).mulVecLin).restrictScalars W) := by
  unfold locSp
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact map_apply_eq_mulVec ρ f x

end GlobalTheory.TwV
