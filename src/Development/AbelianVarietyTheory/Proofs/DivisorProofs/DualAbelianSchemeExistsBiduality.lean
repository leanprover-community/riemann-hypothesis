module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemePoincareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualAbelianSchemePoincareSwapStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem smoothOfRelDim_of_pullback_snd_identity {S : Scheme.{0}} (X : Over S) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd X.hom (𝟙 S))) : SmoothOfRelativeDimension g X.hom := by
  have e : X.hom = inv (pullback.fst X.hom (𝟙 S)) ≫ pullback.snd X.hom (𝟙 S) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  have := smoothOfRelativeDimension_comp (n := 0) (m := g) (inv (pullback.fst X.hom (𝟙 S))) (pullback.snd X.hom (𝟙 S))
  simpa using this

theorem smoothOfRelDim_pullback_snd_identity {S : Scheme.{0}} (X : Over S) (g : ℕ)
    (h : SmoothOfRelativeDimension g X.hom) : SmoothOfRelativeDimension g (pullback.snd X.hom (𝟙 S)) := by
  have e : pullback.snd X.hom (𝟙 S) = pullback.fst X.hom (𝟙 S) ≫ X.hom := by
    rw [pullback.condition, Category.comp_id]
  rw [e]
  have := smoothOfRelativeDimension_comp (n := 0) (m := g) (pullback.fst X.hom (𝟙 S)) X.hom
  simpa using this

theorem dualAbelianScheme : GlobalTheory.Published.DualAbelianScheme := by
  intro S A _ hA
  obtain ⟨B, _, P, hB, hdim, hdual⟩ := GlobalTheory.T.exists_dual_abelianScheme_poincare S A hA
  refine ⟨B, inferInstance, P, hB, fun g hg => ?_, hdual, GlobalTheory.T.isDualAbelianSchemePoincare_swap S A B P hA hB hdim hdual⟩
  exact smoothOfRelDim_of_pullback_snd_identity B g (hdim g S (𝟙 S) (smoothOfRelDim_pullback_snd_identity A g hg))

end GlobalTheory
