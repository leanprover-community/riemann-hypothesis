module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
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
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbVarRed

theorem exists_fixedField_point (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) (_ : LocallyOfFiniteType A.hom) (x : ptOver K Ω ⟶ A)
    (hx : ∀ σ ∈ H, specAut σ ≫ x = x) :
    ∃ y : Sp (IntermediateField.fixedField H) ⟶ A.left,
      spMap (algebraMap (IntermediateField.fixedField H) Ω) ≫ y = x.left := by
  obtain ⟨E, hE1, hE2, -⟩ := GlobalTheory.SS.exists_fieldOfValues A.left Ω x.left
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [← Spec.map_id]
    congr 1
  have hfix : ∀ c ∈ E, ∀ σ ∈ H, σ c = c := by
    intro c hc σ hσ
    have h1 : spMap (σ : Ω →+* Ω) ≫ x.left = spMap (RingHom.id Ω) ≫ x.left := by
      rw [hid, Category.id_comp]
      exact congrArg CommaMorphism.left (hx σ hσ)
    exact (hE1 _ _).1 h1 c hc
  refine (hE2 (IntermediateField.fixedField H) (algebraMap (IntermediateField.fixedField H) Ω)).1 ?_
  intro c hc
  exact ⟨⟨c, fun σ => hfix c hc σ σ.2⟩, rfl⟩

end GlobalTheory.Published.AbVarRed
