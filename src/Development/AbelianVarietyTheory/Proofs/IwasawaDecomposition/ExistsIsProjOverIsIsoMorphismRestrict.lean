module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBasicOpenOfMemClosure
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ChowLemma

theorem exists_dominant_lift {X X' : Scheme.{0}} (π : X' ⟶ X) {U W : X.Opens} (h : U ≤ W)
    (t : U.toScheme ⟶ X') [IsDominant t] (ht : t ≫ π = U.ι) :
    ∃ σ : U.toScheme ⟶ (π ⁻¹ᵁ W).toScheme, IsDominant σ ∧ σ ≫ (π ⁻¹ᵁ W).ι = t ∧
      σ ≫ π ∣_ W = X.homOfLE h := by
  have hr : Set.range t ⊆ Set.range (π ⁻¹ᵁ W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change π (t x) ∈ W
    rw [← Scheme.Hom.comp_apply, ht]
    exact h x.2
  have e := IsOpenImmersion.lift_fac (π ⁻¹ᵁ W).ι t hr
  refine ⟨IsOpenImmersion.lift (π ⁻¹ᵁ W).ι t hr, ?_, e, ?_⟩
  · have : IsDominant (IsOpenImmersion.lift (π ⁻¹ᵁ W).ι t hr ≫ (π ⁻¹ᵁ W).ι) := by
      rwa [e]
    exact IsDominant.of_comp_of_isOpenImmersion _ (π ⁻¹ᵁ W).ι
  · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% e, ht, X.homOfLE_ι]

theorem exists_isProjOver_isIso_morphismRestrict : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp R) [IsProper f], ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (U : X.Opens), IsProjOver (π ≫ f) ∧ (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  first
  | exact @_root_.GlobalTheory.BasicOpenLocalExtension.chow_integral
  | exact _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral
  | (apply _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> assumption)
  | (intros; apply _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral ..)

end GlobalTheory.ChowLemma
