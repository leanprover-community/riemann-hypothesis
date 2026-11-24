module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumMatchLengthSymmPreimages
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.arcDatumMatch_length_symm_preimages : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : O' →+* R) (u : R), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (P : DegPre R) [Module (𝓞 E) P.X] (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left) (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A) (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X), Match a f u P oP φ₁ he₁ w₁ e₁ → Match a f u P oP φ₂ he₂ w₂ e₂ → ∀ y, a.be (e₁.symm y) (e₁.symm y) = a.be (e₂.symm y) (e₂.symm y) := by
  first | exact @GlobalTheory.LN.be_symm_eq_of_match | exact GlobalTheory.LN.be_symm_eq_of_match | (intros; apply GlobalTheory.LN.be_symm_eq_of_match <;> assumption)
