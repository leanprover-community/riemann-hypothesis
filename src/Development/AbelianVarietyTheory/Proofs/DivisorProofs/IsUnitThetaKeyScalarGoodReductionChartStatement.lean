module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitThetaKeyScalarGoodReductionChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.isUnit_thetaKeyScalar_goodReduction_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ κ : KeyRule, IsKeyRule κ → ∀ (M : GChart Y) (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ x : KeyIn K, KeyAt M (spMap (algebraMap R K) ≫ z) (le_preimage_comp _ hz) x → ∃ u : Rˣ, (κ K x : K) = algebraMap R K u := by
  first | exact @GlobalTheory.KeyUnitGood.isUnit_key_of_good | exact GlobalTheory.KeyUnitGood.isUnit_key_of_good | (intros; apply GlobalTheory.KeyUnitGood.isUnit_key_of_good <;> assumption)
