module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU
attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_gtPt_of_character : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (χ₀ : Multiplicative D.X →* Fˣ), ∃ g : GtPtF D F, g.b = DegPre.zeroF D F ∧ (∀ α z J, Good D.P.L z J → (val (g.s α) (𝟙 _) z J).val = gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of F))) (χ₀ (Multiplicative.ofAdd α)).val)) ∧ (∀ N : ℕ, χ₀ ^ N = 1 → GtTors D N g) ∧ (g.IsZero ↔ χ₀ = 1) := by
  intro R _ _ D F _ _ χ₀
  refine ⟨TorusExt.torusPt D F (Additive.ofMul χ₀), TorusExt.torusPt_b _, fun α z J hJ => ?_, fun N hN => ?_, ?_⟩
  · refine (congrArg Units.val (TorusExt.torusPt_val χ₀ α hJ)).trans ?_
    exact (gs_eq (𝟙 _) z ⊤ trivial _).symm
  · refine ⟨_, (TorusExt.isNsmul_iff_eq N _ _).2 rfl, (TorusExt.isZero_iff_eq _).2 ?_⟩
    rw [← map_nsmul, ← ofMul_pow, hN, ofMul_one, map_zero]
  · rw [TorusExt.isZero_iff_eq, map_eq_zero_iff _ TorusExt.torusPt_injective]
    exact ofMul_eq_zero
end GlobalTheory.UU
end
