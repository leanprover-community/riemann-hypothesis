module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSpecPointsLevels
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.hom_spec_points_levels : ∀ (D : Data) (Λ : Lift D), (∀ (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B), spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔ ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a) ∧ (∀ (U : AffOp D.X) (T : Thick D.κ D.t), ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ g : Sec D.s U.unop.1 →+* T.B₀, spMap g ≫ affPt D.s U.unop = T.x ≫ D.i ∧ ∀ r, g (algebraMap D.R _ r) = T.π (algebraMap D.R T.B r)) ∧ (∀ (U : AffOp D.X) (C : Type) [CommRing C] (g g' : Sec D.s U.unop.1 →+* C), spMap g ≫ affPt D.s U.unop = spMap g' ≫ affPt D.s U.unop → g = g') ∧ ∃ N₀, ∀ N, N₀ ≤ N → ∀ U, IsLev (Λ.L.obj U).δ N := by
  first | exact @GlobalTheory.PDForm.Lift.hom_spec | exact GlobalTheory.PDForm.Lift.hom_spec | (intros; apply GlobalTheory.PDForm.Lift.hom_spec <;> assumption)
