module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfFiniteFibres
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFlagEqOfPluckerPointsEqFieldPoints
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

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

theorem _root_.GlobalTheory.T.lieFlag_eq_of_pluckerPoints_eq_field_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (t : ∀ (σ : E →+* ℂ) (m : Fin (Dw.mult σ)), Fin (plkNum Mc m + 1) → ((F.LL (ind σ m)).pull g).Sec), (∀ σ m q, (t σ m q).f = plkLoc F Mc g hg σ m q) → ∀ (ht : ∀ σ m, ⨆ q, nonzeroLocus (t σ m q) = ⊤) {R : Type} [CommRing R] (f : T ⟶ Sp R) (K : Type) [Field K] (a a' : Sp K ⟶ T), a ≫ g ≫ π = a' ≫ g ≫ π → (∀ σ m, a ≫ GlobalTheory.ProjSpace.toProj f (t σ m) (ht σ m) = a' ≫ GlobalTheory.ProjSpace.toProj f (t σ m) (ht σ m)) → ∃ hx' : (a' ≫ g) ≫ π = (a ≫ g) ≫ π, ∀ σ (i : ℕ), F.step (a' ≫ g) hx' σ i = F.step (a ≫ g) rfl σ i := by
  first | exact @GlobalTheory.FlagPlucker.Sep.step_eq_of_toProj_eq | exact GlobalTheory.FlagPlucker.Sep.step_eq_of_toProj_eq | (intros; apply GlobalTheory.FlagPlucker.Sep.step_eq_of_toProj_eq <;> assumption)
