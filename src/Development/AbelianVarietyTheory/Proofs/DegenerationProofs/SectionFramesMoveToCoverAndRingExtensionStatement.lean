module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension
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

theorem _root_.GlobalTheory.T.sectionFrames_move_to_cover_and_ringExtension : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S Z : Scheme.{0}) (t₀ : SAB H S) (t : SAB H Z) (π : Z ⟶ S) (_ : SABMap t t₀ π) (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [CommRing R] [IsDomain R] [CharZero R] (g : R₁ →+* R) (gam : FractionRing R₁ →+* FractionRing R), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R _ (g r)) → ∀ (x₁ : Sp (FractionRing R₁) ⟶ S) (x : Sp (FractionRing R) ⟶ Z), x ≫ π = spMap gam ≫ x₁ → PolAt t₀ x₁ → ∀ (N n : ℕ) (f₁ : Fin n → LB.Sec (LPow t₀.G t₀.PP.L (N : ℤ) (Over.mk x₁))), IsFrame t₀.G t₀.PP.L N x₁ f₁ → ∃ f : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk x)), IsFrame t.G t.PP.L N x f ∧ BasisAlong t.G t.PP.L N (𝟙 _) f := by
  first | exact @GlobalTheory.FramePull.frame_pull | exact GlobalTheory.FramePull.frame_pull | (intros; apply GlobalTheory.FramePull.frame_pull <;> assumption)
