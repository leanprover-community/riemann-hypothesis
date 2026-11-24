module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionTranslatesCoverSemiAbelian
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.finite_section_translates_cover_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, a i ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a i) (x i).left) ∧ ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u := by
  first | exact @GlobalTheory.Mum.cover_by_translates | exact GlobalTheory.Mum.cover_by_translates | (intros; apply GlobalTheory.Mum.cover_by_translates <;> assumption)
