module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActSpreadFromDenseFibresAbelianScheme
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.oAct_spread_from_dense_fibres_abelianScheme : ∀ (O : Type) [CommRing O] (J : Type) (a : J → O) (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] (act₀ : J → (A ⟶ A)), Subring.closure (Set.range a) = ⊤ → IsAbelianScheme A → (∀ j, IsMonHom (act₀ j)) → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (φ : G.left ⟶ A.left) (act : OAct O G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ ∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left} → ∃ r : OAct O A, (∀ j, r.act (a j) = act₀ j) ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (G : Over T) [GrpObj G] (φ : G.left ⟶ A.left) (act : OAct O G), IsGrpPullback G A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left := by
  first | exact @GlobalTheory.oAct_spread_of_dense_fibres | exact GlobalTheory.oAct_spread_of_dense_fibres | (intros; apply GlobalTheory.oAct_spread_of_dense_fibres <;> assumption)
