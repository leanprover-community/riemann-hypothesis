module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoGluedFromLinCombPullback
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_iso_glued_from_linComb_pullback : ∀ {X X' Y : Scheme.{0}} {M : LB Y}, M.IsLB → ∀ {L' : LB X'}, L'.IsLB →
    ∀ {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (X' ⟶ Y)) (ε : K → ℤ) (ψ : K' → (X ⟶ Y)) (e : K' → ℤ)
    (F : X ⟶ X') (w₁ : LB.Iso L' (LB.LinComb M φ ε)), w₁.IsGen →
    ∀ (u : LB.Gen (LB.LinComb M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim ε (fun i => - e i)))), u.IsGen →
    ∃ w : LB.Iso (LB.LinComb M ψ e) (L'.pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (J : (Z ⟶ Y) → M.ι), Good M z J → ∀ j' : L'.ι, F (f z) ∈ L'.U j' →
        gw w f z j' (fun i => J (f ≫ ψ i)) = (gv w₁ (f ≫ F) z (fun k => J ((f ≫ F) ≫ φ k)) j')⁻¹ * val u f z J := by
  first | exact @GlobalTheory.Mum.iso_linComb_pull_glue | exact GlobalTheory.Mum.iso_linComb_pull_glue | (intros; apply GlobalTheory.Mum.iso_linComb_pull_glue <;> assumption)
