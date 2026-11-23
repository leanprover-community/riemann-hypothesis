module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyEndomorphismEqMapLadic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.charpoly_deRhamHomology_endomorphism_eq_map_ladic : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (f : A ⟶ A) [IsMonHom f] (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
      (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
      ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ A),
      (∀ j x y, ev j (x + y) = ev j x * ev j y) →
      (∀ j x, ev j (φ x) = ev j x ≫ f) →
      (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
      (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ A), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
      ∀ [Module.Finite k (HdR A)],
        LinearMap.charpoly (push (dp0 k) (𝟙 _) f) = (LinearMap.charpoly φ).map (Int.castRingHom k) := by
  first | (exact @GlobalTheory.DeRham.charpoly_push_eq) | (exact GlobalTheory.DeRham.charpoly_push_eq) | (intros; apply GlobalTheory.DeRham.charpoly_push_eq  <;> assumption)
