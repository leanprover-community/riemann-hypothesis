module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartSiegelLevelCoverSharpTheta
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_chart_siegelLevelCover_sharpTheta : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ η ∈ genericPoints F.X, ∃ ℓ : ℕ, ℓ.Prime ∧ Odd ℓ ∧ ∀ j : ℕ, 1 ≤ j → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (κ : cycAway n →+* o) (R : Subalgebra o Ω) (J : Type) (b : TBase o ((ℓ ^ j) ^ 2)) (t : TObj (8 * g) ((ℓ ^ j) ^ 2) J b (spMap (algebraMap o R))) (w w' : J) (x : Sp R ⟶ F.X), R.FG ∧ (∀ y : Ω, ∃ a ∈ R, ∃ c ∈ R, y = a / c) ∧ t.Prim w w' ∧ (∀ (T : Scheme.{0}) (f : T ⟶ Sp R) (P : PolAV T) (φ : P.A.left ⟶ t.A.left), IsGrpPullback P.A t.A f φ → LBIso P.L (t.L.pull φ) → SharpOver F W P (f ≫ x)) ∧ (∀ w, (spMap R.val.toRingHom ≫ x) w = η) ∧ spMap R.val.toRingHom ≫ x ≫ F.s = spMap ((algebraMap o Ω).comp κ) ∧ κ.Finite ∧ ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  first | exact @GlobalTheory.PoincChart.exists_chart | exact GlobalTheory.PoincChart.exists_chart | (intros; apply GlobalTheory.PoincChart.exists_chart <;> assumption)
