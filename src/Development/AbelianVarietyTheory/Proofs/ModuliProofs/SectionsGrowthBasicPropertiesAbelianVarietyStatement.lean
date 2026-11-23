module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVariety
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
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (g : ℕ), M.IsLB → (∃ r, SectionsHaveFiniteDimension P.A.hom M r) ∧ (∀ δ δ', Vol P.A.hom M g δ → Vol P.A.hom M g δ' → δ = δ') ∧ (∀ (M' : LB P.A.left) δ, M'.IsLB → LBIso M M' → Vol P.A.hom M g δ → Vol P.A.hom M' g δ) ∧ (∀ (a : ℕ) δ, 1 ≤ a → Vol P.A.hom M g δ → Vol P.A.hom (lbPow M a) g ((a : ℝ) ^ g * δ)) ∧ (∀ (a : ℕ) δ, 1 ≤ a → Out.RelAmple P.A M → Vol P.A.hom (lbPow M a) g ((a : ℝ) ^ g * δ) → Vol P.A.hom M g δ) ∧ ∀ (M' : LB P.A.left) (s : (LB.div M' M).Sec), M'.IsLB → (∃ j, s.f j ≠ 0) → (∀ r r', SectionsHaveFiniteDimension P.A.hom M r → SectionsHaveFiniteDimension P.A.hom M' r' → r ≤ r') ∧ ∀ δ δ', Vol P.A.hom M g δ → Vol P.A.hom M' g δ' → δ ≤ δ' := by
  first | exact @GlobalTheory.VolBasic.vol_basic | exact GlobalTheory.VolBasic.vol_basic | (intros; apply GlobalTheory.VolBasic.vol_basic <;> assumption)
