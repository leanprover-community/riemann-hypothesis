module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsOfAffineBasis
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasCechDeRhamPeriods_of_affine_basis : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : cechDeRhamTotalCocyclesOne (OAff (str A))) (K : Type) (W : K → A.left.affineOpens) (k : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ i j, ∀ z ∈ pre u.ex (W i).1, z ∈ pre u.ex (W j).1 → ∃ l, W l ≤ W i ∧ W l ≤ W j ∧ z ∈ pre u.ex (W l).1 ∧ (∀ a : Opposite.op (W i) ⟶ Opposite.op (W l), k l z = k i z + val u.ex (W l).1 (c.1.1 _ _ a) z) ∧ ∀ a : Opposite.op (W j) ⟶ Opposite.op (W l), k l z = k j z + val u.ex (W l).1 (c.1.1 _ _ a) z) → (∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, ∃ i, W i ≤ U ∧ z ∈ pre u.ex (W i).1) → (∀ i, DifferentiableOn ℂ (k i) (pre u.ex (W i).1)) → (∀ i, ∀ z ∈ pre u.ex (W i).1, fderiv ℂ (k i) z = evForm u.ex (W i).1 z (c.1.2 (Opposite.op (W i)))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i).1, k i (z + l) = k i z + q l) → IsPer u.ex u.Λ (Hyp1.mk _ c) q := by
  first | exact @GlobalTheory.CechPer.isPer_of_basis | exact GlobalTheory.CechPer.isPer_of_basis | (intros; apply GlobalTheory.CechPer.isPer_of_basis <;> assumption)
