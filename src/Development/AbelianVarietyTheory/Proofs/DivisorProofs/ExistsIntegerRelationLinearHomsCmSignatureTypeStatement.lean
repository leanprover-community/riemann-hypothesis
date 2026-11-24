module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRelationLinearHomsCmSignatureType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_integer_relation_linear_homs_cm_signature_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (A B : PAT H (Sp ℂ)) (p q : ℕ), ρ ^ 2 = -(H.d : ℂ) →
    HasType H A.t.act ρ 1 0 → HasType H B.t.act ρ p q → ∀ (n : ℕ), p + q < n → ∀ ψ : Fin n → (A.t.G ⟶ B.t.G),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (ψ i)) →
    ∃ x : Fin n → 𝓞 E, x ≠ 0 ∧ ∏ i, (A.t.act.act (x i) ≫ ψ i) = 1 := by
  first | exact @GlobalTheory.CM.PureHom.exists_prod_act_comp_eq_one_of_pure | exact GlobalTheory.CM.PureHom.exists_prod_act_comp_eq_one_of_pure | (intros; apply GlobalTheory.CM.PureHom.exists_prod_act_comp_eq_one_of_pure <;> assumption)
