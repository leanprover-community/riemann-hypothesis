module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovariantDerivativeValueCharacterGerms
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

theorem _root_.GlobalTheory.T.covariantDerivative_value_character_germs : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) := by
  first | exact @GlobalTheory.nabVal_character_columns_of_canonGauge | exact GlobalTheory.nabVal_character_columns_of_canonGauge | (intros; apply GlobalTheory.nabVal_character_columns_of_canonGauge <;> assumption)
