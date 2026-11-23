module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigValD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstJetTermsGaugeUnitMulBaseChange
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.firstJetTerms_gauge_unit_mul_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR R)) (gm : GtPt D (TE R C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF R C))) gm₀ gm → ∀ (k : ℕ) (J : (Sp (DualNumber R) ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → ∃ T : (DualNumber C)ˣ, GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left) ≠ 0 ∧ (T : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left)) ^ k = ν.rg ^ k ∧ ∀ (s : Fam D C k) (n : ℕ) (c : Fin n → C) (f : Fin n → ∀ α : D.X, D.SecB k α), (∀ α, GeneratorPullback.SecLin D.P.L (DegPre.famφ D C α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))) → ∀ α, jc ν s gm α = (T : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (GlobalTheory.MBLow.TanExp.termV J gm₀ (f i (ν.eX α))) := by
  first | exact @GlobalTheory.MBLow.TanGauge.jc_eq_unit_mul | exact GlobalTheory.MBLow.TanGauge.jc_eq_unit_mul | (intros; apply GlobalTheory.MBLow.TanGauge.jc_eq_unit_mul <;> assumption)
