module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticFrameOfUnitUniformisationFrameStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionReadingExistsUniqueIsTheta
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleValueTestRingEqThetaValueStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueAnalyticFrameEqPolyDerivFockStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem thetaRule_value_periods : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (xf : (U.X k).dom) (W : UnfAt U k xf) (Wu : UnitAt W) (nab : NabV Xo c), IsNab Xo c nab → FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k xf) → ∀ (n : ℕ) (x x2 : Fin n → Dw.La), (∀ b, x2 b ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ b, x2 b - x b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab x P f → Differentiable ℂ Wu.θ ∧ toC (evR Xo c f (U.un k xf)) = ((l.M : ℂ)⁻¹) ^ P.totalDegree * I2.polyDeriv (MvPolynomial.map σ P) (letDir W.e) (fun z => ∏ b, fock Wu.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • W.Pm (W.F.t (W.ik k) (x2 b))) (fun w => Wu.θ ((l.M : ℂ) • w)) (z b)) 0 := by
  intro hci E _ _ _ H Dw l Xo c _ σ r U k xf W Wu nab hnab hft n x x2 h2 hx a P hP f hf
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨Φ, hof, hHm, -, -, hrd, -, hlin, hlev⟩ := GlobalTheory.T.exists_analytic_frame_of_unit_uniformisation_frame E H Dw l Xo c σ r U k xf W Wu
  have hv := GlobalTheory.T.thetaRuleValue_testRing_eq_thetaValue hci E H Dw l Xo c nab hnab a n x P hP f hf (CAt σ) (U.un k xf) hft
  refine ⟨((GlobalTheory.AnVal.reading_existsUnique_isTh _ _ _ _ _ Φ.toAnFr 1 _).2.1 _ hrd).1, ?_⟩
  have key := GlobalTheory.T.thetaValue_analyticFrame_eq_polyDeriv_fock hci E H Dw l Xo c (U.un k xf) W.g _ W.e Φ
    (W.Pm.comp (W.F.t (W.ik k)).toAddMonoidHom) (fun a => by rw [hof.2.1]; exact ⟨_, rfl⟩) hlin hlev nab hnab Wu.θ hrd
    n x x2 h2 hx a P hP _ hv
  rw [hHm] at key
  exact key

end GlobalTheory.AnVal
