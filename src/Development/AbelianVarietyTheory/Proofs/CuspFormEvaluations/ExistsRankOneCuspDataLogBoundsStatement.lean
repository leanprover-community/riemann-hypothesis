module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRankOneCuspDataLogBounds
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.exists_rankOne_cuspData_log_bounds : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (e : ∀ k : (T.U j σ).Comp, XExt ((T.U j σ).X k)) (M wg : ℝ), 1 ≤ M ∧ Real.log M ≤ 30 * large₂.sc.L ∧ 0 < wg ∧ Real.log wg ≤ 3 * large₂.sc.L ∧ Real.log ((fdeg D.host.E : ℝ) * wg + 2) ≤ 5 * large₂.sc.L ∧ ∀ k, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤ wg ∧ (∀ v ∈ (e k).L', herm ((T.U j σ).X k).Gm v v = 0 → ∀ b : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc b = b → IsIntegral ℤ b → ∃ γ ∈ ((T.U j σ).X k).Γ, ((T.U j σ).X k).χ (laU (T.U j σ) (wtA w) w.n k) γ = 1 ∧ ∀ τ : ((T.U j σ).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j σ).X k).flowMat v τ ((M : ℂ) * τ.1 b)) ∧ Real.log (1 + ∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ 3 * large₂.sc.L ∧ Real.log (e k).NA ≤ 4 * large₂.sc.L ∧ Real.log (e k).NC ≤ 2 * large₂.sc.L ∧ Real.log (e k).g ≤ 19 * large₂.sc.L ∧ Real.log (1 / (e k).k0) ≤ 3 * large₂.sc.L := by
  first | exact @GlobalTheory.CuspDataBounds.cusp_data_bounds | exact GlobalTheory.CuspDataBounds.cusp_data_bounds | (intros; apply GlobalTheory.CuspDataBounds.cusp_data_bounds <;> assumption)
