module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LowerBoundAtFramesFamilyWithScaledThetaRules
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.lower_bound_at_frames_family_with_scaled_thetaRules : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (_EX : ErrX D) (j : ℕ) (hj : InR D j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal (recB h.toLawsCore)) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW S wL → ∀ (P₁ : MvPolynomial (LtN (T.Q.Dw j) wL.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA wL) wL.n → IsBlockProd P₁ → ∀ (N : ℕ) (w : Fin (N + 1) → (recB h.toLawsCore).Cusp j wL), ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F) P₁ (fun k => ((w k).1 : T.R j)) → ∀ tableLineDegreeFive : ℝ, p14 D.host.E D.R.r wL.n D.R.m ≤ tableLineDegreeFive → I2AtFramePoints (T.U j) (xiR D) (fun k => ((w k).1 : T.R j)) (wtA wL, wL.n) (I2.th (E := D.host.E) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL)))) tableLineDegreeFive (WeightAlgebra.DF wL) (cc D large₂ C2 A2 CR wL) := by
  first | exact @GlobalTheory.DegreeInterpolationBounds.i2iAt_record | exact GlobalTheory.DegreeInterpolationBounds.i2iAt_record | (intros; apply GlobalTheory.DegreeInterpolationBounds.i2iAt_record <;> assumption)
