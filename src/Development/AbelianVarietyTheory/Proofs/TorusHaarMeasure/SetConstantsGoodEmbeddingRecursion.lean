module

public import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveInstSt
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.TranscendenceDegreeRatiosCuspFormsComponentsStatement
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

noncomputable section

namespace GlobalTheory.BigRec


variable {D : D7} {T : Top D}

variable (h : LawsP T) {j : ℕ} (hj : InR D j)





theorem bigAt_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (c : ℝ) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) → (j < D.R.m → 0 < G.iet ∧ (recPlus h j hj).NonZeroComp _ G.et ∧ ∃ σ, GoodEmb T.Q.c σ ∧ PhRec h j σ G.w G.iet G.et c) → 0 ≤ c → 2 * c * g0 D ≤ 1 → (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th : (recB h.toLawsCore).Cusp j w1, (recPlus h j hj).NonZeroComp w1 th) → BigAt h j hj hG G := by
  intro D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hE hc hcg _
  exact ⟨hN, GlobalTheory.T.transcendenceDegree_ratios_cuspForms_components D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hE hc hcg⟩

end GlobalTheory.BigRec
