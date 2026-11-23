module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankLowerBoundCuspFormVanishingLowCoeff
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.finrank_lower_bound_cuspForm_vanishing_low_coeff : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → MggOnto h j CR Tn c (addL wF wL Tn) → δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j) ≤ Module.finrank ℂ (R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))) := by
  first | exact @GlobalTheory.LowerBound.lower_bound | exact GlobalTheory.LowerBound.lower_bound | (intros; apply GlobalTheory.LowerBound.lower_bound <;> assumption)
