module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RealisationValuesEqValuedPointOrders
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.realisation_values_eq_valuedPoint_orders : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → ∀ (δ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (T.Q.Dw j) → ℤ), OrdTie hG δ (trivialClassCondition (T.Q.Xo j) T.Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) → ∀ la (ζ : PtsG G la), ∃ (Z : Comp (T.Q.Xo j) T.Q.c) (v : AddValuation (Om Z) (WithTop ℤ)), ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v ∧ ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := T.Q.c.F) v la ∧ ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), (evC hG Z F.1 = 0 → (hw la ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) = 0) ∧ (evC hG Z F.1 ≠ 0 → (hw la ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) ≠ 0 ∧ vV (hw la ζ).T.V ((hw la ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) = ordC (δ Z v) v (wtZ (wtA w) w.n) (valC hG (wtA w) w.n F.1 Z)) := by
  first | exact @GlobalTheory.RealisationValues.values_eq_orders | exact GlobalTheory.RealisationValues.values_eq_orders | (intros; apply GlobalTheory.RealisationValues.values_eq_orders <;> assumption)
