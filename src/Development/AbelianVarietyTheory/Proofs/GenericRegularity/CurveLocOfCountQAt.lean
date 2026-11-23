module

public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BirationalOfFormRatiosFullTrdegStatement
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory

theorem curveLoc_of_countQAt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), ∀ (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), CountQAtSt h j hj hG hT → ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w), ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w), (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q → RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧ phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a := by
  intro D T h j hj hG hT hQ ka wL wF G S g0 la hH Z r
  exact CurveLoc.loc_of_bir (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
    (birAt_of h j hj hG hT G ((GlobalTheory.T.birational_of_formRatios_full_trdeg D T h j hj hG ka wL wF G).2 hH.2.1) Z)
    (hQ ka wL wF G S g0 la hH Z) r

end GlobalTheory
