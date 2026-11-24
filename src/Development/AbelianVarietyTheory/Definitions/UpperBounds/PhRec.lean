module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.GlobalFamilyData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.BigRec

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

def PhRec {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (σ : T.Q.c.F →+* ℂ) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (i : ℕ)
    (et : (recB h.toLawsCore).Cusp j (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j i)) (c : ℝ) : Prop :=
  ∀ k : (T.U j σ).Comp, ∃ ph : Frame ((T.U j σ).X k).Ψ D.R.r → ℝ,
    (∀ x ∈ ((T.U j σ).X k).dom, 0 ≤ ph x) ∧
    (∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ ((T.U j σ).X k).dom, ((T.U j σ).X k).la1 x < ε0 →
      ca / ((T.U j σ).X k).la1 x ^ 2 ≤ ph x) ∧
    InterpolationModelInequalities ((T.U j σ).X k) (laU (T.U j σ) (wtA wL) wL.n k)
      (laU (T.U j σ) (wtA (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j i)) (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j i).n k)
      (fun m => rdU (T.U j σ) (w m).1 k) (rdU (T.U j σ) et.1 k) c i ph

end GlobalTheory.BigRec
