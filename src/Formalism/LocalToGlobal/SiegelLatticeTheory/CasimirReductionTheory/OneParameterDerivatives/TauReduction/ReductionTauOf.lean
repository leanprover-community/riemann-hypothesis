module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.Imports

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Matrix Filter Topology

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem reductionTau_of (h3 : SubmoduleExists) (h6 : SizesLocallyComparable) (h7 : InfimumContinuousFamily)
    (h8 : MinkowskiSubmodule) (h9 : LatticeVectorsBoundedBelow) (h10 : HeightsPositive) : ReductionTau := by
  unfold Formalism.L2.SG.LitS.ReductionTau
  intro I hn
  refine ⟨?_, fun x => ?_⟩
  · exact h7 I.GA (Sub I) (fun x s => size I s) (fun x => h3 I hn x)
      (fun x s => Real.rpow_nonneg (h10 I x s).le _) (fun x r hr => h6 I x r hr)
  · obtain ⟨c, hc, hc8⟩ := h8 I
    obtain ⟨l, hl, hl9⟩ := h9 I x
    have hδ : ∀ s : Sub I x, Real.sqrt (l / c) ≤ size I s := by
      intro s
      obtain ⟨u, huB, hu0, hsum⟩ := hc8 x s
      have h1 := hl9 u (s.B_lat huB) hu0
      have hs0 : 0 ≤ size I s := Real.rpow_nonneg (h10 I x s).le _
      exact Real.sqrt_le_iff.2 ⟨hs0, (div_le_iff₀ hc).2 (by linarith)⟩
    haveI := h3 I hn x
    exact ⟨lt_min (by norm_num) (lt_of_lt_of_le (Real.sqrt_pos.2 (div_pos hl hc)) (le_ciInf hδ)),
      min_le_left _ _⟩

end Formalism.L2.SG.Pf.Tau
