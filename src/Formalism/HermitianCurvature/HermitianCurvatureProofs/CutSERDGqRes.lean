module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_group_residue : RDGqRes := by
  intro k r Wp Wq _ _ _ _ _ _ D q hq
  obtain ⟨hq1, hq2⟩ := hq
  have hsec := (D.sec.2 q.2 hq2).1
  have hU : B2.embWb k r (D.μsec q.2) ∈ B2.UWb k r :=
    TwoByOneBlock.emb_mem_UWb (k := k) (r := r) hsec
  have hv := TwoByOneBlock.sec_vec D.z_mem D.z'_mem D.sec hq2
  refine ⟨(q.1, B2.embWb k r (D.μsec q.2)), ?_, ?_⟩
  · refine ⟨hq1, ⟨hU.1, fun a _ => hU.2 a⟩, ?_⟩
    show 0 < Complex.normSq (zetaL k r D.z D.z' (Fin.last r) (B2.embWb k r (D.μsec q.2))) - Tz k r D.z * Tz k r D.z'
    have hz : zetaL k r D.z D.z' (Fin.last r) (B2.embWb k r (D.μsec q.2)) = q.2 := by
      unfold zetaL fvec
      simpa using hv.2.2
    rw [hz]
    linarith
  · refine ⟨((∏ a : Fin r, if (a : ℕ) < ((Fin.last r : Fin (r + 1)) : ℕ) then ‖q.1 a‖ ^ (Mdim k r a - 1) else 1 : ℝ) : ℂ), ?_, ?_⟩
    · rw [Complex.ofReal_ne_zero]
      refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
      split_ifs
      · exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hq1 a))
      · exact one_ne_zero
    · intro J _
      have hcell : wCell k r (Fin.last r) q.1 * B2.embWb k r (D.μsec q.2) = B.gq D q := by
        rw [Rad.wCell_last_eq]
        exact ((TwoByOneBlock.bigCellFactor k r q.1 (D.μsec q.2)).1).symm
      unfold resG
      rw [hcell]

end Formalism.FourierDecayAlt.P.CutSE
