module

public import Formalism.HermitianCurvature.StatementTL
public import Formalism.FormalDegreeBessel.FinalBF
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

theorem big_cell_values : TL.CellVals := by
  intro k r Wp Wq _ _ _ _ _ Bs x hx
  obtain ⟨hc, hg, hG⟩ := hx
  obtain ⟨μ, -, hμ⟩ := (TwoByOneBlock.UWb_iff x.2).1 (NFRadRedA.glev_uwb hg)
  have hGV : wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by
    have h1 : wCell k r (Fin.last r) x.1 ∈ Glev k r 0 := by
      unfold wCell
      exact Qx3.wlist_glev hc _
    exact (Qx5.Glev_mul h1 (Qx4.glev0 hg.1)).1
  have hM : wCell k r (Fin.last r) x.1 * x.2 = bigCell k r x.1 μ := by
    rw [P5.Rad.wCell_last_eq, hμ, ← (bruhat_big_cell_factorization k r x.1 μ).1]
  rw [hM] at hGV ⊢
  set ζ := zetaL k r Bs.z Bs.z' (Fin.last r) x.2 with hζdef
  have hz : ζ = herm (Hb k) (μ *ᵥ wbPart k r Bs.z') (wbPart k r Bs.z) := by
    rw [hζdef, P5.Rad.zetaL_last, hμ]
    have e1 : B2.embWb k r μ *ᵥ Bs.z' = TwoByOneBlock.jV k r (μ *ᵥ wbPart k r Bs.z') := by
      conv_lhs => rw [← TwoByOneBlock.jV_wbPart Bs.z'_mem]
      exact TwoByOneBlock.emb_mulVec_jV _ _
    rw [e1]
    conv_lhs => rw [← TwoByOneBlock.jV_wbPart Bs.z_mem]
    rw [TwoByOneBlock.herm_jV]
  let d : Fin (r + 1) → ℂ := fun a => if h : (a : ℕ) < r then x.1 ⟨a, h⟩ else ζ
  have hZ : Zhat k r Bs.z Bs.z' (bigCell k r x.1 μ) = diagonal d := by
    rw [bigCellZhat k r Bs.z Bs.z' x.1 μ Bs.z_mem Bs.z'_mem]
    congr 1
    funext a
    by_cases h : (a : ℕ) < r
    · simp [d, h]
    · simp only [d, h, dite_false]
      rw [BigCellHermitian.herm_bigCell x.1 μ Bs.z_mem Bs.z'_mem, hz]
  have hD := BruhatBigCell.dmin_diag Bs.z Bs.z' _ d hZ
  have hTT : 0 < Tz k r Bs.z * Tz k r Bs.z' := mul_pos Bs.T_pos Bs.T'_pos
  have hζ : ζ ≠ 0 := by
    intro h0
    have : GGl k r Bs.z Bs.z' x.2 = Complex.normSq ζ - Tz k r Bs.z * Tz k r Bs.z' := rfl
    rw [this, h0, map_zero] at hG
    linarith
  have hd0 : ∀ a, d a ≠ 0 := by
    intro a
    by_cases h : (a : ℕ) < r
    · simp only [d, h, dite_true]
      exact hc _
    · simp only [d, h, dite_false]
      exact hζ
  have hP : ∏ a : Fin r, x.1 a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc a
  have hDr : Dmin k r Bs.z Bs.z' (bigCell k r x.1 μ) ⟨r, by omega⟩ = ∏ a : Fin r, x.1 a := by
    rw [hD]
    refine Finset.prod_congr rfl ?_
    intro i _
    have hi : ((Fin.castLE (by omega) i : Fin (r + 1)) : ℕ) < r := i.isLt
    simp only [d, hi, dite_true]
    rfl
  have hDl : Dmin k r Bs.z Bs.z' (bigCell k r x.1 μ) (Fin.last (r + 1)) = (∏ a : Fin r, x.1 a) * ζ := by
    rw [hD]
    show ∏ i : Fin (r + 1), d (Fin.castLE (by omega) i) = _
    rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl ?_
      intro i _
      have hi : ((Fin.castLE (by omega) i.castSucc : Fin (r + 1)) : ℕ) < r := i.isLt
      simp only [d, hi, dite_true]
      rfl
    · have hi : ¬ ((Fin.castLE (by omega) (Fin.last r) : Fin (r + 1)) : ℕ) < r := by simp
      simp only [d, hi, dite_false]
  have hGf : Gf k r Bs.z Bs.z' (bigCell k r x.1 μ) = Complex.normSq (∏ a : Fin r, x.1 a) * GGl k r Bs.z Bs.z' x.2 := by
    unfold Gf
    rw [hDl, hDr]
    show _ = _ * (Complex.normSq ζ - Tz k r Bs.z * Tz k r Bs.z')
    rw [map_mul]
    ring
  refine ⟨⟨hGV, ?_, ?_⟩, hDr, hDl, hGf⟩
  · rw [hGf]
    exact mul_pos (Complex.normSq_pos.mpr hP) hG
  · intro l _
    rw [hD]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _

end

end Formalism.FourierDecayAlt.P
