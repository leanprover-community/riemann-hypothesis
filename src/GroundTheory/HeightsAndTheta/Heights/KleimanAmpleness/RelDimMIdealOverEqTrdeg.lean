module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideRest
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockVecSegreJoin
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TrdegEqOfLeOfIsAlgebraic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open GroundTheory.Heights₂.Heights.NumbersDVR (segreVec)

theorem relDim_mIdealOver_eq_trdeg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ t : ℕ, Algebra.trdeg F (chartRingOver F y c) = t ∧
      relDim (mIdealOver F y) = ((t : ℕ) : WithBot (WithTop ℤ)) := by
  have hy := trdeg_quotient_mIdealOver (F := F) y c hc
  have _ : (mIdealOver F y).IsPrime := RingHom.ker_isPrime _
  have hfin := trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y)
  rw [hy] at hfin
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)
  have dimy : ringKrullDim (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) =
      ((t + Fintype.card K : ℕ) : ℕ∞) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hy, ht]
    simp
  refine ⟨t, ht, ?_⟩
  unfold relDim
  rw [dimy]
  have e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
      ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) =
      (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
  rw [e₁, Nat.cast_add, add_sub_cancel_right]
  rfl

theorem SegreDim.proof : SegreDim.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y hy
  choose c hc using hy
  obtain ⟨t, ht, hrel⟩ := relDim_mIdealOver_eq_trdeg (F := F) y c hc
  obtain ⟨t', ht', hrel'⟩ := relDim_mIdealOver_eq_trdeg (F := F) (segreJoin y) (segreChart c c)
    (segreChart_adm y (segreVec_ne_zero y hc) hc)
  have heq : chartRingOver F (segreJoin y) (segreChart c c) = chartRingOver F y c :=
    le_antisymm (segre_diag_le (S := F) y c) (chartRingOver_le_segre (S := F) y c c)
  rw [heq, ht] at ht'
  have htt : t = t' := by exact_mod_cast ht'
  rw [hrel, hrel', htt]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
