module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelColumns

theorem colOp : KerBasic → CvTest → KernelL2RowsColumns → KerMul → ColOp := by
  intro hB hC hL hM X ι _ ψ hψ
  classical
  refine ⟨?_, ?_⟩
  · intro y j
    have hm : MemLp (fun x => ker X.Γ ψ x y) 2 X.ν := (hL X ψ hψ).1 y
    refine ⟨WithLp.toLp 2 (Pi.single j (hm.toLp _)), ?_, ?_⟩
    · have e : (WithLp.toLp 2 (Pi.single j (hm.toLp _)) : X.Hs ι) j = hm.toLp _ := by
        simp
      rw [e]
      exact hm.coeFn_toLp
    · intro l hl
      ext1
      simp [Pi.single_eq_of_ne hl]
  · intro Φ T hΦ hT y j u hu
    have key : ∀ i, (T u i : X.G → ℂ) =ᵐ[X.ν] fun x => ker X.Γ (cv X.μ (Φ i j) ψ) x y := by
      intro i
      filter_upwards [hT u i] with x hx
      rw [hx, Finset.sum_eq_single j]
      · rw [← hM X (Φ i j) ψ (hΦ i j) hψ x y]
        apply integral_congr_ae
        filter_upwards [hu.1] with z hz
        rw [hz]
      · intro l _ hl
        have h0 : (u l : X.G → ℂ) =ᵐ[X.ν] 0 := by
          rw [hu.2 l hl]
          exact Lp.coeFn_zero _ _ _
        have : (fun z => ker X.Γ (Φ i l) x z * (u l : X.G → ℂ) z) =ᵐ[X.ν] fun _ => 0 := by
          filter_upwards [h0] with z hz
          rw [hz]
          simp
        rw [integral_congr_ae this]
        simp
      · intro h
        exact absurd (Finset.mem_univ j) h
    refine ⟨key, ?_⟩
    intro x i v hv
    have hc := hC X (Φ i j) ψ (hΦ i j) hψ
    have ha := (hB X ψ hψ).2.2.2.1
    have hadj := (hB X ψ hψ).2.2.2.2.1
    rw [PiLp.inner_apply, Finset.sum_eq_single i]
    · rw [L2.inner_def, ← hM X (adj ψ) (cv X.μ (Φ i j) ψ) ha hc.1 x y]
      apply integral_congr_ae
      filter_upwards [hv.1, key i] with z hz1 hz2
      rw [hz1, hz2, RCLike.inner_apply, hadj x z, mul_comm]
    · intro l _ hl
      rw [hv.2 l hl]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h

end GlobalTheory.CompanionTheory.KernelColumns

end
