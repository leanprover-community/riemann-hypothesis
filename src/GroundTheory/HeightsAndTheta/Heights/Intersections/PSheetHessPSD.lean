module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StSheetHessPSD
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemiPosTwist
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterOsgood

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ComplexOrder

theorem analyticAt_of_eventually_differentiableAt {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {e : ℕ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (h : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') : AnalyticAt ℂ γ y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp h
  rw [analyticAt_pi_iff]
  intro p
  exact osgood e U (fun y' => γ y' p) hUo
    (fun y' hy' => ((differentiableAt_pi.mp (hU y' hy')) p).differentiableWithinAt) y hyU

theorem SheetHessPSD.proof : SheetHessPSD.Statement := by
  intro K _ ι _ P e Ψ M y w γ hM hPos hγ
  have hev := hγ.2
  have hγy : γ y ∈ mcPts P := hev.self_of_nhds.2.1
  have hz : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := hγy.1
  have han : AnalyticAt ℂ γ y :=
    analyticAt_of_eventually_differentiableAt (hev.mono fun _ h => h.1)
  have hUo := SemipositiveTwist.isOpen_noZeroBlock (ι := ι)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (M.h z)) (γ y) :=
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos _ hz).ne'
  have hcomp : (fun y' => Real.log (M.h (γ y'))) = (fun z => Real.log (M.h z)) ∘ γ := rfl
  have hC2 : ContDiffAt ℝ 2 (fun y' => Real.log (M.h (γ y'))) y := by
    rw [hcomp]
    exact hlog.comp y (han.restrictScalars.contDiffAt)
  show (ReciprocityTheory.AnForm.hessC (fun y' => Real.log (M.h (γ y'))) y).PosSemidef
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ y hC2 fun x => ?_
  rw [hcomp, ReciprocityTheory.AnForm.levi_comp x han hlog]
  have hL := SemipositiveTwist.laplacian_line_eq_levi hlog (fderiv ℂ γ y x)
  have hΔ := hPos (γ y) hz (fderiv ℂ γ y x)
  linarith

end GroundTheory.Heights₂.Heights.Inter
