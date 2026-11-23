module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

theorem SemiposTwist.proof : SemiposTwist.Statement := by
  intro K _ ι _ P0 P L p q hL
  set U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hU
  have hUo : IsOpen U := by
    have e : U = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
      ext z
      simp [hU]
    rw [e]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_iUnion fun i => (continuous_apply _).isOpen_preimage _ isOpen_ne
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  have hsm : IsSmoothHerm (HermLine.zcomb L (fsH ι) q p) := by
    have e : (HermLine.zcomb L (fsH ι) q p).h = fun z => L.h z ^ q * (fsH ι).h z ^ p := by
      funext z
      show L.h z ^ (q : ℤ) * (fsH ι).h z ^ (p : ℤ) = _
      rw [zpow_natCast, zpow_natCast]
    unfold IsSmoothHerm
    rw [e]
    exact (hL.1.pow q).mul (hH.pow p)
  refine ⟨hsm, fun z hz w hw => ?_⟩
  have hzU : z ∈ U := hz.1
  have hlog : ∀ A : HermLine ι, IsSmoothHerm A → ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z :=
    fun A hA => ((hA.contDiffAt (hUo.mem_nhds hzU)).of_le (WithTop.coe_le_coe.2 le_top)).log
      (A.pos z hzU).ne'
  have h1 := hlog L hL.1
  have h2 := hlog (fsH ι) hH
  have hev : (fun y => Real.log ((HermLine.zcomb L (fsH ι) q p).h y)) =ᶠ[𝓝 z]
      fun y => (0 + (q : ℝ) * Real.log (L.h y)) + (p : ℝ) * Real.log ((fsH ι).h y) := by
    filter_upwards [hUo.mem_nhds hzU] with y hy
    show Real.log (L.h y ^ (q : ℤ) * (fsH ι).h y ^ (p : ℤ)) = _
    rw [Real.log_mul (zpow_pos (L.pos y hy) _).ne' (zpow_pos ((fsH ι).pos y hy) _).ne',
      Real.log_zpow, Real.log_zpow]
    push_cast
    ring
  have hLz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (L.h y)) z w := hL.2 z hz w hw
  have hHz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log ((fsH ι).h y)) z w :=
    FsLineLevi.proof K ι z w hzU
  have e1 := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => 0 + (q : ℝ) * Real.log (L.h y))
    (g := fun y => Real.log ((fsH ι).h y)) (p : ℝ) (contDiffAt_const.add (contDiffAt_const.mul h1)) h2 w
  have e2 := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ))
    (g := fun y => Real.log (L.h y)) (q : ℝ) contDiffAt_const h1 w
  have hl0 : ReciprocityTheory.AnForm.levi (fun _ => (0 : ℝ)) z w = 0 := by simp [ReciprocityTheory.AnForm.levi]
  change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev, e1, e2, hl0]
  have a1 := mul_nonneg (Nat.cast_nonneg (α := ℝ) q) hLz
  have a2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) hHz
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
