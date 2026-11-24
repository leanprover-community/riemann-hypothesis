module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamDeriv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PoinPt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

open UpperTheory.V.Lit.Dr
open Set ContinuousAlternatingMap
open scoped ContDiff

theorem UpperTheory.V.Lit.Dr.poincare :
    Poincare := by
  intro V F _ _ _ _ _ _ Y hY hconv q w hw hd
  rcases Y.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨0, contDiffOn_empty, fun p hp => hp.elim⟩
  have hseg : ContDiff ℝ ∞ (fun z : V × ℝ => p₀ + z.2 • (z.1 - p₀)) := by fun_prop
  set U : Set (V × ℝ) := (fun z : V × ℝ => p₀ + z.2 • (z.1 - p₀)) ⁻¹' Y with hU
  have hUo : IsOpen U := hY.preimage hseg.continuous
  have hmem : ∀ p ∈ Y, ∀ t ∈ Icc (0 : ℝ) 1, p₀ + t • (p - p₀) ∈ Y :=
    fun p hp t ht => hconv.add_smul_sub_mem hp₀ hp ht
  let Φ : V × ℝ → V [⋀^Fin q]→L[ℝ] F :=
    fun z => z.2 ^ q • (w (p₀ + z.2 • (z.1 - p₀))).curryLeft (z.1 - p₀)
  have hΦ : ContDiffOn ℝ ∞ Φ U := by
    have h1 : ContDiffOn ℝ ∞ (fun z : V × ℝ => w (p₀ + z.2 • (z.1 - p₀))) U :=
      hw.comp hseg.contDiffOn fun z hz => hz
    have h2 : ContDiffOn ℝ ∞ (fun z : V × ℝ => (w (p₀ + z.2 • (z.1 - p₀))).curryLeft) U :=
      (curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap.contDiff.comp_contDiffOn h1
    exact (contDiff_snd.pow q).contDiffOn.smul
      (h2.clm_apply (contDiff_fst.sub contDiff_const).contDiffOn)
  refine ⟨fun p => ∫ t in (0 : ℝ)..1, Φ (p, t),
    paramSmooth V _ Y U Φ hY hUo (fun z hz => hmem z.1 hz.1 z.2 hz.2) hΦ, fun p hp => ?_⟩
  obtain ⟨hc, hD⟩ := paramDeriv V _ p U Φ hUo (hmem p hp) hΦ
  have hI := hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one
  have hI' := ((alternatizeUncurryFinCLM ℝ V F).continuous.comp_continuousOn hc).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) zero_le_one
  have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => r ^ (q + 1) • w (p₀ + r • (p - p₀)))
      (alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => Φ (x, t)) p)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hm := hmem p hp t ht
    exact poinPt V F q w p₀ p t
      ((hw.contDiffAt (hY.mem_nhds hm)).differentiableAt (by simp)) (hd _ hm)
  have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hI'
  rw [(alternatizeUncurryFinCLM ℝ V F).intervalIntegral_comp_comm hI, ← hD.fderiv] at h3
  refine Eq.trans h3 ?_
  simp
