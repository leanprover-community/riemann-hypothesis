module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt maMeasure isPotentialAdd
  isPotentialRsmul isPotential_ofFun isPshAdd maMeasureMono maMeasure_thm massIndep mIntegrableCont
  pot_contDiffAt_two)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_formNonneg {A : FinHolAtlas D X} {V : Set X} (hV : interior Vᶜ = ∅)
    {P : LocPot X} (hP : IsPotential A P) (hnn : FormNonneg A V P) : IsPsh A P := by
  intro x j y hy w
  by_contra hneg
  push Not at hneg
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  have h2 := pot_contDiffAt_two hP x j hy.1 hy.2
  have hc : ContinuousAt (fun z => levi (P.φ x ∘ (A.chart j).symm) z w) y := by
    have h0 := ((h2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt
    unfold levi
    exact (((h0.clm_apply continuousAt_const).clm_apply continuousAt_const).add
      ((h0.clm_apply continuousAt_const).clm_apply continuousAt_const)).div_const 4
  have hev : ∀ᶠ z in 𝓝 y, levi (P.φ x ∘ (A.chart j).symm) z w < 0 ∧
      z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x :=
    (hc.eventually (eventually_lt_nhds hneg)).and (hO.mem_nhds hy)
  obtain ⟨N, hNsub, hNo, hyN⟩ := mem_nhds_iff.1 hev
  have himg : IsOpen ((A.chart j).symm '' N) :=
    (A.chart j).isOpen_image_symm_of_subset_target hNo fun z hz => (hNsub hz).2.1
  have hsub : (A.chart j).symm '' N ⊆ Vᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzV
    have h := hnn x j z ⟨(hNsub hz).2.1, hzV, (hNsub hz).2.2⟩ w
    linarith [(hNsub hz).1]
  have hmem : (A.chart j).symm y ∈ interior Vᶜ := interior_maximal hsub himg ⟨y, hyN, rfl⟩
  rw [hV] at hmem
  exact hmem

end GroundTheory.Heights₂.Heights.AnalyticLimit
