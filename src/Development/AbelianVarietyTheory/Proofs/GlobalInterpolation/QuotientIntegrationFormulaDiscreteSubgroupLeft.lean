module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.QuotDiscrete


open MeasureTheory in
open scoped ENNReal in
theorem _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  have h1 : μ.inv = Measure.haarScalarFactor μ.inv μ • μ :=
    Measure.isMulLeftInvariant_eq_smul μ.inv μ
  set c := Measure.haarScalarFactor μ.inv μ with hc
  have h2 : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := (Measure.inv_inv μ).symm
      _ = (c • μ).inv := by rw [← h1]
      _ = c • μ.inv := by
          ext s _
          simp [Measure.inv_apply]
      _ = (c * c) • μ := by rw [h1, smul_smul]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK1
  have hfin : μ K < ∞ := hK.measure_lt_top
  have h3 : ((c * c : NNReal) : ℝ≥0∞) * μ K = 1 * μ K := by
    rw [one_mul]
    conv_rhs => rw [h2]
    rfl
  have h4 : ((c * c : NNReal) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h3
  have h5 : ((c : ℝ) * c) = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have hc0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  exact ⟨by rw [h1, h6, one_smul]⟩


end GlobalTheory.QuotDiscrete
