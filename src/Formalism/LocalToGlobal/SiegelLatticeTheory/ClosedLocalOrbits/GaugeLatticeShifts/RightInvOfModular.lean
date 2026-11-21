import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
import Formalism.RealPlaceAnalysis.FinalF

section
noncomputable section

open MeasureTheory Topology Filter
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

local notation "Δ" => Measure.modularCharacterFun (G := G)

theorem map_right (g : G) : (Measure.haar : Measure G).map (· * g) = Δ g • (Measure.haar : Measure G) :=
  Measure.map_right_mul_eq_modularCharacterFun_smul _ g

theorem haar_preimage (g : G) {A : Set G} (hA : MeasurableSet A) :
    (Measure.haar : Measure G) ((· * g) ⁻¹' A) = (Δ g : ℝ≥0∞) * (Measure.haar : Measure G) A := by
  have h : ((Measure.haar : Measure G).map (· * g)) A = (Δ g • (Measure.haar : Measure G)) A := by rw [map_right]
  rw [Measure.map_apply (measurable_mul_const g) hA] at h
  rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

theorem exists_compact_pos : ∃ C : Set G, IsCompact C ∧ 0 < (Measure.haar : Measure G) C ∧
    (Measure.haar : Measure G) C ≠ ⊤ := by
  obtain ⟨C, hC, h1⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨C, hC, ?_, hC.measure_lt_top.ne⟩
  exact Measure.measure_pos_of_nonempty_interior _ ⟨1, mem_interior_iff_mem_nhds.2 h1⟩


theorem eventually_lt (ε : ℝ) (hε : 0 < ε) : ∀ᶠ h in 𝓝 (1 : G), (Δ h : ℝ) < 1 + ε := by
  obtain ⟨C, hC, hpos, hfin⟩ := exists_compact_pos (G := G)
  have hlt : (Measure.haar : Measure G) C < ENNReal.ofReal (1 + ε) * (Measure.haar : Measure G) C := by
    have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal (1 + ε) := by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have := ENNReal.mul_lt_mul_right hpos.ne' hfin h1
    simpa [mul_comm] using this
  obtain ⟨U, hCU, hU, hUlt⟩ := Set.exists_isOpen_lt_of_lt C _ hlt
  obtain ⟨V, hV, hCV⟩ := compact_open_separated_mul_right hC hU hCU
  have hV' : ∀ᶠ h in 𝓝 (1 : G), h⁻¹ ∈ V := by
    have ht : Tendsto (fun h : G => h⁻¹) (𝓝 1) (𝓝 1) := by simpa using continuous_inv.tendsto (1 : G)
    exact ht hV
  filter_upwards [hV'] with h hh
  have hsub : (· * h) ⁻¹' C ⊆ U := by
    intro x hx
    apply hCV
    exact ⟨x * h, hx, h⁻¹, hh, by group⟩
  have h2 : (Δ h : ℝ≥0∞) * (Measure.haar : Measure G) C < ENNReal.ofReal (1 + ε) * (Measure.haar : Measure G) C := by
    rw [← haar_preimage h hC.isClosed.measurableSet]
    exact lt_of_le_of_lt (measure_mono hsub) hUlt
  have h3 : (Δ h : ℝ≥0∞) < ENNReal.ofReal (1 + ε) :=
    not_le.1 fun hle => lt_irrefl _ (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle zero_le) h2)
  rw [← ENNReal.ofReal_coe_nnreal] at h3
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 h3



end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
end
end

section
noncomputable section

open MeasureTheory Topology Filter Matrix
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

theorem inS_pres {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a : ℕ) :
    ∀ y ∈ spanLt e a, g *ᵥ y ∈ spanLt e a := by
  intro y hy
  have hle : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin g) := by
    unfold spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have hb' : (b : ℕ) < a := hb
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    have e1 : g *ᵥ e b = e b + (g - 1) *ᵥ e b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e1]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨b, hb', rfl⟩) ?_
    refine Submodule.span_mono ?_ (hg.1 b)
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, lt_trans hc hb', rfl⟩
  exact hle hy

theorem inS_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hh : InS e z h) : InS e z (g * h) := by
  have key : ∀ v : Fin n → ℂ, (g * h - 1) *ᵥ v = g *ᵥ ((h - 1) *ᵥ v) + (g - 1) *ᵥ v := fun v => by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  refine ⟨fun a => ?_, ?_⟩
  · rw [key]
    exact Submodule.add_mem _ (inS_pres e z hg a.1 _ (hh.1 a)) (hg.1 a)
  · rw [key]
    exact Submodule.add_mem _ (inS_pres e z hg r _ hh.2) hg.2

theorem inS_one : InS e z (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨fun a => by rw [sub_self, Matrix.zero_mulVec]; exact Submodule.zero_mem _,
    by rw [sub_self, Matrix.zero_mulVec]; exact Submodule.zero_mem _⟩

def SG : Subgroup (Formalism.REAL.UJ ε) where
  carrier := SLoc ε e z
  one_mem' := inS_one e z
  mul_mem' {a b} ha hb := inS_mul e z ha hb
  inv_mem' {a} ha := Formalism.L2.SG.RealObj.InfCut.inS_inv _ _ (Formalism.MainNotions.S.uMat a) (Formalism.MainNotions.S.uMat a⁻¹)
    (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' a) ha

theorem coe_SG : (SG ε e z : Set (Formalism.REAL.UJ ε)) = SLoc ε e z := rfl

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  ((Formalism.REAL.uJEmb n ε).1).continuous

theorem SG_closed : IsClosed (SG ε e z : Set (Formalism.REAL.UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ v) := fun v =>
    ((continuous_uMat ε).sub continuous_const).matrix_mulVec continuous_const
  have e1 : (SG ε e z : Set (Formalism.REAL.UJ ε)) =
      (⋂ a : Fin r, (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ e a) ⁻¹' (spanLt e a.1 : Set (Fin n → ℂ))) ∩
        (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ z) ⁻¹' (spanLt e r : Set (Fin n → ℂ)) := by
    ext g
    simp only [coe_SG, SLoc, InS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe]
  rw [e1]
  exact (isClosed_iInter fun a => (Submodule.closed_of_finiteDimensional _).preimage (hc _)).inter
    ((Submodule.closed_of_finiteDimensional _).preimage (hc _))

section Sub

variable {ε e z}

local notation "SS" => (SG ε e z)

instance instLCSG : LocallyCompactSpace SS := (SG_closed ε e z).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance instSCSG : SecondCountableTopology SS := Topology.IsEmbedding.subtypeVal.secondCountableTopology


end Sub

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
end
end
