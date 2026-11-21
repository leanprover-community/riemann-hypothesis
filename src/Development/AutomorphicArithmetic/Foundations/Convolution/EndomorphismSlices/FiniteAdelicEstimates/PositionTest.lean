import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem locAlg : LocAlg := by
  intro E _ _ _ a b Z L w
  have hK2 : K2 a b w = (KGL w a).prod (KGL w b) := rfl
  have hop : IsOpen (((L.L₁ w).prod (L.L₂ w) : Subgroup _) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (L.open₁ w).prod (L.open₂ w)
  have hle : (L.L₁ w).prod (L.L₂ w) ≤ K2 a b w := Subgroup.prod_mono (L.le₁ w) (L.le₂ w)
  have hKop : IsOpen ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
    rw [hK2, Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  have hln : L.ln w = idem ((L.L₁ w).prod (L.L₂ w)) := rfl
  have hKi : idem (K2 a b w) = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 := by
    funext y
    simp only [idem, Subgroup.relIndex_self, Nat.cast_one]
    rfl
  obtain ⟨h1, h2, h3⟩ := PositivityTheory.Rg.BcB.F.idemAlg E a b w _ hop hle
  obtain ⟨-, -, k3⟩ := PositivityTheory.Rg.BcB.F.idemAlg E a b w _ hKop le_rfl
  refine ⟨hln ▸ h1, hln ▸ h2, fun hw => ?_, fun f hf => ?_, fun f hf => ?_⟩
  · obtain ⟨e₁, e₂⟩ := L.off w hw
    rw [hln, e₁, e₂, ← hK2, hKi]
  · rw [hln]
    exact ⟨(h3 f hf).2.1, (h3 f hf).1⟩
  · rw [← hKi]
    exact ⟨(k3 f hf).2.1, (k3 f hf).1, (k3 f hf).2.2⟩

end UpperTheory.Zero.ConvolutionTheory.EB

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem levelFam_of {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (Z : Finset (Pl E))
    (K : ∀ w : Pl E, Subgroup (GLw n w)) (hZ : ∀ w ∈ Z, IsSplitAt w) (ho : ∀ w, IsOpen (K w : Set (GLw n w)))
    (hle : ∀ w, K w ≤ GlobalTheory.LFun.KGL w n) (hoff : ∀ w ∉ Z, K w = GlobalTheory.LFun.KGL w n) :
    IsLevelFam (GlobalTheory.BCT.thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) K := by
  refine ⟨fun w => ?_, ?_⟩
  · by_cases hw : w ∈ Z
    · refine ⟨ho w, hle w, fun k hk => ?_⟩
      have h : GlobalTheory.BCT.thL n w = MonoidHom.id _ := by
        unfold GlobalTheory.BCT.thL
        rw [if_pos (hZ w hw)]
      rw [h]
      exact hk
    · rw [hoff w hw]
      exact PositivityTheory.Rg.BcB.F.LocOk.lev_K n w
  · filter_upwards [Z.finite_toSet.compl_mem_cofinite] with w hw
    exact hoff w hw

theorem positionTest : PositionTest := by
  intro E _ _ _ a b S Z L hS
  have hZ : ∀ w ∈ Z, IsSplitAt w := fun w hw => (hS w hw).2
  have h₁ := levelFam_of Z L.L₁ hZ L.open₁ L.le₁ fun w hw => (L.off w hw).1
  have h₂ := levelFam_of Z L.L₂ hZ L.open₂ L.le₂ fun w hw => (L.off w hw).2
  have hH : ∀ w, IsHecke ((L.L₁ w).prod (L.L₂ w)) (L.ln w) := fun w => (locAlg E a b Z L w).1
  have hI : ∀ w ∉ Z, L.ln w = (K2 a b w : Set _).indicator 1 := fun w hw => (locAlg E a b Z L w).2.2.1 hw
  have hK : ∀ w ∉ Z, (L.L₁ w).prod (L.L₂ w) = K2 a b w := by
    intro w hw
    rw [(L.off w hw).1, (L.off w hw).2]
  refine ⟨fun w _ => hH w, ⟨L.L₁, L.L₂, h₁, h₂, hH, ?_⟩, fun φ hφ => ⟨fun w hw => ?_, fun T e =>
    ⟨L.L₁, L.L₂, h₁, h₂, fun w => ?_, ?_⟩⟩⟩
  · filter_upwards [Z.finite_toSet.compl_mem_cofinite] with w hw
    exact hI w hw
  · have h := PositivityTheory.Rg.BcB.F.LocOk.prod_open_le (h₁.1 w) (h₂.1 w)
    exact ⟨_, h.1, h.2, hφ w hw⟩
  · by_cases hw : w ∈ Z
    · have h : intersection_update_fsHerm_neg_one Z T φ e w = φ w := if_pos hw
      rw [h]
      exact hφ w hw
    · by_cases hT : w ∈ T
      · have h : intersection_update_fsHerm_neg_one Z T φ e w = fn2 a b w (e w) := by
          unfold intersection_update_fsHerm_neg_one
          rw [if_neg hw, if_pos hT]
        rw [h]
        show GlobalTheory.BCT.IsHecke ((L.L₁ w).prod (L.L₂ w)) _
        rw [hK w hw]
        exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (e w)
      · have h : intersection_update_fsHerm_neg_one Z T φ e w = L.ln w := by
          unfold intersection_update_fsHerm_neg_one
          rw [if_neg hw, if_neg hT, hI w hw]
        rw [h]
        exact hH w
  · filter_upwards [(Z ∪ T).finite_toSet.compl_mem_cofinite] with w hw
    have hw' : w ∉ Z ∧ w ∉ T := by simpa using hw
    unfold intersection_update_fsHerm_neg_one
    rw [if_neg hw'.1, if_neg hw'.2]

end UpperTheory.Zero.ConvolutionTheory.EB
end
end
