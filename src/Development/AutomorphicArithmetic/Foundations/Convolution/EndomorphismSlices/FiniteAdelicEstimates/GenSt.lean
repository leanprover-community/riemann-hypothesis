import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.MultOfKer
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.EntEmpty
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.MemULOfSplit

section
theorem UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 :
    UpperTheory.Zero.ConvolutionTheory.EB.SphComm2 := by
  intro E _ _ _ a b w f f' hf hf'
  exact PositivityTheory.Rg.BcB.F.sphComm E a b w f f' hf hf'
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

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private theorem position_sph (Z T : Finset (Pl E)) (L : Lv a b Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (w : Pl E) (hw : w ∉ Z) : IsHecke (K2 a b w) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  unfold intersection_update_fsHerm_neg_one
  rw [if_neg hw]
  split_ifs
  · exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (e w)
  · exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w .one

private theorem position_Z (Z T : Finset (Pl E)) (L : Lv a b Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (w : Pl E) (hw : w ∈ Z) : intersection_update_fsHerm_neg_one Z T L.ln e w = L.ln w := by
  unfold intersection_update_fsHerm_neg_one
  rw [if_pos hw]

private theorem position_comm (Z T T' : Finset (Pl E)) (L : Lv a b Z) (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T L.ln e w) (intersection_update_fsHerm_neg_one Z T' L.ln e' w) =
      PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T' L.ln e' w) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  by_cases hw : w ∈ Z
  · rw [position_Z Z T L e w hw, position_Z Z T' L e' w hw]
  · exact UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 E a b w _ _ (position_sph Z T L e w hw) (position_sph Z T' L e' w hw)

private theorem position_comm_star (Z T T' : Finset (Pl E)) (L : Lv a b Z) (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T L.ln e w) (lfStar (intersection_update_fsHerm_neg_one Z T' L.ln e' w)) =
      PositivityTheory.Rg.BcN.F2.mconv (lfStar (intersection_update_fsHerm_neg_one Z T' L.ln e' w)) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  have hl := UpperTheory.Zero.ConvolutionTheory.EB.locAlg E a b Z L w
  by_cases hw : w ∈ Z
  · rw [position_Z Z T L e w hw, position_Z Z T' L e' w hw, hl.2.1]
  · exact UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 E a b w _ _ (position_sph Z T L e w hw)
      ((hl.2.2.2.2 _ (position_sph Z T' L e' w hw)).2.2)

theorem _root_.UpperTheory.Zero.ConvolutionTheory.EB.hkComm :
    UpperTheory.Zero.ConvolutionTheory.EB.HkComm := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ T T' e₁ e₂ e₁' e₂'
  have hst := UpperTheory.Zero.ConvolutionTheory.EB.positionTest E a b S Z L hZ
  have ht : ∀ (T : Finset (Pl E)) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))), IsTestP (intersection_update_fsHerm_neg_one Z T L.ln e) :=
    fun T e => (hst.2.2 L.ln hst.1).2 T e
  have hf := (UpperTheory.Zero.ConvolutionTheory.EB.ffAlg E a b l₁ l₂ D A S hS).2
  have h1 := hf _ _ (ht T e₁) (ht T e₂)
  have h2 := hf _ _ (ht T' e₁') (ht T' e₂')
  have hstar := h2.2.1
  refine ⟨?_, ?_⟩
  · show mulF A.ν (A.ff S _ _) (A.ff S _ _) = mulF A.ν (A.ff S _ _) (A.ff S _ _)
    rw [h1.2.2.2.2 _ _ (ht T' e₁') (ht T' e₂'), h2.2.2.2.2 _ _ (ht T e₁) (ht T e₂)]
    simp only [position_comm Z T T' L e₁ e₁', position_comm Z T T' L e₂ e₂']
  · show mulF A.ν (A.ff S _ _) (adjF (A.ff S _ _)) = mulF A.ν (adjF (A.ff S _ _)) (A.ff S _ _)
    rw [hstar]
    have hs := hf _ _ h2.2.2.1 h2.2.2.2.1
    rw [h1.2.2.2.2 _ _ h2.2.2.1 h2.2.2.2.1, hs.2.2.2.2 _ _ (ht T e₁) (ht T e₂)]
    simp only [position_comm_star Z T T' L e₁ e₁', position_comm_star Z T T' L e₂ e₂']

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

theorem genSt : GenSt := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ T e₁ e₂
  have hPt := ptOk E a b l₁ l₂ D A
  have hMul := hkMul E a b l₁ l₂ D A S Z L hS hZ
  have hComm := hkComm E a b l₁ l₂ D A S Z L hS hZ
  have hidm : ∀ e e', A.hk S L ∅ e e' = A.idm S L := hMul.2.2.2.2.1
  have hfin : ∀ T' e e', IsFinM (A.hk S L T' e e') := fun T' e e' => (hMul.2.2.2.2.2.2.1 T' e e').1

  have hform : ∀ γ : Gam a b S Z, ∃ wa wb T' e e',
      A.gen S L T e₁ e₂ γ = A.pt wa wb (A.hk S L T' e e') := by
    rintro (_ | x | x | _)
    · exact ⟨_, _, ∅, fun _ => .one, fun _ => .one, by
        rw [hidm]; rfl⟩
    · exact ⟨_, _, ∅, fun _ => .one, fun _ => .one, by
        rw [hidm]; rfl⟩
    · exact ⟨_, _, _, _, _, rfl⟩
    · exact ⟨_, _, _, _, _, rfl⟩
  have hok : ∀ γ, (A.gen S L T e₁ e₂ γ).Ok := by
    intro γ
    obtain ⟨wa, wb, T', e, e', h⟩ := hform γ
    rw [h]
    exact hPt.2.2.1 wa wb _ (hfin T' e e')
  refine ⟨⟨hok, ?_, ?_⟩, ?_⟩
  · intro x y
    obtain ⟨wa, wb, T', e, e', h⟩ := hform x
    obtain ⟨wa', wb', T'', f, f', h'⟩ := hform y
    have hx := hok x
    have hy := hok y
    rw [h] at hx ⊢
    rw [h'] at hy ⊢
    exact BlockFiniteConvolution.blkComm₀ E A.blk _ _ hx hy (hComm T' T'' e e' f f').1
  · intro x y
    obtain ⟨wa, wb, T', e, e', h⟩ := hform x
    obtain ⟨wa', wb', T'', f, f', h'⟩ := hform y
    have hx := hok x
    have hy := hok y
    rw [h] at hx ⊢
    rw [h'] at hy ⊢
    have hop := BlockFiniteConvolution.blkOp₀ E A.blk _ _ hy hy
    rw [ContinuousLinearMap.star_eq_adjoint, ← hop.2.2.2.2.2.1]
    exact BlockFiniteConvolution.blkComm₀ E A.blk _ _ hx hop.2.2.2.2.1 (hComm T' T'' e e' f f').2
  · haveI : Countable (Pl E) := Small.countable_pl E
    infer_instance

end UpperTheory.Zero.ConvolutionTheory.EB
end
end
