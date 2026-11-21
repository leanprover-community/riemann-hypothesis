import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GOfPrime
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.HaarIdx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TensTopRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TwoPrimes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MatRMulMatC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfAdaptedMod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ThetaEpsCases
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsAdaptedColumn

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped ENNReal

theorem massDataIndices_of (hA : MeasAAll) (hB : MeasBAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hX p
  obtain ⟨i, hi, hi0, hμi⟩ := hA X hb hK FdN FdN' u u' hX p
  obtain ⟨j, hj, hj0, hμj, hB0, hBt⟩ := hB X hb hK FdN FdN' u u' hX p
  refine ⟨?_, ?_⟩
  · show (X.measG.μGv p.1 (KvX X p)).toReal =
      (ggC D.R.rS D.R.k (gOf p) : ℝ) / ((nnC D.R.rS D.R.k (gOf p) : ℝ) * (ukC D.R.k (gOf p) : ℝ)) *
        (X.measG.μGv p.1 (KppX X hb p)).toReal
    have h1 : (muP X p (KvX X p)).toReal = (i : ℝ) * (muP X p (KppX X hb p)).toReal := by
      rw [hμi, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    rw [← hi, mul_div_assoc, div_self hi0, mul_one]
    exact h1
  · show (X.measG.μGv p.1 (KnatX X u p)).toReal / (X.measG.μGv p.1 (KvX X p)).toReal =
      (glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ) / (ggC D.R.rS D.R.k (gOf p) : ℝ)
    have h1 : (muP X p (KvX X p)).toReal = (j : ℝ) * (muP X p (KnatX X u p)).toReal := by
      rw [hμj, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    have hpos : (muP X p (KnatX X u p)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hB0, hBt⟩
    show (muP X p (KnatX X u p)).toReal / (muP X p (KvX X p)).toReal = _
    rw [h1, ← hj]
    rcases eq_or_ne (j : ℝ) 0 with h0 | h0
    · simp [h0]
    · rw [mul_comm (j : ℝ) (muP X p (KnatX X u p)).toReal, mul_comm (j : ℝ), div_mul_eq_div_div,
        div_self hpos, div_mul_eq_div_div, div_self hj0]

def LocAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word), HypX X hb FdN FdN' u u' → ∀ p : TypX X,
      StTop X p ∧ StK X p ∧ StRed X p ∧ StImA X hb p ∧ StImB X u p

theorem massDataIndices_of_haarIdx_redIdx_locAll (hH : HaarIdx) (hR : RedIdx) (hL : LocAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A :=
  massDataIndices_of
    (fun X hb hK FdN FdN' u u' hX p =>
      let h := hL X hb hK FdN FdN' u u' hX p
      measA_of X hb hH hR p h.1 h.2.1 h.2.2.1 h.2.2.2.1)
    (fun X hb hK FdN FdN' u u' hX p =>
      let h := hL X hb hK FdN FdN' u u' hX p
      measB_of X hH hR u p h.1 h.2.1 h.2.2.1 h.2.2.2.2)

theorem massDataIndices_of_locAll (hL : LocAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A := by
  have hH : HaarIdx := by
    exact haarIdx
  have hR : RedIdx := by
    exact redIdx
  intro D X
  exact massDataIndices_of_haarIdx_redIdx_locAll hH hR hL X

def LocOpen : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word), HypX X hb FdN FdN' u u' → ∀ p : TypX X,
      StK X p ∧ StRed X p ∧ StImA X hb p ∧ StImB X u p

theorem massDataIndices_of_locOpen (hL : LocOpen) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A := by
  exact massDataIndices_of_locAll (fun X hb hK FdN FdN' u u' hX p => ⟨stTop X p, hL X hb hK FdN FdN' u u' hX p⟩)

end MassDataIdxSteps
end
end

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

theorem oEpSplit_holds (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (hθ : IsSplitEquiv X p θ) :
    OEpSplit X p θ := by
  have hone : θ.symm (1, 1) = 1 := by rw [Prod.mk_one_one, map_one]
  have hsub : ∀ a b : FpX X p × FpX X p, θ.symm (a - b) = θ.symm a - θ.symm b := fun a b => map_sub _ _ _
  have hm : 1 - epsP X p ∈ OEp X p := imA_OEp_sub X p (imA_OEp_one X p) (imA_eps_mem X p)
  rcases PIW.MassDataColumns.theta_eps_cases X p θ hθ with h | h
  · have e1 : θ.symm (1, 0) = epsP X p := by rw [← h, AlgEquiv.symm_apply_apply]
    have e2 : θ.symm (0, 1) = 1 - epsP X p := by
      rw [← hone, ← e1, ← hsub]; congr 1; ext <;> simp
    exact ⟨e1 ▸ imA_eps_mem X p, e2 ▸ hm⟩
  · have e1 : θ.symm (0, 1) = epsP X p := by rw [← h, AlgEquiv.symm_apply_apply]
    have e2 : θ.symm (1, 0) = 1 - epsP X p := by
      rw [← hone, ← e1, ← hsub]; congr 1; ext <;> simp
    exact ⟨e2 ▸ hm, e1 ▸ imA_eps_mem X p⟩

def StAdaptBasisA : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ AdaptA X p θ Q

theorem reduction_image_of_basis (hb : AdBridgeIso X.B.I) (h : StAdaptBasisA X p) : LevelReductionImage X hb p := by
  obtain ⟨θ, hθ, Q, hL, hA⟩ := h
  exact reduction_image_of_adapted_mod X p hb latCoreX_holds ⟨θ, hθ, oEpSplit_holds X p θ hθ, Q, hL, hA⟩

end Loc

end MassDataIdxSteps
end
end

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem stAdaptBasisA_holds {D : D7} (X : HidaSetting D) (p : TypX X) : StAdaptBasisA X p :=
  adaptA_holds X p

theorem reduction_image_every_place {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X) : LevelReductionImage X hb p :=
  reduction_image_of_basis X p hb (stAdaptBasisA_holds X p)

end MassDataIdxSteps
end
end

section
namespace MassDataIdxSteps

theorem locOpen_holds : LocOpen := fun X hb _hK _ _ u _ _ p =>
  ⟨stK_holds X p, stRed_of_embP X p (embP_holds X p), stImA_of X hb p (reduction_image_every_place X hb p),
    stImB_of_adaptQ X u p (stAdaptQ_holds X hb u p)⟩

end MassDataIdxSteps
end
