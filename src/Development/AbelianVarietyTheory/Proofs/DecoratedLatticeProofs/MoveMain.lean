module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBasePointCarryingLatticeAndFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPoints
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionEqOfLocalAgreementStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeEqOfSplitPlaceFrameSpanStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RLatMove

theorem card_eq_of_frame {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) : Fintype.card Y = n := by
  apply le_antisymm
  · calc Fintype.card Y = (1 : Matrix Y Y k).rank := Matrix.rank_one.symm
      _ = (F.γ * F.β).rank := by rw [F.γβ]
      _ ≤ F.γ.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin n) := Matrix.rank_le_card_width _
      _ = n := Fintype.card_fin n
  · calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
      _ = (1 : Matrix (Fin n) (Fin n) k).rank := Matrix.rank_one.symm
      _ = (F.β * F.γ).rank := by rw [F.βγ]
      _ ≤ F.β.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card Y := Matrix.rank_le_card_width _

def frameGL {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) (B : GL Y k) (σ : Fin n ≃ Y) : GL (Fin n) k where
  val := (F.β * B.val).submatrix id σ
  inv := ((B⁻¹).val * F.γ).submatrix σ id
  val_inv := by
    rw [Matrix.submatrix_mul_equiv (F.β * B.val) ((B⁻¹).val * F.γ) id σ id]
    have : F.β * B.val * ((B⁻¹).val * F.γ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc B.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul, F.βγ]
    rw [this, Matrix.submatrix_id_id]
  inv_val := by
    have h := Matrix.submatrix_mul_equiv ((B⁻¹).val * F.γ) (F.β * B.val) σ (Equiv.refl (Fin n)) σ
    simp only [Equiv.coe_refl] at h
    rw [h]
    have : (B⁻¹).val * F.γ * (F.β * B.val) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
    rw [this, Matrix.submatrix_one_equiv]

end GlobalTheory.RLatMove

namespace GlobalTheory.RLatMove

end GlobalTheory.RLatMove

namespace GlobalTheory.RLatMove

end GlobalTheory.RLatMove
