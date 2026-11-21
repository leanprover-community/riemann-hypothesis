import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsModelWithBaseExOPnPt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherLast

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SpecialModelPoint.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    [Algebra (FractionRing O) Ω] [IsScalarTower O (FractionRing O) Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K), IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase O y k₀ →
    ∀ (Ω' : Type) [Field Ω'] [Algebra (IsLocalRing.ResidueField O) Ω'] (y' : (Σ k, ι k) → Ω'),
      (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) →
      NumbersDVR.specialIdeal (mIdealOver O y) ≤ mIdealOver (IsLocalRing.ResidueField O) y' →
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase (IsLocalRing.ResidueField O) y' k₀

theorem SpecialModelPoint.hyps :
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () ∧
      (∀ k, ∃ i, IndefiniteRowSideFullHecke.Kleiman2.pnPt (IsLocalRing.ResidueField exO) 1 ⟨k, i⟩ ≠ 0) ∧
      NumbersDVR.specialIdeal (mIdealOver exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1)) ≤
        mIdealOver (IsLocalRing.ResidueField exO) (IndefiniteRowSideFullHecke.Kleiman2.pnPt (IsLocalRing.ResidueField exO) 1) := by
  refine ⟨isModelWithBase_exO_pnPt, fun _ => ⟨0, IndefiniteRowSideFullHecke.Kleiman2.pnPt_ne_zero _ 1 _⟩, ?_⟩
  rw [specialIdeal_exO_pnPt]
  exact bot_le

example (h : SpecialModelPoint.Statement) :=
  h exO (IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1) Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 1) (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) ()
    SpecialModelPoint.hyps.1 _ (IndefiniteRowSideFullHecke.Kleiman2.pnPt (IsLocalRing.ResidueField exO) 1) SpecialModelPoint.hyps.2.1
    SpecialModelPoint.hyps.2.2

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver)

theorem SpecialModelPoint.proof (hgen : BlockGenOfModel.Statement) (htr : BlockGenTransfer.Statement)
    (hmod : ModelOfBlockGen.Statement) : SpecialModelPoint.Statement := by
  intro O _ _ _ Ω _ _ _ _ K _ _ ι _ y k₀ hy Ω' _ _ y' hy' hle
  let _ : Algebra O Ω' :=
    ((algebraMap (IsLocalRing.ResidueField O) Ω').comp (IsLocalRing.residue O)).toAlgebra
  have : IsScalarTower O (IsLocalRing.ResidueField O) Ω' :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hle' : mIdealOver O y ≤ mIdealOver O y' := by
    intro f hf
    have h1 := hle (Ideal.mem_map_of_mem (MvPolynomial.map (IsLocalRing.residue O)) hf)
    rw [mIdealOver, RingHom.mem_ker] at h1 ⊢
    rw [← h1, mConeMapOver, mConeMapOver]
    exact (MvPolynomial.aeval_map_algebraMap (IsLocalRing.ResidueField O) _ f).symm
  have hb : BlockGen O y' k₀ := htr O K ι Ω y k₀ (hgen O K ι Ω y k₀ hy) Ω' y' hy' hle'
  refine hmod _ K ι Ω' y' k₀ hy' ?_
  intro j hj k
  obtain ⟨w, hw, hsum⟩ := hb j hj k
  refine ⟨w, fun a b => ?_, hsum⟩
  have hsub : chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀)) (fun _ => j) ≤
      (chartRingOver (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀))
        (fun _ => j)).restrictScalars O :=
    Algebra.adjoin_le Algebra.subset_adjoin
  exact hsub (hw a b)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
