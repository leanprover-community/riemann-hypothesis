module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.SiegelCov

section Gen

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR

theorem chi_adele (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) =
      (modu (Ainf F) (fstA F M.det) : ℝ) * ∏ᶠ v, ‖evalV F v (sndA F M.det)‖ := by
  classical
  let Mi : Matrix κ κ (Ainf F) := (fstA F).toRingHom.mapMatrix M
  let Mf : Matrix κ κ (Af F) := (sndA F).toRingHom.mapMatrix M
  have hi : Mi.det = fstA F M.det := (RingHom.map_det _ _).symm
  have hf : Mf.det = sndA F M.det := (RingHom.map_det _ _).symm
  have hMi : IsUnit Mi.det := hi ▸ hM.map (fstA F)
  have hMf : IsUnit Mf.det := hf ▸ hM.map (sndA F)
  let j : (κ → Ainf F) × (κ → Af F) →+ (κ → AF F) := zipHom κ (Ainf F) (Af F)
  have hj : IsOpenEmbedding j := GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs κ (Ainf F) (Af F)
  have s1 : addEquivAddHaarChar (mulVecCE M hM) =
      addEquivAddHaarChar (prodCE (mulVecCE Mi hMi) (mulVecCE Mf hMf)) :=
    GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict _ _ j hj (mulVecCE M hM) (prodCE (mulVecCE Mi hMi) (mulVecCE Mf hMf)) fun p => by
      funext i
      show (M *ᵥ j p) i = ((Mi *ᵥ p.1) i, (Mf *ᵥ p.2) i)
      have e1 : fstA F ((M *ᵥ j p) i) = (Mi *ᵥ p.1) i := by
        rw [show (fstA F) ((M *ᵥ j p) i) = (fstA F).toRingHom ((M *ᵥ j p) i) from rfl, RingHom.map_mulVec]
        rfl
      have e2 : sndA F ((M *ᵥ j p) i) = (Mf *ᵥ p.2) i := by
        rw [show (sndA F) ((M *ᵥ j p) i) = (sndA F).toRingHom ((M *ᵥ j p) i) from rfl, RingHom.map_mulVec]
        rfl
      rw [← e1, ← e2]
      rfl
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace F, v.Completion))
  haveI : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ v : InfinitePlace F, v.Completion))
  have s2 : addEquivAddHaarChar (mulVecCE Mi hMi) = modu (Ainf F) Mi.det :=
    GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced (Ainf F) inferInstance inferInstance κ Mi hMi
  rw [s1, GlobalTheory.T.addEquivAddHaarChar_prodCongr, NNReal.coe_mul, s2, chi_Af F Mf hMf, hi, hf]

theorem addEquivAddHaarChar_mulVecCE_adele (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    addEquivAddHaarChar (mulVecCE M hM) = distribHaarChar (AF F) hM.unit := by
  let N : Matrix Unit Unit (AF F) := fun _ _ => M.det
  have hdet : N.det = M.det := Matrix.det_unique N
  have hN : IsUnit N.det := hdet ▸ hM
  have htr := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (GlobalTheory.ModuNorm.evalUnitCE (AF F)) (mulVecCE N hN)
  have hext : ((GlobalTheory.ModuNorm.evalUnitCE (AF F)).symm.trans (mulVecCE N hN)).trans (GlobalTheory.ModuNorm.evalUnitCE (AF F)) =
      GlobalTheory.ModuNorm.mulUnitCE hM.unit := by
    ext x
    show (N *ᵥ fun _ => x) () = M.det * x
    simp [Matrix.mulVec, dotProduct, N]
  rw [hext] at htr
  rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar, htr]
  apply NNReal.coe_injective
  rw [chi_adele, chi_adele, hdet]

end Gen

end GlobalTheory.SiegelCov

namespace GlobalTheory.SiegelCov

section Coord

open Matrix GlobalTheory.ModuLR

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)

end Coord

end GlobalTheory.SiegelCov

