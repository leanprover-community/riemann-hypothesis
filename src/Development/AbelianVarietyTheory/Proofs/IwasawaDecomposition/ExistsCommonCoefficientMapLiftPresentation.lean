import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupsEquivUnitFormGramOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseWeightEqForcedLiftWeight
import Formalism.LocalToGlobal.Columns.InputsGenus
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Divisibility.DefGroup
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftResidueTwistCharacterEqResChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabCardOfStabTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemHatSwap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormLevelPrimesIsSplitSet

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryGroups_equiv_unitForm_gram_one : ∀ (X : Stages) (i : Fin X.toD7.R.m), (Vc X.toD7 i).gram = 1 →
    ∃ (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i))
      (eΓ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV ≃* GQ (Vc X.toD7 i)),
      (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) ∧
      (∀ γ, Bridge.ratF (Vc X.toD7 i) (eΓ γ) = eG (Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV γ)) ∧
      (∀ γ, Bridge.IsRatMat (Vc X.toD7 i) (eΓ γ) (LiftBrg.castGL (LiftBrg.rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.StdGroups.stdGroups_equiv | exact GlobalTheory.Mem.R3.LiftBrg.StdGroups.stdGroups_equiv | (intros; apply GlobalTheory.Mem.R3.LiftBrg.StdGroups.stdGroups_equiv <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseWeight_eq_forcedLiftWeight : ∀ (X : Stages) (i : Fin X.toD7.R.m) (τ : X.B.fields.Tau) (a : Fin X.B.R.nV),
    (X.B.wts.lamV ((i : ℕ) + 1) τ).w a =
      (Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ).w (Fin.cast (LiftBrg.rkEq X i) a) := by
  first | exact @GlobalTheory.Mem.LiftWt.lamV_eq_lamLdef | exact GlobalTheory.Mem.LiftWt.lamV_eq_lamLdef | (intros; apply GlobalTheory.Mem.LiftWt.lamV_eq_lamLdef <;> assumption)
end

section
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise {n r t : ℕ} (hn : n = r + t) (a : Fin n) :
    Formalism.L2.DIV.blkOf r t a = Formalism.L2.Col.coarse r [t] a.val ∧
      Formalism.L2.DIV.blk2 r a = Formalism.L2.Col.coarse r [t] a.val := by
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]
    simp [Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h]
  · have h' : r ≤ a.val := Nat.not_lt.mp h
    rw [Formalism.L2.Col.coarse_of_le h']
    have hlt : a.val - r < t := by omega
    have hd : (a.val - r) / t = 0 := Nat.div_eq_of_lt hlt
    simp [Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h, hd, Formalism.L2.Col.blkIdx, hlt]

theorem blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks :
    ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ g : GL (Fin n) κ,
      (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) ∧
        (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) := by
  intro κ _ n r t hn g
  rw [Formalism.L2.DIV.mem_blockTri, Formalism.L2.DIV.mem_blockTri, Formalism.L2.Col.mem_btG]
  refine ⟨?_, ?_⟩
  · simp only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).1]
  · simp only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).2]

end GlobalTheory
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_blockTri_blkOf_and_blk2_iff_mem_blockUT : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ g : GL (Fin n) κ,
    (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) ∧
      (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) := by
  atlas_forward_decl GlobalTheory.blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks
end

section
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem topBlock_eq_one_iff_mem_colHK : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (hr : r ≤ n) (g : GL (Fin n) κ),
    g ∈ Formalism.L2.Col.blockUT n κ r [t] → (Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g ∈ Formalism.L2.Col.HK n κ r [t]) := by
  intro κ _ n r t _ hr g hg
  have hb : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (n := n) r) := by
    refine Formalism.L2.DIV.mem_blockTri.2 fun i j hij => ?_
    have hji : j.val < r ∧ ¬ i.val < r := by
      unfold Formalism.L2.DIV.blk2 at hij
      by_cases hj : j.val < r <;> by_cases hi : i.val < r <;> simp [hj, hi] at hij ⊢
    refine hg (show Formalism.L2.Col.coarse r [t] j.val < Formalism.L2.Col.coarse r [t] i.val from ?_)
    rw [Formalism.L2.Col.coarse_of_lt hji.1, Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hji.2)]
    exact Nat.succ_pos _
  rw [Formalism.L2.Col.mem_HK, Units.ext_iff, Formalism.L2.DIV.upper_block_val_submatrix hr hb, Units.val_one]
  constructor
  · intro h
    refine ⟨hg, fun i j hi hj => ?_⟩
    have h1 := congrFun (congrFun h ⟨i.val, hi⟩) ⟨j.val, hj⟩
    simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.mk.injEq] at h1
    rw [Matrix.one_apply]
    simp only [Fin.ext_iff]
    exact h1
  · rintro ⟨-, h⟩
    ext i j
    rw [Matrix.submatrix_apply, h _ _ i.2 j.2]
    simp [Matrix.one_apply]

end GlobalTheory
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperLeftBlock_eq_one_iff_mem_HK : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (hr : r ≤ n) (g : GL (Fin n) κ),
    g ∈ Formalism.L2.Col.blockUT n κ r [t] → (Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g ∈ Formalism.L2.Col.HK n κ r [t]) := by
  atlas_forward_decl GlobalTheory.topBlock_eq_one_iff_mem_colHK
end

section
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem blkOf_eq_coarse {n r t : ℕ} (hn : n = r + t) :
    (Formalism.L2.DIV.blkOf r t : Fin n → ℕ) = fun a => Formalism.L2.Col.coarse r [t] a.val := by
  funext a
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]; simp [Formalism.L2.DIV.blkOf, h]
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp h)]
    have h2 : a.val - r < t := by omega
    simp [Formalism.L2.DIV.blkOf, h, Formalism.L2.Col.blkIdx, h2, Nat.div_eq_of_lt h2]

theorem twoBlocks_eq_coarse_of_add {n r t : ℕ} (hn : n = r + t) :
    (Formalism.L2.DIV.blk2 r : Fin n → ℕ) = fun a => Formalism.L2.Col.coarse r [t] a.val := by
  funext a
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]; simp [Formalism.L2.DIV.blk2, h]
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp h)]
    have h2 : a.val - r < t := by omega
    simp [Formalism.L2.DIV.blk2, h, Formalism.L2.Col.blkIdx, h2]

theorem lowerBlockDet_coarse_partition_eq_blockDet_upperTri {κ : Type} [CommRing κ] {n r t : ℕ} (g : GL (Fin n) κ)
    (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]) :
    Formalism.L2.DIV.dBlk (fun a : Fin n => Formalism.L2.Col.coarse r [t] a.val) 1 g =
      Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  have hg' : g ∈ Formalism.L2.DIV.blockTri (fun a : Fin n => Formalism.L2.Col.coarse r [t] a.val) := hg
  apply Units.ext
  rw [Formalism.L2.DIV.diag_block_det_val 1 hg', Formalism.L2.Col.blkDet_val]
  rfl

theorem secondBlockDet_eq_blockDet_of_sum_partitions : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (g : GL (Fin n) κ) (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]),
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  intro κ _ n r t hn g hg
  refine ⟨?_, ?_⟩
  · rw [blkOf_eq_coarse hn]; exact lowerBlockDet_coarse_partition_eq_blockDet_upperTri g hg
  · rw [twoBlocks_eq_coarse_of_add hn]; exact lowerBlockDet_coarse_partition_eq_blockDet_upperTri g hg

end GlobalTheory
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dBlk_eq_blkDet_coarse : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (g : GL (Fin n) κ) (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]),
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  atlas_forward_decl GlobalTheory.secondBlockDet_eq_blockDet_of_sum_partitions
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.Mem.R3.LevChi

theorem chi_succ_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (w : {w // w ∈ (X.B.primes px).vGs}) (c : (𝓞 X.B.fields.E ⧸ w.1.asIdeal)ˣ),
      L.chi ((i : ℕ) + 1) w.1 c = Units.map X.toD7.what₂.embLL.toMonoidHom (Formalism.L2.Col.chiAt I.Ch w (i : ℕ) c) := by
  intro X px I U L hI hL i w c
  have hw : w.1 ∈ L.Pg := by rw [hL.Pg]; exact w.2
  have hres := hL.is.chi i w.1 hw
  have hmu : L.C.mu0 i = I.C.mu0 i := by rw [hL.C]; rfl
  rw [hmu] at hres
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 X.B.fields.E ⧸ w.1.asIdeal)
  have hy0 : ((y : 𝓞 X.B.fields.E) : X.B.fields.E) ≠ 0 := by
    intro h
    have h0 : y = 0 := RingOfIntegers.ext h
    apply c.ne_zero
    rw [← hy, h0, map_zero]
  let x : X.B.fields.Eˣ := Units.mk0 _ hy0
  have h1 := hres y x c rfl hy.symm
  have h2 := (hI.ch_tied.mu0 i).atg w x y c rfl hy.symm
  have h3 : (((L.chi ((i : ℕ) + 1) w.1 c)⁻¹ : ℂˣ) : ℂ) = X.B.embLL (((I.Ch.chi i w c)⁻¹ : X.B.fields.Kˣ) : X.B.fields.K) :=
    (congrArg Units.val h1).trans h2
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀] at h3
  have h5 : ((L.chi ((i : ℕ) + 1) w.1 c : ℂˣ) : ℂ) = X.B.embLL ((I.Ch.chi i w c : X.B.fields.Kˣ) : X.B.fields.K) :=
    inv_injective h3
  have e : Formalism.L2.Col.chiAt I.Ch w (i : ℕ) = I.Ch.chi i w := by
    unfold Formalism.L2.Col.chiAt Formalism.L2.Col.extChi
    rw [dif_pos (show (i : ℕ) < X.B.R.m from i.2)]
    rfl
  rw [e]
  exact Units.ext h5

end GlobalTheory.Mem.R3.LevChi
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLevelCharacter_typePrime_eq_columnCharacter : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (w : {w // w ∈ (X.B.primes px).vGs}) (c : (𝓞 X.B.fields.E ⧸ w.1.asIdeal)ˣ),
      L.chi ((i : ℕ) + 1) w.1 c = Units.map X.toD7.what₂.embLL.toMonoidHom (Formalism.L2.Col.chiAt I.Ch w (i : ℕ) c) := by
  atlas_forward_decl GlobalTheory.Mem.R3.LevChi.chi_succ_eq
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftResidueTwistCharacter_eq_resChar : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ (t : TupU I U) (PP : HeightOneSpectrum (𝓞 X.B.fields.E)), PP ∈ Formalism.L2.Col.QE I.sel t.1 →
      ∀ c : (𝓞 X.B.fields.E ⧸ PP.asIdeal)ˣ, L.xiR t PP c = Units.map X.toD7.what₂.embLL.toMonoidHom
        (Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) PP c) := by
  first | exact @GlobalTheory.Mem.LevResXi.xiR_eq_map_resChar | exact GlobalTheory.Mem.LevResXi.xiR_eq_map_resChar | (intros; apply GlobalTheory.Mem.LevResXi.xiR_eq_map_resChar <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.LevDisj

theorem places_disjoint : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ t : TupU I U, Disjoint (X.B.primes px).vGs (Formalism.L2.Col.QE I.sel t.1) := by
  intro X px I U L hI _ _ t
  rw [Finset.disjoint_left]
  intro P hG hQ
  exact GlobalTheory.KFormsCmp.disj (GlobalTheory.BasePrimes.primes_ok X.B px).1 hI.sel_ok t.1 hI.g_mem hQ hG

end GlobalTheory.Mem.LevDisj
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimes_disjoint_twistChosenPrimes : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ t : TupU I U, Disjoint (X.B.primes px).vGs (Formalism.L2.Col.QE I.sel t.1) := by
  atlas_forward_decl GlobalTheory.Mem.LevDisj.places_disjoint
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Mem.LevPres
open Formalism.L2.DIV

theorem castGL_rfl' {R : Type} [CommRing R] {m : ℕ} (x : GL (Fin m) R) : LiftBrg.castGL (rfl : m = m) x = x :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem castGL_castGL_symm' {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (y : GL (Fin n) R) :
    LiftBrg.castGL h (LiftBrg.castGL h.symm y) = y := by
  subst h; rw [castGL_rfl', castGL_rfl']

theorem castGL_St {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ}
    (h : m = n) (x : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    LiftBrg.castGL h x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ↔ x ∈ St (1 : GL (Fin m) _) := by
  subst h; rw [castGL_rfl']

theorem castGL_redFn {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ}
    (h : m = n) (x : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) :
    redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) PP (LiftBrg.castGL h x) = LiftBrg.castGL h (redFn 1 PP x) := by
  subst h; rw [castGL_rfl', castGL_rfl']

theorem castGL_blkOf {κ : Type} [CommRing κ] {m n : ℕ} (h : m = n) (r t : ℕ) (g : GL (Fin m) κ) :
    LiftBrg.castGL h g ∈ blockTri (blkOf r t) ↔ g ∈ blockTri (blkOf r t) := by
  subst h; rw [castGL_rfl']

theorem generalLinearGroupCastOfEq_mem_twoBlockTri_iff {κ : Type} [CommRing κ] {m n : ℕ} (h : m = n) (r : ℕ) (g : GL (Fin m) κ) :
    LiftBrg.castGL h g ∈ blockTri (blk2 r) ↔ g ∈ blockTri (blk2 r) := by
  subst h; rw [castGL_rfl']

theorem generalLinearGroupCastOfEq_rowBlock_eq {κ : Type} [CommRing κ] {m n r : ℕ} (h : m = n) (hr : r ≤ n) (hr' : r ≤ m) (g : GL (Fin m) κ) :
    upperLeftBlock hr (LiftBrg.castGL h g) = upperLeftBlock hr' g := by
  subst h; rw [castGL_rfl']

theorem generalLinearGroupCastOfEq_diagBlock_eq {κ : Type} [CommRing κ] {m n : ℕ} (h : m = n) (r t : ℕ) (g : GL (Fin m) κ) :
    dBlk (blkOf r t) 1 (LiftBrg.castGL h g) = dBlk (blkOf r t) 1 g := by
  subst h; rw [castGL_rfl']

theorem generalLinearGroupCastOfEq_twoBlock_diagBlock_eq {κ : Type} [CommRing κ] {m n : ℕ} (h : m = n) (r : ℕ) (g : GL (Fin m) κ) :
    dBlk (blk2 r) 1 (LiftBrg.castGL h g) = dBlk (blk2 r) 1 g := by
  subst h; rw [castGL_rfl']

section StdSide'

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (SG : Finset (Pl E)) (H : Subgroup (Formalism.L2.Col.GLG E n SG))

theorem mem_J0_empty (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ Formalism.L2.Col.J0 hc n ∅ ↔ x ∈ Formalism.L2.Col.UAd hc n ∧ x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  unfold Formalism.L2.Col.J0
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun P hP => absurd hP (Finset.notMem_empty P)⟩

theorem mem_colJ_iff (x : Formalism.L2.Col.UAd hc n) :
    x ∈ Bridge.colJ hc n ∅ SG H ↔
      ∃ hx : (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Col.J0 hc n ∅, Formalism.L2.Col.redG hc n ∅ SG ⟨x, hx⟩ ∈ H := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem redG_apply' (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.Col.J0 hc n ∅) (w : SG) :
    Formalism.L2.Col.redG hc n ∅ SG ⟨x, hx⟩ w = redFn 1 w.1 x := by
  unfold redFn
  rw [extendOne_of_mem _ (Formalism.L2.Col.congruence_subgroup_le_stabilizer hc n ∅ hx)]
  rfl

theorem redH_apply' (m : Formalism.L2.Col.JH hc n ∅ SG H) (w : SG) :
    ((Formalism.L2.Col.redH hc n ∅ SG H m : H) : Formalism.L2.Col.GLG E n SG) w =
      redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 ((m : Formalism.L2.Col.J0 hc n ∅) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  show Formalism.L2.Col.redG hc n ∅ SG (m : Formalism.L2.Col.J0 hc n ∅) w = _
  exact redG_apply' hc n SG _ (m : Formalism.L2.Col.J0 hc n ∅).2 w

end StdSide'

theorem lev_eq_of_eq {κ K : Type} [CommRing κ] [Field K] {n : ℕ} {l₁ l₂ : Formalism.L2.Col.Lev κ K n} (e : l₁ = l₂)
    (g : GL (Fin n) κ) (h₁ : g ∈ l₁.H) (h₂ : g ∈ l₂.H) : l₁.lam ⟨g, h₁⟩ = l₂.lam ⟨g, h₂⟩ := by
  subst e; rfl

theorem mem_levEnvJ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (y : Bridge.Gf V) :
    y ∈ (levEnv V β L).J ↔ Formalism.UG.bc (swapAE D) (y : GL (Fin V.rank) _) ∈ lev D.sp.cm V.gram β (flag1L L) := Iff.rfl

theorem levEnv_chi {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (y : Bridge.Gf V)
    (hy : y ∈ (levEnv V β L).J) :
    (levEnv V β L).χ ⟨y, hy⟩ = levFn β (flag1L L) (Formalism.UG.bc (swapAE D) (y : GL (Fin V.rank) _)) := rfl

theorem levFn_datVt (X : Stages) {T : Type} (L : Formalism.IndefR.Links.LevCh X.toD7 T) (i : Fin X.toD7.R.m) (t : T)
    (M : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) :
    levFn 1 (flag1L (L.datVt i t)) M =
      (∏ PP ∈ L.Pg, (L.chi ((i : ℕ) + 1) PP)⁻¹ (dBlk (blkOf X.toD7.R.r X.toD7.R.t) 1 (redFn 1 PP M))) *
        ∏ PP ∈ L.Q t, L.xiR t PP (dBlk (blk2 X.toD7.R.r) 1 (redFn 1 PP M)) := by
  have h0 : ext1 (flag1L (L.datVt i t)).P.H (flag1L (L.datVt i t)).P.chi (rTup 1 (flag1L (L.datVt i t)) M) = 1 :=
    Formalism.IndefR.Lev.subgroupCharExtension_one_apply _ _
  unfold levFn
  rw [h0, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact Finset.prod_range_one _

theorem chr_eq_one {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (Λ : Formalism.L2.Col.LevFam E K n SG) (h : Λ.grp) (e : h.1 = 1) : Λ.chr h = 1 := by
  have e' : h = 1 := Subtype.ext e
  rw [e', map_one]

theorem prod_glue {E : Type} [Field E] [NumberField E] (A' B' A B : Finset (HeightOneSpectrum (𝓞 E))) (hA : A' = A) (hB : B' = B)
    (hd : Disjoint A B) (a b φ : HeightOneSpectrum (𝓞 E) → ℂˣ) (ha : ∀ P ∈ A, φ P = (a P)⁻¹) (hb : ∀ P ∈ B, φ P = (b P)⁻¹) :
    ((∏ P ∈ A', a P) * ∏ P ∈ B', b P)⁻¹ = ∏ w : Formalism.L2.Col.uSG A B, φ w.1 := by
  classical
  subst hA hB
  rw [Finset.prod_coe_sort (Formalism.L2.Col.uSG A' B') φ, mul_inv, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_congr rfl ha, ← Finset.prod_congr rfl hb]
  convert (Finset.prod_union hd).symm

theorem lev_type_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L →
    ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i)),
    (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) →
    ∃ hJ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J =
        (Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).map eG.toMonoidHom,
      ∀ (k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp)
        (hk : eG (k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J),
        (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩)⁻¹ : ℂˣ) =
          Units.map X.toD7.what₂.embLL.toMonoidHom ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr
            (Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
              ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _).symm k))) ∧
        ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ Bridge.principalCongruenceSubgroup X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) →
          (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩ = 1) := by
  intro X px I U L hI hV hL i t eG heG
  classical
  have hβ : L.βV i = 1 := hL.beta.1 i
  have hPg : L.Pg = (X.B.primes px).vGs := hL.Pg
  have hQ : L.Q t = Formalism.L2.Col.QE I.sel t.1 := by rw [hL.Q t, ← tup_ixOf I t]
  have hdisj := GlobalTheory.T.typePrimes_disjoint_twistChosenPrimes X px I U L hI hV hL t
  have hrk := LiftBrg.rkEq X i
  have hnV : X.B.R.nV = X.B.R.r + X.B.R.t := rfl
  have hM : ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV,
      Formalism.UG.bc (swapAE X.toD7) ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) =
        LiftBrg.castGL hrk (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) := by
    intro x
    rw [← heG x]
    exact (castGL_castGL_symm' _ _).symm
  have hUA : ∀ y : Bridge.Gf (Vc X.toD7 i),
      Formalism.UG.bc (swapAE X.toD7) (y : GL (Fin (Vc X.toD7 i).rank) _) ∈ UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
    rintro ⟨_, g, rfl⟩
    exact GlobalTheory.LevSplit.finE_mem_UA _ g

  have hHv : ∀ (w : LiftBrg.sgL X I U t) (hw : w.1 ∈ (X.B.primes px).vGs) (g : GL (Fin X.B.R.nV) (𝓞 X.B.fields.E ⧸ w.1.asIdeal)),
      g ∈ ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).H ↔ g ∈ Formalism.L2.Col.HK X.B.R.nV _ X.B.R.r [X.B.R.t] := by
    intro w hw g
    show g ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w).H ↔ _
    have e : Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w = Formalism.L2.Col.mtTyK I.Ch ((i : ℕ) + 1) ⟨w.1, hw⟩ :=
      Formalism.L2.Col.LevFam.glue_of_mem _ _ w hw
    rw [e]
    rfl
  have hHq : ∀ (w : LiftBrg.sgL X I U t) (hw : w.1 ∉ (X.B.primes px).vGs) (g : GL (Fin X.B.R.nV) (𝓞 X.B.fields.E ⧸ w.1.asIdeal)),
      g ∈ ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).H ↔ g ∈ Formalism.L2.Col.blockUT X.B.R.nV _ X.B.R.r [X.B.R.t] := by
    intro w hw g
    show g ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w).H ↔ _
    have e : Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w =
        Formalism.L2.Col.mtTyQ X.B.R (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) (Formalism.L2.Col.QE I.sel t.1)
          ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩ :=
      Formalism.L2.Col.LevFam.glue_of_not _ _ w hw
    rw [e]
    rfl

  have hmem : ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV,
      eG x ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J ↔
        x ∈ Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp := by
    intro x
    have hx0 := hUA (eG x)
    rw [hM x] at hx0
    have hcr : ∀ PP : Pl X.toD7.host.E,
        LiftBrg.castGL hrk (redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) PP (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) =
          redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) PP
            (LiftBrg.castGL hrk (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) :=
      fun PP => (castGL_redFn hrk _ PP).symm
    rw [mem_levEnvJ, hM x, hβ, mem_lev, mem_parLev, castGL_St]
    refine Iff.trans ?_ (mem_colJ_iff X.toD7.sp.cm X.B.R.nV (LiftBrg.sgL X I U t) _ x).symm
    constructor
    · rintro ⟨⟨-, hSt, hg, hq⟩, hr⟩
      have hr' : rTup 1 (flag1L (L.datVt i t)) (LiftBrg.castGL hrk (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) = 1 :=
        Subgroup.mem_bot.1 hr
      have hx : (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) ∈ Formalism.L2.Col.J0 X.toD7.sp.cm X.B.R.nV ∅ :=
        (mem_J0_empty _ _ _).2 ⟨x.2, hSt⟩
      refine ⟨hx, (Subgroup.mem_pi _).2 fun w _ => ?_⟩
      show Formalism.L2.Col.redG X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) ⟨_, hx⟩ w ∈
        ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).H
      rw [show Formalism.L2.Col.redG X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) ⟨_, hx⟩ w =
        redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E) (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))
          from redG_apply' _ _ _ _ hx w]
      by_cases hw : w.1 ∈ (X.B.primes px).vGs
      · rw [hHv w hw]
        have hPP : w.1 ∈ (flag1L (L.datVt i t)).Pg := by
          show w.1 ∈ L.Pg
          rw [hPg]; exact hw
        have h1 : LiftBrg.castGL hrk (redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E)
            (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) ∈ blockTri (blkOf X.B.R.r X.B.R.t) := by
          convert hg w.1 hPP using 2
          all_goals first | rfl | exact hcr _
        rw [castGL_blkOf] at h1
        have h2 := ((GlobalTheory.T.mem_blockTri_blkOf_and_blk2_iff_mem_blockUT hnV _).1).1 h1
        refine (GlobalTheory.T.upperLeftBlock_eq_one_iff_mem_HK hnV (Formalism.L2.Col.r_le_nV X.B.R) _ h2).1 ?_
        have h3 : upperLeftBlock (flag1L (L.datVt i t)).hr (LiftBrg.castGL hrk (redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X))
            (w.1 : Pl X.toD7.host.E) (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)))) = 1 := by
          have h3' : upperLeftBlock (flag1L (L.datVt i t)).hr (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E)
              (LiftBrg.castGL hrk (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)))) = 1 := congrFun hr' ⟨w.1, hPP⟩
          convert h3' using 2
          all_goals first | rfl | exact hcr _
        rw [generalLinearGroupCastOfEq_rowBlock_eq hrk (flag1L (L.datVt i t)).hr (Formalism.L2.Col.r_le_nV X.B.R)] at h3
        exact h3
      · rw [hHq w hw]
        have hq' : w.1 ∈ Formalism.L2.Col.QE I.sel t.1 := (Finset.mem_union.mp w.2).resolve_left hw
        have hPP : w.1 ∈ (flag1L (L.datVt i t)).Q := by
          show w.1 ∈ L.Q t
          rw [hQ]; exact hq'
        have h1 : LiftBrg.castGL hrk (redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E)
            (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) ∈ blockTri (blk2 X.B.R.r) := by
          convert hq w.1 hPP using 2
          all_goals first | rfl | exact hcr _
        rw [generalLinearGroupCastOfEq_mem_twoBlockTri_iff] at h1
        exact ((GlobalTheory.T.mem_blockTri_blkOf_and_blk2_iff_mem_blockUT hnV _).2).1 h1
    · rintro ⟨hx, hH⟩
      have hSt := ((mem_J0_empty _ _ _).1 hx).2
      have hw' : ∀ w : LiftBrg.sgL X I U t, redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E)
          (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) ∈ ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).H := fun w => by
        rw [show redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E) (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) =
          Formalism.L2.Col.redG X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) ⟨_, hx⟩ w from (redG_apply' _ _ _ _ hx w).symm]
        exact (Subgroup.mem_pi _).1 hH w (Set.mem_univ _)
      refine ⟨⟨hx0, hSt, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
      · have hv : PP ∈ (X.B.primes px).vGs := by rw [← hPg]; exact hPP
        have hk := (hHv ⟨PP, Finset.mem_union_left _ hv⟩ hv _).1 (hw' ⟨PP, Finset.mem_union_left _ hv⟩)
        rw [← hcr, castGL_blkOf]
        exact ((GlobalTheory.T.mem_blockTri_blkOf_and_blk2_iff_mem_blockUT hnV _).1).2 (Formalism.L2.Col.HK_le_blockUT _ _ _ _ hk)
      · have hq' : PP ∈ Formalism.L2.Col.QE I.sel t.1 := by rw [← hQ]; exact hPP
        have hb : redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) PP (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) ∈
            Formalism.L2.Col.blockUT X.B.R.nV _ X.B.R.r [X.B.R.t] := by
          by_cases hv : PP ∈ (X.B.primes px).vGs
          · exact Formalism.L2.Col.HK_le_blockUT _ _ _ _
              ((hHv ⟨PP, Finset.mem_union_right _ hq'⟩ hv _).1 (hw' ⟨PP, Finset.mem_union_right _ hq'⟩))
          · exact (hHq ⟨PP, Finset.mem_union_right _ hq'⟩ hv _).1 (hw' ⟨PP, Finset.mem_union_right _ hq'⟩)
        rw [← hcr, generalLinearGroupCastOfEq_mem_twoBlockTri_iff]
        exact ((GlobalTheory.T.mem_blockTri_blkOf_and_blk2_iff_mem_blockUT hnV _).2).2 hb
      · refine Subgroup.mem_bot.2 ?_
        funext PP
        have hv : PP.1 ∈ (X.B.primes px).vGs := by rw [← hPg]; exact PP.2
        have hk := (hHv ⟨PP.1, Finset.mem_union_left _ hv⟩ hv _).1 (hw' ⟨PP.1, Finset.mem_union_left _ hv⟩)
        show upperLeftBlock (L.datVt i t).hr (redFn 1 PP.1 (LiftBrg.castGL hrk (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)))) = 1
        rw [← hcr, generalLinearGroupCastOfEq_rowBlock_eq hrk (L.datVt i t).hr (Formalism.L2.Col.r_le_nV X.B.R)]
        exact (GlobalTheory.T.upperLeftBlock_eq_one_iff_mem_HK hnV _ _ (Formalism.L2.Col.HK_le_blockUT _ _ _ _ hk)).2 hk

  have hJ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J =
      (Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
        (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).map eG.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · intro hy
      refine ⟨eG.symm y, (hmem _).1 (by rwa [eG.apply_symm_apply]), eG.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).2 hx
  refine ⟨hJ, fun k hk => ?_⟩
  have hm1 := Bridge.colJEquiv_symm_coe X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
    (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp k
  have hxk : ((((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
      (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).symm k : Formalism.L2.Col.JH _ _ _ _ _) :
        Formalism.L2.Col.J0 X.toD7.sp.cm X.B.R.nV ∅) : GL (Fin X.B.R.nV) (LiftBrg.EA X)) =
      ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)) := congrArg Subtype.val hm1
  have hredw : ∀ w : LiftBrg.sgL X I U t,
      ((Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
        ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).symm k) : _) : Formalism.L2.Col.GLG _ _ _) w =
        redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E)
          ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)) := by
    intro w
    exact (redH_apply' _ _ _ _ _ w).trans (congrArg _ hxk)
  have hcrk : ∀ PP : Pl X.toD7.host.E,
      redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) PP
          (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X))) =
        LiftBrg.castGL hrk (redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) PP
          ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X))) :=
    fun PP => castGL_redFn hrk _ PP
  have perw : ∀ (w : LiftBrg.sgL X I U t) (g : GL (Fin X.B.R.nV) (𝓞 X.B.fields.E ⧸ w.1.asIdeal))
      (hg : g ∈ ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).H),
      g = redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E)
          ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)) →
      Units.map X.toD7.what₂.embLL.toMonoidHom (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).lam ⟨g, hg⟩) =
        if (w.1 : Pl X.toD7.host.E) ∈ (X.B.primes px).vGs then
          L.chi ((i : ℕ) + 1) w.1 (dBlk (blkOf X.toD7.R.r X.toD7.R.t) 1 (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) w.1
            (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)))))
        else (L.xiR t w.1 (dBlk (blk2 X.toD7.R.r) 1 (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) w.1
            (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X))))))⁻¹ := by
    intro w g hg hgw
    by_cases hv : (w.1 : Pl X.toD7.host.E) ∈ (X.B.primes px).vGs
    · rw [if_pos hv]
      have hg' : g ∈ Formalism.L2.Col.HK X.B.R.nV _ X.B.R.r [X.B.R.t] := (hHv w hv g).1 hg
      have hb := Formalism.L2.Col.HK_le_blockUT _ _ _ _ hg'
      have e : Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w = Formalism.L2.Col.mtTyK I.Ch ((i : ℕ) + 1) ⟨w.1, hv⟩ :=
        Formalism.L2.Col.LevFam.glue_of_mem _ _ w hv
      have l1 : ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).lam ⟨g, hg⟩ =
          ((Formalism.L2.Col.mtTyK I.Ch ((i : ℕ) + 1) ⟨w.1, hv⟩).lam ⟨g, hg'⟩)⁻¹ := by
        show ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w).lam⁻¹) ⟨g, hg⟩ = _
        rw [MonoidHom.inv_apply, lev_eq_of_eq e g hg hg']
      have l2 : (Formalism.L2.Col.mtTyK I.Ch ((i : ℕ) + 1) ⟨w.1, hv⟩).lam ⟨g, hg'⟩ =
          (Formalism.L2.Col.chiAt I.Ch ⟨w.1, hv⟩ (i : ℕ))⁻¹
            (Formalism.L2.Col.blkDet X.B.R.nV _ (Formalism.L2.Col.coarse X.B.R.r [X.B.R.t]) 1 ⟨g, hb⟩) := by
        show Formalism.L2.Col.lamKV (Formalism.L2.Col.chiAt I.Ch ⟨w.1, hv⟩ ((i : ℕ) + 1 - 1)) X.B.R.nV X.B.R.r X.B.R.t ⟨g, hg'⟩ = _
        rw [Nat.add_sub_cancel]
        unfold Formalism.L2.Col.lamKV Formalism.L2.Col.lamK
        rw [MonoidHom.comp_apply, Formalism.L2.Col.detChar_apply]
        simp only [List.length_singleton, Finset.prod_range_one]
        rfl
      have d1 : dBlk (blkOf X.B.R.r X.B.R.t) 1 g =
          Formalism.L2.Col.blkDet X.B.R.nV _ (Formalism.L2.Col.coarse X.B.R.r [X.B.R.t]) 1 ⟨g, hb⟩ := (GlobalTheory.T.dBlk_eq_blkDet_coarse hnV g hb).1
      have d2 : dBlk (blkOf X.toD7.R.r X.toD7.R.t) 1 (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) w.1
            (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)))) =
          dBlk (blkOf X.B.R.r X.B.R.t) 1 g :=
        (congrArg _ (hcrk w.1)).trans ((generalLinearGroupCastOfEq_diagBlock_eq hrk _ _ _).trans (congrArg _ hgw.symm))
      rw [l1, l2, MonoidHom.inv_apply, inv_inv]
      refine (GlobalTheory.T.liftLevelCharacter_typePrime_eq_columnCharacter X px I U L hI hL i ⟨w.1, hv⟩ _).symm.trans ?_
      exact congrArg _ (d2.trans d1).symm

    · rw [if_neg hv]
      have hq' : (w.1 : Pl X.toD7.host.E) ∈ Formalism.L2.Col.QE I.sel t.1 := (Finset.mem_union.mp w.2).resolve_left hv
      have hb : g ∈ Formalism.L2.Col.blockUT X.B.R.nV _ X.B.R.r [X.B.R.t] := (hHq w hv g).1 hg
      have e : Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w =
          Formalism.L2.Col.mtTyQ X.B.R (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) (Formalism.L2.Col.QE I.sel t.1)
            ⟨w.1, hq'⟩ := Formalism.L2.Col.LevFam.glue_of_not _ _ w hv
      have l1 : ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).lam ⟨g, hg⟩ =
          ((Formalism.L2.Col.mtTyQ X.B.R (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) (Formalism.L2.Col.QE I.sel t.1)
            ⟨w.1, hq'⟩).lam ⟨g, hb⟩)⁻¹ := by
        show ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w).lam⁻¹) ⟨g, hg⟩ = _
        rw [MonoidHom.inv_apply, lev_eq_of_eq e g hg hb]
      have l2 : (Formalism.L2.Col.mtTyQ X.B.R (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) (Formalism.L2.Col.QE I.sel t.1)
            ⟨w.1, hq'⟩).lam ⟨g, hb⟩ =
          Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) w.1
            (Formalism.L2.Col.blkDet X.B.R.nV _ (Formalism.L2.Col.coarse X.B.R.r [X.B.R.t]) 1 ⟨g, hb⟩) := by
        show Formalism.L2.Col.lamQP (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) w.1 X.B.R.nV X.B.R.r X.B.R.t ⟨g, hb⟩ = _
        unfold Formalism.L2.Col.lamQP Formalism.L2.Col.lamQ
        rw [Formalism.L2.Col.detChar_apply]
        simp only [List.length_singleton, Finset.prod_range_one]
      have d1 : dBlk (blk2 X.B.R.r) 1 g =
          Formalism.L2.Col.blkDet X.B.R.nV _ (Formalism.L2.Col.coarse X.B.R.r [X.B.R.t]) 1 ⟨g, hb⟩ := (GlobalTheory.T.dBlk_eq_blkDet_coarse hnV g hb).2
      have d2 : dBlk (blk2 X.toD7.R.r) 1 (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) w.1
            (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)))) =
          dBlk (blk2 X.B.R.r) 1 g :=
        (congrArg _ (hcrk w.1)).trans ((generalLinearGroupCastOfEq_twoBlock_diagBlock_eq hrk _ _).trans (congrArg _ hgw.symm))
      rw [l1, l2]
      refine (map_inv (Units.map X.toD7.what₂.embLL.toMonoidHom) _).trans ?_
      congr 1
      refine (GlobalTheory.T.liftResidueTwistCharacter_eq_resChar X px I U L hI hV hL t w.1 hq' _).symm.trans ?_
      exact congrArg _ (d2.trans d1).symm

  obtain ⟨φ, hφ⟩ : ∃ φ : Pl X.toD7.host.E → ℂˣ, ∀ PP, φ PP =
      if PP ∈ (X.B.primes px).vGs then
        L.chi ((i : ℕ) + 1) PP (dBlk (blkOf X.toD7.R.r X.toD7.R.t) 1 (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) PP
          (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)))))
      else (L.xiR t PP (dBlk (blk2 X.toD7.R.r) 1 (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) PP
          (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X))))))⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have e1 : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩ =
      levFn 1 (flag1L (L.datVt i t))
        (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X))) := by
    refine (levEnv_chi _ _ _ _ hk).trans ?_
    rw [hM k, hβ]
  have hch : (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩)⁻¹ : ℂˣ) =
      Units.map X.toD7.what₂.embLL.toMonoidHom ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr
        (Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
          ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
            (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).symm k))) := by
    refine (congrArg (·⁻¹) e1).trans ?_
    refine Eq.trans ?_ (congrArg (Units.map X.toD7.what₂.embLL.toMonoidHom)
      (Formalism.L2.Col.LevFam.chr_apply (X := X.B.fields) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv _).symm)
    refine Eq.trans ?_ (map_prod _ _ _).symm
    refine Eq.trans ?_ (Finset.prod_congr rfl fun w _ => ((perw w _ _ (hredw w)).trans (hφ w.1).symm).symm)
    refine (congrArg (·⁻¹) (levFn_datVt X L i t _)).trans ?_
    refine prod_glue (E := X.toD7.host.E) L.Pg (L.Q t) _ _ hPg hQ hdisj _ _ φ (fun PP hP => ?_) (fun PP hP => ?_)
    · exact (hφ PP).trans ((if_pos hP).trans (inv_inv _).symm)
    · exact (hφ PP).trans (if_neg (Finset.disjoint_right.1 hdisj hP))
  refine ⟨hch, fun hk1 => ?_⟩
  have hred1 := (Bridge.mem_principal_congruence_iff X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
    (((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
      (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).symm k : Formalism.L2.Col.JH _ _ _ _ _) :
        Formalism.L2.Col.J0 X.toD7.sp.cm X.B.R.nV ∅)).1 (by rw [hm1]; exact hk1)
  refine inv_eq_one.mp (hch.trans ?_)
  refine (congrArg (Units.map X.toD7.what₂.embLL.toMonoidHom)
    (chr_eq_one (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv _ hred1)).trans ?_
  exact map_one _

end GlobalTheory.Mem.LevPres
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftAdelicForm_level_type_eq_columnLevel : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L →
    ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i)),
    (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) →
    ∃ hJ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J =
        (Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).map eG.toMonoidHom,
      ∀ (k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp)
        (hk : eG (k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J),
        (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩)⁻¹ : ℂˣ) =
          Units.map X.toD7.what₂.embLL.toMonoidHom ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr
            (Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
              ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _).symm k))) ∧
        ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ Bridge.principalCongruenceSubgroup X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) →
          (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩ = 1) := by
  atlas_forward_decl GlobalTheory.Mem.LevPres.lev_type_eq
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.TransportRead

theorem transport_ext_eq : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ G' Γ' : Type}
    [Group G] [Group Γ] [Group G'] [Group Γ'] {ι : Γ →* G} {J : Subgroup G} (A : Bridge.AdPts S ι J) (h : S.Ok)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v))
    {ι' : Γ' →* G'} {ρ' : Γ' →* Module.End ℂ W} {J' : Subgroup G'} {χ' : J' →* ℂˣ}
    (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ)
    (hJ : J' = J.map eG.toMonoidHom) (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k)
    (f : (S.toCSD h).Forms) (g : G'),
    ((Bridge.classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).transport eG eΓ hι hρ hJ hχ).ext (f : S.Cl → S.V) g =
      coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q (eG.symm g))) := by
  intro K _ _ _ S G Γ G' Γ' _ _ _ _ ι J A h W _ _ σ ρ χ coef hli hspan hpair hK1 hgl ι' ρ' J' χ' eG eΓ hι hρ hJ hχ f g
  set P' := (Bridge.classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).transport eG eΓ hι hρ hJ hχ with hP'
  have hJ' : ∀ x, x ∈ J' ↔ eG.symm x ∈ J := fun x => by subst hJ; exact Subgroup.mem_map_equiv
  have hspec := P'.dec_spec g
  set γ' := P'.decG g
  set c := P'.decC g
  set k' := P'.decK g
  have hy : P'.y c = eG (A.y c) := rfl
  have hc : P'.coef = coef := rfl
  let k'' : J := ⟨eG.symm (k' : G'), (hJ' _).1 k'.2⟩
  have hg : eG.symm g = ι (eΓ.symm γ') * A.y c * (k'' : G) := by
    have e : ι (eΓ.symm γ') = eG.symm (ι' γ') := by
      rw [MulEquiv.eq_symm_apply, ← hι, MulEquiv.apply_symm_apply]
    rw [e, hspec, hy]
    simp only [map_mul, MulEquiv.symm_apply_apply, k'']
  have hq : A.q (eG.symm g) = A.gl (eΓ.symm γ', k''⁻¹) • S.outSec.rep c := by
    rw [hg, A.q_mul, A.q_y]
  set φ := (S.res h).symm f with hφ
  have hφc : ((φ : S.EqFun) : S.D → S.V) (S.outSec.rep c) = (f : S.Cl → S.V) c := by
    have := Formalism.L2.Col.GSD.resOf_apply S h S.outSec φ c
    rw [← this]
    show (((S.res h) φ).1 : S.Cl → S.V) c = (f : S.Cl → S.V) c
    rw [hφ, LinearEquiv.apply_symm_apply]
  have hk : k' = ⟨eG (k'' : G), by simp only [k'', MulEquiv.apply_symm_apply]; exact k'.2⟩ :=
    Subtype.ext (by simp only [k'', MulEquiv.apply_symm_apply])
  rw [hq, φ.2, hφc, hgl]
  show (χ' k' : ℂ) • ρ' γ' (P'.coef ((f : S.Cl → S.V) c)) = _
  rw [hc, hk, hχ]
  have hγ : ρ' γ' = ρ (eΓ.symm γ') := by rw [← hρ, MulEquiv.apply_symm_apply]
  rw [hγ, map_inv, inv_inv, Units.smul_def]

end GlobalTheory.Mem.TransportRead
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedClassSetPresentation_reads_equivariant : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ G' Γ' : Type}
    [Group G] [Group Γ] [Group G'] [Group Γ'] {ι : Γ →* G} {J : Subgroup G} (A : Bridge.AdPts S ι J) (h : S.Ok)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v))
    {ι' : Γ' →* G'} {ρ' : Γ' →* Module.End ℂ W} {J' : Subgroup G'} {χ' : J' →* ℂˣ}
    (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ)
    (hJ : J' = J.map eG.toMonoidHom) (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k)
    (f : (S.toCSD h).Forms) (g : G'),
    ((Bridge.classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).transport eG eΓ hι hρ hJ hχ).ext (f : S.Cl → S.V) g =
      coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q (eG.symm g))) := by
  atlas_forward_decl GlobalTheory.Mem.TransportRead.transport_ext_eq
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftLatStd

theorem hLat_eq_decoPt_N : ∀ (X : Stages) (i : Fin X.toD7.R.m) (Λ : Submodule (𝓞 X.toD7.host.E) (Fin (Vc X.toD7 i).rank → X.toD7.host.E)),
    IsSDFrame (Vc X.toD7 i) 1 Λ 1 → ∀ (SG : Finset (Pl X.toD7.host.E))
    (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i)),
    (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) →
    ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV,
      Bridge.hLat (Vc X.toD7 i) (eG x) =
        (Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ SG (QuotientGroup.mk x)).1.N.map
          (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (LiftBrg.rkEq X i)).symm).toLinearMap := by
  intro X i Λ hΛ SG eG hx x
  have hΛ' := hΛ
  obtain ⟨c, hfr, -⟩ := hΛ'
  rw [GlobalTheory.HLatMove.hLat_eq_span hΛ, Formalism.L2.Col.decoPt_mk]
  unfold Formalism.L2.Col.decoOf
  rw [dif_pos (Formalism.L2.Col.decorated_lattice_exists _ _ _ _ _ x.2)]
  set h := eG x with hh
  set g := Formalism.UG.bc (swapAE X.toD7) (h : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E)) with hg
  have hxg : (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) = LiftBrg.castGL (LiftBrg.rkEq X i).symm g := (hx x).symm
  have hL : ∀ y : Fin (Vc X.toD7 i).rank → X.toD7.host.E,
      (h.1⁻¹).1 *ᵥ (fun j => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F) ⊗ₜ[X.toD7.host.F] y j) ∈
          GlobalTheory.AdLat.hat X.toD7.host.F (Λ : Set (Fin (Vc X.toD7 i).rank → X.toD7.host.E)) ↔
        ∀ j, ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) j ∈
          Formalism.L2.Herm.intAf X.toD7.host.F X.toD7.host.E := by
    intro y
    have e : ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) =
        fun j => Algebra.TensorProduct.comm X.toD7.host.F _ X.toD7.host.E
          (((h.1⁻¹).1 *ᵥ (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F) ⊗ₜ[X.toD7.host.F] y k)) j) := by
      rw [hg, ← map_inv]
      funext j
      change _ = swapAE X.toD7 _
      rw [RingHom.map_mulVec (swapAE X.toD7)]
      rfl
    have e1 := hfr ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k)))
    rw [inv_one, Units.val_one, Matrix.one_mulVec] at e1
    rw [← e1, e]
    constructor
    · intro hz
      exact GlobalTheory.PrincInLevel.swap_mem_hatL Λ _ hz
    · intro hz
      have := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ hz
      simpa only [AlgEquiv.symm_apply_apply] using this
  have hR : ∀ y : Fin (Vc X.toD7 i).rank → X.toD7.host.E,
      y ∈ (Formalism.UG.CS.globLat (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (Formalism.L2.Col.stdLat X.toD7.host.E X.B.R.nV)).map
          (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (LiftBrg.rkEq X i)).symm).toLinearMap ↔
        ∀ j, ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) j ∈
          Formalism.L2.Herm.intAf X.toD7.host.F X.toD7.host.E := by
    intro y
    rw [Submodule.mem_map_equiv, LinearEquiv.funCongrLeft_symm, Formalism.L2.Col.mem_globLat]
    unfold Formalism.L2.Col.pullV
    rw [hxg, ← map_inv]
    simp only [LiftBrg.castGL, Units.coe_mapEquiv, Equiv.symm_symm, LinearEquiv.funCongrLeft_apply]
    simp only [LinearMap.funLeft_apply]
    have e2 : ∀ (M : Matrix (Fin (Vc X.toD7 i).rank) (Fin (Vc X.toD7 i).rank) (Lev.EAf X.toD7)),
        ((Matrix.reindexAlgEquiv (Lev.EAf X.toD7) (Lev.EAf X.toD7) (finCongr (LiftBrg.rkEq X i).symm)).toRingEquiv.toMulEquiv M) *ᵥ
          (fun a => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y (finCongr (LiftBrg.rkEq X i) a))) =
        fun a => (M *ᵥ fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k)) (finCongr (LiftBrg.rkEq X i) a) := by
      intro M
      change Matrix.reindexAlgEquiv (Lev.EAf X.toD7) (Lev.EAf X.toD7) (finCongr (LiftBrg.rkEq X i).symm) M *ᵥ _ = _
      rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
      funext a
      simp [Function.comp_def]
    rw [e2]
    exact ⟨fun H j => by simpa using H ((finCongr (LiftBrg.rkEq X i)).symm j), fun H a => H _⟩
  refine le_antisymm (Submodule.span_le.2 fun y hy => (hR y).2 ((hL y).1 hy)) fun y hy => Submodule.subset_span ((hL y).2 ((hR y).1 hy))

end GlobalTheory.Mem.R3.LiftLatStd
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedStdLattice_eq_decoratedLattice_reindexed : ∀ (X : Stages) (i : Fin X.toD7.R.m) (Λ : Submodule (𝓞 X.toD7.host.E) (Fin (Vc X.toD7 i).rank → X.toD7.host.E)),
    IsSDFrame (Vc X.toD7 i) 1 Λ 1 → ∀ (SG : Finset (Pl X.toD7.host.E))
    (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i)),
    (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) →
    ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV,
      Bridge.hLat (Vc X.toD7 i) (eG x) =
        (Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ SG (QuotientGroup.mk x)).1.N.map
          (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (LiftBrg.rkEq X i)).symm).toLinearMap := by
  atlas_forward_decl GlobalTheory.Mem.R3.LiftLatStd.hLat_eq_decoPt_N
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormLevelPrimes_isSplitSet : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ t : TupU I U, Formalism.L2.DIV.IsSplitSet (LiftBrg.sgL X I U t) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL | exact GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL | (intros; apply GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftPresStd

theorem vv_cast_equiv : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι]
    (emb : ι → E →+* K) {n n' : ℕ} (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n'),
    (∀ τ a, (lam τ).w a = (lam' τ).w (Fin.cast h a)) →
    ∃ e : VV K lam ≃ₗ[K] VV K lam',
      (∀ (g : GL (Fin n') E) v, e (rhoVr emb lam (LiftBrg.castGL h.symm g) v) = rhoVr emb lam' g (e v)) ∧
      (∀ (J : Matrix (Fin n) (Fin n) E) x y,
        pairVr emb lam' (J.reindex (finCongr h) (finCongr h)) (e x) (e y) = pairVr emb lam J x y) ∧
      (∀ N : Submodule (𝓞 E) (Fin n → E), (nabAtr emb lam N).map (e.toLinearMap.restrictScalars (𝓞 K)) =
        nabAtr emb lam' (N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr h).symm).toLinearMap)) ∧
      (∀ N : Submodule (𝓞 E) (Fin n → E), (delAtr emb lam N).map (e.toLinearMap.restrictScalars (𝓞 K)) =
        delAtr emb lam' (N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr h).symm).toLinearMap)) ∧
      (∀ i j, (bVV K lam').repr (e (bVV K lam i)) j ∈ Formalism.DivisionValues.cmMax K) ∧
      (∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (c0 : VV K lam' →ₛₗ[σ] W),
        LinearIndependent ℂ (fun i => c0 (bVV K lam' i)) → Submodule.span ℂ (Set.range fun i => c0 (bVV K lam' i)) = ⊤ →
        LinearIndependent ℂ (fun i => c0 (e (bVV K lam i))) ∧ Submodule.span ℂ (Set.range fun i => c0 (e (bVV K lam i))) = ⊤) := by
  intro E K _ _ _ _ _ ι _ emb n n' h lam lam' hl
  subst h
  have hlam : lam = lam' := by
    funext τ
    have h1 := hl τ
    rcases hw : lam τ with ⟨w, hw1⟩
    rcases hw' : lam' τ with ⟨w', hw1'⟩
    rw [hw, hw'] at h1
    have : w = w' := funext fun a => by simpa using h1 a
    subst this
    rfl
  subst hlam
  have hN : ∀ N : Submodule (𝓞 E) (Fin n → E),
      N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr (rfl : n = n)).symm).toLinearMap = N := by
    intro N
    ext x
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      convert hy using 1
      funext a
      rfl
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨LinearEquiv.refl K _, fun g v => ?_, fun J x y => ?_, fun N => ?_, fun N => ?_, fun i j => ?_, fun W _ _ σ c0 h1 h2 => ⟨h1, h2⟩⟩
  · have : LiftBrg.castGL (rfl : n = n).symm g = g := by ext a b; simp [LiftBrg.castGL]
    rw [this]; rfl
  · have : J.reindex (finCongr (rfl : n = n)) (finCongr (rfl : n = n)) = J := by ext a b; simp
    rw [this]; rfl
  · rw [hN]; exact Submodule.map_id _
  · rw [hN]; exact Submodule.map_id _
  · show (bVV K lam).repr (bVV K lam i) j ∈ Formalism.DivisionValues.cmMax K
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem ufGL_ratHom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (γ : Formalism.L2.Col.URat hc n),
    Formalism.L2.Col.ufGL E n (Formalism.L2.Col.ratHom hc n γ) = (γ : GL (Fin n) E) := by
  intro F E _ _ _ _ _ _ hc n γ
  apply Units.ext
  ext a b
  simp [Formalism.L2.Col.ufGL, Formalism.L2.Col.toGLm, Formalism.L2.Col.ratHom, Formalism.UG.glEquiv, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

theorem formRho_colGl {X : Formalism.L2.Col.Fields} {n : ℕ} [NeZero n] {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (hc : Formalism.BasicNotions.CMData X.F X.E)
    (C : Formalism.L2.Col.CoefPk X n (Formalism.L2.Col.DecoSet X.E n ∅ SG)) (Λ : Formalism.L2.Col.LevFam X.E X.K n SG)
    (γ : Formalism.L2.Col.URat hc n) (k : Bridge.colJ hc n ∅ SG Λ.grp) (v : C.V) :
    (Formalism.L2.Col.formGSD C Λ).ρ (Bridge.colGl (Formalism.L2.Col.rf_onDeco C Λ) (γ, k)) v =
      ((Λ.chr (Formalism.L2.Col.redH hc n ∅ SG Λ.grp ((Bridge.colJEquiv hc n ∅ SG Λ.grp).symm k)) : X.Kˣ) : X.K) •
        C.rho (Formalism.L2.Col.ratHom hc n γ) v := rfl

theorem castGL_symm_castGL {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) :
    LiftBrg.castGL h.symm (LiftBrg.castGL h g) = g := by
  subst h
  ext a b
  simp [LiftBrg.castGL]

theorem exists_oneCoef_presStd : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∃ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) ∧
      ∀ t : TupU I U, ∃ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 P ∧
        (∀ v, P.coef v = c v) ∧ Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef P (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) := by
  intro X px I hX U Xg tr L eG0 hI hV hL hG cV i c0L hcV hmap hin hβ hgram
  obtain ⟨e0, he_rho, he_pair, he_nab, he_del, he_rat, he_li⟩ :=
    vv_cast_equiv X.B.fields.emb (LiftBrg.rkEq X i) (X.B.wts.lamV ((i : ℕ) + 1))
      (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) (GlobalTheory.T.baseWeight_eq_forcedLiftWeight X i)
  let c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W :=
    { toFun := fun v => c0L (e0 v)
      map_add' := fun v w => by show c0L (e0 (v + w)) = c0L (e0 v) + c0L (e0 w); rw [map_add]; exact c0L.map_add _ _
      map_smul' := fun a v => by show c0L (e0 (a • v)) = _; rw [LinearEquiv.map_smul]; exact c0L.map_smulₛₗ a (e0 v) }
  have hc : ∀ v, c v = c0L (e0 v) := fun v => rfl
  have hint : ∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v) := by
    intro γ γE h v
    exact (congrArg c0L (he_rho γE v)).trans (hmap.1 γ γE h (e0 v))
  refine ⟨c, hint, fun t => ?_⟩
  obtain ⟨eG, eΓ, hchar, hι, hrat⟩ := GlobalTheory.T.exists_unitaryGroups_equiv_unitForm_gram_one X i hgram
  obtain ⟨hJ, hχ⟩ := GlobalTheory.T.liftAdelicForm_level_type_eq_columnLevel X px I U L hI hV hL i t eG hchar

  letI : Algebra X.toD7.host.F X.B.fields.E := inferInstanceAs (Algebra X.toD7.host.F X.toD7.host.E)
  have hneg : X.toD7.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  have hgr : (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) =
      (1 : Matrix (Fin X.B.R.nV) (Fin X.B.R.nV) X.toD7.host.E).reindex (finCongr (LiftBrg.rkEq X i)) (finCongr (LiftBrg.rkEq X i)) := by
    rw [hneg, if_neg (by simp), hgram]
    ext a b
    simp [Matrix.one_apply]
  have hSG : Formalism.L2.Col.DecoPtSurj X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) :=
    Formalism.L2.Col.decoPtSurj_of _ _ _ _ (Formalism.L2.Col.unimodGenus_holds _ _) Formalism.L2.DIV.reduction_surjective_bis
      (by classical convert GlobalTheory.T.rowFormLevelPrimes_isSplitSet X px I U L hI hL t using 1; exact Finset.empty_union _) (Finset.disjoint_empty_left _)
  let o := Formalism.L2.Col.rf_onDeco (X := X.B.fields) (n := X.B.R.nV) (ST := ∅) (SG := LiftBrg.sgL X I U t)
    (Formalism.L2.Col.mtVal (Pr := X.B.primes px) X.B.wts ((i : ℕ) + 1) _) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv
  have hmem : ∀ k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
      (eG.toMonoidHom.comp (Subgroup.subtype _)) k ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J := fun k => by
    rw [hJ]; exact Subgroup.mem_map_of_mem _ k.2
  let χc := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ.comp ((eG.toMonoidHom.comp (Subgroup.subtype _)).codRestrict _ hmem)
  have hχc : ∀ k, ((χc k)⁻¹ : ℂˣ) = Units.map X.toD7.what₂.embLL.toMonoidHom ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr
      (Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
        ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _).symm k))) := fun k => (hχ k (hmem k)).1
  have hK1 : ∀ k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
      (k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ Bridge.principalCongruenceSubgroup X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) → χc k = 1 :=
    fun k hk => (hχ k (hmem k)).2 hk
  have hli := he_li (cV i).W X.toD7.what₂.embLL c0L hmap.2.1 hmap.2.2
  have hpair : ∀ x x', inner ℂ (c x) (c x') = X.toD7.what₂.embLL ((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).pair x x') := by
    intro x x'
    refine (hin (e0 x) (e0 x')).trans ?_
    congr 1
    rw [hgr]
    exact he_pair 1 x x'
  have hgl : ∀ (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) k (v : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V),
      c ((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).ρ (Bridge.colGl o (γ, k)) v) =
        ((χc k)⁻¹ : ℂˣ) • ((cV i).coef.ρ.comp eΓ.toMonoidHom) γ (c v) := by
    intro γ k v
    rw [show (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).ρ (Bridge.colGl o (γ, k)) v = _ from
      formRho_colGl (X := X.B.fields) X.toD7.sp.cm _ _ γ k v]
    refine (c.map_smulₛₗ _ _).trans ?_
    have e3 : (Formalism.L2.Col.mtVal (Pr := X.B.primes px) X.B.wts ((i : ℕ) + 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)).rho
        (Formalism.L2.Col.ratHom X.toD7.sp.cm X.B.R.nV γ) v =
        rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1))
          (LiftBrg.castGL (LiftBrg.rkEq X i).symm (LiftBrg.castGL (LiftBrg.rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) v := by
      show rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1))
        (Formalism.L2.Col.ufGL X.toD7.host.E X.B.R.nV (Formalism.L2.Col.ratHom X.toD7.sp.cm X.B.R.nV γ)) v = _
      rw [ufGL_ratHom]
      exact congrArg (fun g => rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) g v) (castGL_symm_castGL (LiftBrg.rkEq X i) _).symm
    have e2 := hint (eΓ γ) _ (hrat γ) v
    have e4 := (congrArg c e3).trans e2
    rw [hχc k, Units.smul_def]
    erw [e4]
    rfl

  let A := Bridge.colAdPts o hSG
  let P0 := Bridge.colClassPres (hc := X.toD7.sp.cm) o hSG (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) X.toD7.what₂.embLL
    ((cV i).coef.ρ.comp eΓ.toMonoidHom) χc c hli.1 hli.2 hpair hK1 hgl
  let P : LiftBrg.PresL X I hX U Xg tr L cV i t :=
    P0.transport eG eΓ hι (fun _ => rfl) hJ (fun k hk => rfl)
  refine ⟨P, ?_, fun v => rfl, e0, he_rat, fun x => rfl, ?_, ?_, ?_⟩

  · intro f g
    have h5 := GlobalTheory.T.transportedClassSetPresentation_reads_equivariant (ι' := Bridge.ratF (Vc X.toD7 i)) (ρ' := (cV i).coef.ρ) (J' := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J)
      (χ' := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ) A (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) X.toD7.what₂.embLL
      ((cV i).coef.ρ.comp eΓ.toMonoidHom) χc c hli.1 hli.2 hpair hK1 hgl eG eΓ hι (fun _ => rfl) hJ (fun k hk => rfl) f g
    refine h5.trans ?_
    have hq : A.q (eG.symm g) = LiftBrg.ptL X I U i t 1 1 g := by
      show Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (eG.symm g)) = _
      rw [Formalism.L2.Col.decoPt_mk]
      unfold LiftBrg.ptL
      congr 1
      have := hchar (eG.symm g)
      rw [MulEquiv.apply_symm_apply] at this
      rw [this]
      simp
    erw [hq]
    rfl
  · intro x x'
    rw [hgr]
    exact he_pair 1 x x'
  · intro cl
    have h6 := GlobalTheory.T.translatedStdLattice_eq_decoratedLattice_reindexed X i (L.ΛV i) (by rw [← hβ]; exact hL.is.βV i) (LiftBrg.sgL X I U t) eG hchar (A.y cl)
    have hy := A.q_y cl
    have hy' : Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (A.y cl)) =
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).outSec.rep cl := hy
    refine Eq.trans ?_ (congrArg (nabAtr (labLL X.toD7) (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ)) h6).symm
    rw [hy']
    exact he_nab _
  · intro cl
    have h6 := GlobalTheory.T.translatedStdLattice_eq_decoratedLattice_reindexed X i (L.ΛV i) (by rw [← hβ]; exact hL.is.βV i) (LiftBrg.sgL X I U t) eG hchar (A.y cl)
    have hy := A.q_y cl
    have hy' : Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (A.y cl)) =
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).outSec.rep cl := hy
    refine Eq.trans ?_ (congrArg (delAtr (labLL X.toD7) (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ)) h6).symm
    rw [hy']
    exact he_del _

end GlobalTheory.Mem.R3.LiftPresStd
end
end
