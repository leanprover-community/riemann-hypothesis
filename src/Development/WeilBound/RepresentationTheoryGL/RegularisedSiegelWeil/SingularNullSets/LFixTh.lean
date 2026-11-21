import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTest
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWA

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open PositivityTheory.Rg.Rsw.L

variable {D : D7} {ρ p : ℕ}

theorem det_mem_subring {R : Type} [CommRing R] (T : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, M i j ∈ T) : M.det ∈ T := by
  let N : Matrix (Fin n) (Fin n) T := fun i j => ⟨M i j, h i j⟩
  have e : M = T.subtype.mapMatrix N := by ext i j; rfl
  rw [e, ← RingHom.map_det]
  exact (N.det).2

theorem evFin_eInf (v : Pl D) : evFin D.host.F v (GlobalTheory.ThK.ConeEuler.eInf D.host.F) = 0 := by
  rw [LFixW.evFin_apply, GlobalTheory.ThK.ConeEuler.eInf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd, LinearMap.inl_apply]
  rfl

theorem unitArch_eq_one (l : (AE D)ˣ) (hinf : ∀ w, compInf D.host.F D.host.E w (l : AE D) = 1) :
    GlobalTheory.ThK.ConeEuler.unitArch D.host.F D.host.E l = 1 := by
  apply Units.ext
  apply LIdemEx.ae_ext
  · intro w
    rw [GlobalTheory.IdeleCyl.compInf_unitArch, hinf, Units.val_one, map_one]
  · intro v
    change compFin D.host.F D.host.E v (GlobalTheory.ThK.ConeEuler.eInf D.host.F • (l : AE D) +
      (1 - GlobalTheory.ThK.ConeEuler.eInf D.host.F) • 1) = cv D v ((1 : (AE D)ˣ) : AE D)
    rw [map_add, GlobalTheory.ThK.compFin_smul, GlobalTheory.ThK.compFin_smul, evFin_eInf, map_sub, map_one, evFin_eInf, sub_zero,
      zero_smul, zero_add, one_smul, Units.val_one]

theorem unitAt_eq_one (l : (AE D)ˣ) (v : Pl D) (hat : cv D v (l : AE D) = 1) :
    GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l = 1 := by
  apply Units.ext
  change GlobalTheory.ThK.ConeEuler.eFin v • (l : AE D) + (1 - GlobalTheory.ThK.ConeEuler.eFin v) • 1 = ((1 : (AE D)ˣ) : AE D)
  have h0 : compFin D.host.F D.host.E v ((l : AE D) - 1) = 0 := by
    rw [map_sub, map_one]; exact sub_eq_zero.2 hat
  have hk := GlobalTheory.InertLagUniq.liftV_one_smul_eq_zero (E := D.host.E) v _ h0
  have e : GlobalTheory.ThK.ConeEuler.eFin v • (l : AE D) + (1 - GlobalTheory.ThK.ConeEuler.eFin v) • (1 : AE D) =
      1 + GlobalTheory.ThK.ConeEuler.eFin v • ((l : AE D) - 1) := by
    rw [sub_smul, one_smul, smul_sub]; abel
  rw [e, Units.val_one]
  change 1 + GlobalTheory.LatVac.liftV v 1 • ((l : AE D) - 1) = 1
  rw [hk, add_zero]

theorem chr_abs_one {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {b₀ : HermE D ρ} {S : Finset (Pl D)}
    (hS : ∀ v ∉ S, GoodPl χ b₀ v) (l : (AE D)ˣ) (hA : GlobalTheory.ThK.ConeEuler.unitArch D.host.F D.host.E l = 1)
    (hAt : ∀ v ∈ S, GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l = 1)
    (hmem : ∀ v ∉ S, GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l ∈ GlobalTheory.ThK.unitsAt D.host.E v) :
    χ l = 1 ∧ absE D.host.F D.host.E l = 1 := by
  have key := (GlobalTheory.ThK.ConeEulerChr.chr_abs_eq_finprod χ hχ.1 l 1).2
  have hfp : (∏ᶠ v : Pl D, (χ (GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l) : ℂ) *
      ((absE D.host.F D.host.E (GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l) : ℝ) : ℂ) ^ 1) = 1 := by
    rw [finprod_congr (g := fun _ => (1 : ℂ)) ?_, finprod_one]
    intro v
    by_cases hv : v ∈ S
    · rw [hAt v hv]; simp
    · have hm := hmem v hv
      rw [(hS v hv).unr _ hm, GlobalTheory.ThK.absE_of_mem_unitsAt hm]; simp
  rw [hfp, hA] at key
  simp only [map_one, Circle.coe_one, NNReal.coe_one, Complex.ofReal_one, mul_one, pow_one] at key
  have habs : absE D.host.F D.host.E l = 1 := by
    have hn := congrArg norm key
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, norm_one,
      Real.norm_of_nonneg (NNReal.coe_nonneg _)] at hn
    exact_mod_cast hn
  refine ⟨?_, habs⟩
  rw [habs, NNReal.coe_one, Complex.ofReal_one, mul_one] at key
  exact Circle.coe_eq_one.1 key

theorem levi_chr {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {b₀ : HermE D ρ} {S : Finset (Pl D)}
    (hS : ∀ v ∉ S, GoodPl χ b₀ v) (a : GL (Fin p) (AE D))
    (h1 : ∀ i j w, compInf D.host.F D.host.E w (a.1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j)
    (h2 : ∀ i j, ∀ v ∈ S, cv D v (a.1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j)
    (h3 : ∀ i j, ∀ v ∉ S, cv D v (a.1 i j) ∈ intLoc D.host.F D.host.E v ∧
      cv D v ((a⁻¹).1 i j) ∈ intLoc D.host.F D.host.E v) :
    χ (Matrix.GeneralLinearGroup.det a) = 1 ∧ absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
  have hv0 : ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = (a : Matrix (Fin p) (Fin p) (AE D)).det :=
    Matrix.GeneralLinearGroup.val_det_apply a
  have hv1 : (((Matrix.GeneralLinearGroup.det a)⁻¹ : (AE D)ˣ) : AE D) =
      ((a⁻¹ : GL (Fin p) (AE D)) : Matrix (Fin p) (Fin p) (AE D)).det := by
    rw [← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply _
  have hinf : ∀ w, compInf D.host.F D.host.E w ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = 1 := by
    intro w
    rw [hv0, RingHom.map_det]
    have e : (compInf D.host.F D.host.E w).mapMatrix (a : Matrix (Fin p) (Fin p) (AE D)) = 1 := by
      ext i j; exact h1 i j w
    rw [e, Matrix.det_one]
  have hat : ∀ v ∈ S, cv D v ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = 1 := by
    intro v hv
    rw [hv0, RingHom.map_det]
    have e : (cv D v).mapMatrix (a : Matrix (Fin p) (Fin p) (AE D)) = 1 := by
      ext i j; exact h2 i j v hv
    rw [e, Matrix.det_one]
  have hint : ∀ v ∉ S, cv D v ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) ∈ intLoc D.host.F D.host.E v ∧
      cv D v (((Matrix.GeneralLinearGroup.det a)⁻¹ : (AE D)ˣ) : AE D) ∈ intLoc D.host.F D.host.E v := by
    intro v hv
    rw [hv0, hv1, RingHom.map_det, RingHom.map_det]
    exact ⟨det_mem_subring _ _ fun i j => (h3 i j v hv).1, det_mem_subring _ _ fun i j => (h3 i j v hv).2⟩
  refine chr_abs_one hχ hS _ (unitArch_eq_one _ hinf) (fun v hv => unitAt_eq_one _ v (hat v hv)) fun v hv => ?_
  refine GlobalTheory.ThK.mem_unitsAt.2 ⟨GlobalTheory.ThK.ConeEuler.unitAt_mem v _, ?_, ?_⟩
  · rw [GlobalTheory.ThK.ConeEuler.compFin_unitAt_self]; exact (hint v hv).1
  · rw [← map_inv, GlobalTheory.ThK.ConeEuler.compFin_unitAt_self]; exact (hint v hv).2

end PositivityTheory.Rg.Rsw.L.LFixTh

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open PositivityTheory.Rg.Rsw.L

variable {D : D7} {ρ p n : ℕ}

theorem one_cc {R : Type} [Ring R] (i j : Fin n) :
    (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) (Fin.castAdd n i) (Fin.castAdd n j) = (1 : Matrix (Fin n) (Fin n) R) i j := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    exact fun h' => h (Fin.castAdd_injective _ _ h')

theorem map_one_apply {R : Type} [Ring R] (f : AE D →+* R) (i j : Fin n) :
    f ((1 : Mx D n n) i j) = (1 : Matrix (Fin n) (Fin n) R) i j := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]

theorem mat_inv_levi {g : G D p} {a : GL (Fin p) (AE D)} (ha : mat g = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    mat g⁻¹ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
  have h1 : (a⁻¹).1 * a.1 = 1 := a.inv_mul
  have h2 : adj a.1 * adj (a⁻¹).1 = 1 := by
    delta GlobalTheory.MixModel.adj
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one]
  have hprod : blk4 (a⁻¹).1 0 0 (adj a.1) * blk4 a.1 0 0 (adj (a⁻¹).1) = 1 := by
    delta GlobalTheory.StdUnn.blk4
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, h1, h2, Matrix.fromBlocks_one]
    exact Matrix.submatrix_one_equiv _
  delta GlobalTheory.StdUnn.mat at ha ⊢
  rw [map_inv]
  exact Units.inv_eq_of_mul_eq_one_left (by rw [ha]; exact hprod)

private theorem matHom_proj_fst_eq_mat_map_cv (g : G D p) (v : Pl D) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D p)
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (GlobalTheory.StdUnn.Jst D p) v g)).1 = (mat g).map (cv D v) := by
  delta GlobalTheory.AdelicU.proj GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH
  rfl

private theorem exists_mat_apply_eq_one_at_S_and_int_off_S {S : Finset (Pl D)} {h : G D p} (hh : h ∈ KOff D p S) :
    (∀ (w : NumberField.InfinitePlace D.host.F) (i j : Fin (p + p)),
      compInf D.host.F D.host.E w (mat h i j) = (1 : Matrix (Fin (p + p)) (Fin (p + p)) _) i j) ∧
    (∀ v ∈ S, ∀ i j : Fin (p + p), cv D v (mat h i j) = (1 : Matrix (Fin (p + p)) (Fin (p + p)) _) i j) ∧
    (∀ v ∉ S, ∀ i j : Fin (p + p), cv D v (mat h i j) ∈ intLoc D.host.F D.host.E v) := by
  delta PositivityTheory.Rg.Rsw.L.KOff GlobalTheory.AdelicU.levelOff GlobalTheory.AdelicU.finAwayPts at hh
  obtain ⟨hfa, hoff⟩ := Subgroup.mem_inf.mp hh
  obtain ⟨hfin, haway⟩ := Subgroup.mem_inf.mp hfa
  refine ⟨fun w i j => ?_, fun v hv i j => ?_, fun v hv i j => ?_⟩
  · delta GlobalTheory.AdelicU.finPts at hfin
    have h1 := congrArg (fun u : GL (Fin (p + p)) _ => u.1 i j) (MonoidHom.mem_ker.mp hfin)
    have h2 : (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA _) (AlgHom.id (↥D.host.F) D.host.E)) (mat h i j) =
        (1 : Matrix (Fin (p + p)) (Fin (p + p)) _) i j := h1
    have e := Algebra.TensorProduct.map_comp (GlobalTheory.AutFunCompare.evW w) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA (↥D.host.F))
      (AlgHom.id (↥D.host.F) D.host.E) (AlgHom.id (↥D.host.F) D.host.E)
    rw [AlgHom.id_comp] at e
    have hc : compInf D.host.F D.host.E w (mat h i j) =
        (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id (↥D.host.F) D.host.E))
          ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA _) (AlgHom.id (↥D.host.F) D.host.E)) (mat h i j)) :=
      DFunLike.congr_fun e (mat h i j)
    rw [hc, h2]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]
  · delta GlobalTheory.AdelicU.awayPts at haway
    have hker := MonoidHom.mem_ker.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp haway v) hv)
    have h3 := matHom_proj_fst_eq_mat_map_cv h v
    rw [hker, map_one] at h3
    have h4 := congrArg (fun M : Matrix (Fin (p + p)) (Fin (p + p)) _ => M i j) h3
    exact h4.symm
  · have hs := (GlobalTheory.AdelicU.mem_stabLoc_stdLattice_iff.mp
      (Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hoff v) hv))).1 i j
    rw [matHom_proj_fst_eq_mat_map_cv] at hs
    exact hs

theorem levi_blocks {S : Finset (Pl D)} {g : G D p} (hg : g ∈ KOff D p S) {a : GL (Fin p) (AE D)}
    (ha : mat g = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    (∀ i j, (∀ w, compInf D.host.F D.host.E w (a.1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j ∧
      compInf D.host.F D.host.E w ((a⁻¹).1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j) ∧
      (∀ v ∈ S, cv D v (a.1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j ∧
        cv D v ((a⁻¹).1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j) ∧
      (∀ v ∉ S, cv D v (a.1 i j) ∈ intLoc D.host.F D.host.E v ∧ cv D v ((a⁻¹).1 i j) ∈ intLoc D.host.F D.host.E v)) := by
  have hgi : g⁻¹ ∈ KOff D p S := inv_mem hg
  obtain ⟨hI, hS, hO⟩ := exists_mat_apply_eq_one_at_S_and_int_off_S hg
  obtain ⟨hI', hS', hO'⟩ := exists_mat_apply_eq_one_at_S_and_int_off_S hgi
  have hA : ∀ i j, mat g (Fin.castAdd p i) (Fin.castAdd p j) = a.1 i j := by
    intro i j
    rw [ha]
    delta GlobalTheory.StdUnn.blk4
    rw [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd,
      Matrix.fromBlocks_apply₁₁]
  have hAi : ∀ i j, mat g⁻¹ (Fin.castAdd p i) (Fin.castAdd p j) = (a⁻¹).1 i j := by
    intro i j
    rw [mat_inv_levi ha]
    delta GlobalTheory.StdUnn.blk4
    rw [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd,
      Matrix.fromBlocks_apply₁₁]
  intro i j
  refine ⟨fun w => ⟨?_, ?_⟩, fun v hv => ⟨?_, ?_⟩, fun v hv => ⟨?_, ?_⟩⟩
  · rw [← hA, hI, one_cc]
  · rw [← hAi, hI', one_cc]
  · rw [← hA, hS v hv, one_cc]
  · rw [← hAi, hS' v hv, one_cc]
  · rw [← hA]
    exact hO v hv _ _
  · rw [← hAi]
    exact hO' v hv _ _

theorem levi_good {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {g : G D p} (hg : g ∈ KOff D p S)
    {a : GL (Fin p) (AE D)} (ha : mat g = blk4 a.1 0 0 (adj (a⁻¹).1)) (f : Mx D ρ p → ℂ) (hf : Good S e f)
    (y : Mx D ρ p) : f (y * a.1) = f y := by
  have hb := levi_blocks hg ha
  have he1 : ∀ k j, e * a.1 k j = e * (1 : Mx D p p) k j := by
    intro k j
    apply PositivityTheory.Rg.Rsw.L.LIdemEx.ae_ext
    · intro w
      rw [map_mul, map_mul, ((hb k j).1 w).1, map_one_apply]
    · intro v
      rw [map_mul, map_mul, map_one_apply]
      by_cases hv : v ∈ S
      · rw [((hb k j).2.1 v hv).1]
      · rw [he.2 v, if_neg hv, zero_mul, zero_mul]
  have hsmul : e • (y * a.1) = e • y := by
    ext i j
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    calc e * (y * a.1) i j = ∑ k, y i k * (e * a.1 k j) := by
          rw [Matrix.mul_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ k, y i k * (e * (1 : Mx D p p) k j) := Finset.sum_congr rfl fun k _ => by rw [he1]
      _ = e * ∑ k, y i k * (1 : Mx D p p) k j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = e * y i j := by rw [← Matrix.mul_apply, Matrix.mul_one]
  have hint : ∀ (x : Mx D ρ p) (b : Mx D p p), IntOff S x →
      (∀ v ∉ S, ∀ k j, cv D v (b k j) ∈ intLoc D.host.F D.host.E v) → IntOff S (x * b) := by
    intro x b hx hb' v hv i j
    rw [Matrix.mul_apply, map_sum]
    exact Subring.sum_mem _ fun k _ => by
      rw [map_mul]
      exact Subring.mul_mem _ (hx v hv i k) (hb' v hv k j)
  have hyI : IntOff S (y * a.1) ↔ IntOff S y := by
    constructor
    · intro h
      have h' := hint _ (a⁻¹).1 h fun v hv k j => ((hb k j).2.2 v hv).2
      rwa [Matrix.mul_assoc, a.mul_inv, Matrix.mul_one] at h'
    · intro h
      exact hint _ a.1 h fun v hv k j => ((hb k j).2.2 v hv).1
  rw [hf (y * a.1), hf y, hsmul]
  by_cases h : IntOff S y
  · rw [if_pos (hyI.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hyI.mp h')), if_neg h]

end PositivityTheory.Rg.Rsw.L.LFixTh

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

open LFixTh

open Classical in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem fixTh : IdemEx → GenG → GenK → FixTh := by
  intro _ hG hK D ρ p m ψ hψ χ hχ θ _ b₀ hb₀
  obtain ⟨S₁, hS₁⟩ := hK D p
  obtain ⟨S₃, hS₃⟩ := LFixW.psi_kernel hψ
  obtain ⟨S₄, hS₄⟩ := LFixW.ft_supp b₀.1 hb₀ hψ
  have hgood := eventually_goodPl hχ b₀
  refine ⟨S₁ ∪ S₃ ∪ S₄ ∪ (Filter.eventually_cofinite.1 hgood).toFinset, fun S hS e he Ω hΩ hgoodΩ => ?_⟩
  have hSg : ∀ v ∉ S, GoodPl χ b₀ v := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)))
  have hSI := hS₃ S (fun v hv => hS (by simp [hv]))
  have hS4 := hS₄ S (fun v hv => hS (by simp [hv])) e he p m.μ
  have : m.μ.IsAddHaarMeasure := m.hμ.1
  let A' : Set (G D p) := {x | Ω x = Ω 1}
  have hA'c : IsClosed A' := by
    have e : A' = ⋂ y, {x | Ω x y = Ω 1 y} := by
      ext x; simp only [A', Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
    rw [e]
    exact isClosed_iInter fun y => isClosed_eq (hΩ.cont.comp (continuous_id.prodMk continuous_const)) continuous_const
  have hgen : ∀ g ∈ KOff D p S, (IsN g ∨ IsM g ∨ ∃ w u, IsW w ∧ IsN u ∧ u ∈ KOff D p S ∧ g = w * u * w⁻¹) →
      ∀ x ∈ A', g * x ∈ A' := by
    intro g hg hgt x hx
    simp only [A', Set.mem_ofPred_eq] at hx ⊢
    rcases hgt with ⟨b, hb⟩ | ⟨a, ha⟩ | ⟨w, u, hw, ⟨b, hb⟩, hu, rfl⟩
    · funext y
      rw [hΩ.unip g b hb x y, hx]
      by_cases hy : IntOff S y
      · rw [unip_one hSg hSI hg hb hy, one_mul]
      · rw [hgoodΩ y, if_neg hy, mul_zero]
    · have hbl := levi_blocks hg ha
      obtain ⟨h1, h2⟩ := levi_chr hχ hSg a (fun i j w => ((hbl i j).1 w).1) (fun i j v hv => ((hbl i j).2.1 v hv).1)
        (fun i j v hv => (hbl i j).2.2 v hv)
      funext y
      rw [hΩ.levi g a ha x y, hx, h1, h2, levi_good he hg ha _ hgoodΩ y]
      simp [npow]
    · let c : ℂ := (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin p) (AE D))) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin p) (AE D)))) ((ρ : ℂ) / 2)
      have hΦ : ∀ y, Ω (w⁻¹ * x) y = ∫ z, (fun z => c * Ω 1 (-z)) z * ψ (trA (pr b₀ y z).trace) ∂m.μ := by
        intro y
        have e1 : w⁻¹ * x = w * ((w * w)⁻¹ * x) := by group
        rw [e1, hΩ.weyl w hw]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [hΩ.levi _ (-1) (mat_ww hw) x z, hx, Units.val_neg, Units.val_one, Matrix.mul_neg, Matrix.mul_one]
      have hzero : ∀ y, ψ (halfTr (b * pr b₀ y y).trace) * Ω (w⁻¹ * x) y = Ω (w⁻¹ * x) y := by
        intro y
        by_cases hy : IntOff S y
        · rw [unip_one hSg hSI hu hb hy, one_mul]
        · rw [hΦ y, show (∫ z, (fun z => c * Ω 1 (-z)) z * ψ (trA (pr b₀ y z).trace) ∂m.μ) = 0 from
            hS4 this _ (good_neg hgoodΩ c) y hy, mul_zero]
      funext y
      have e2 : w * u * w⁻¹ * x = w * (u * (w⁻¹ * x)) := by group
      have e3 : Ω 1 y = Ω (w * (w⁻¹ * x)) y := by rw [mul_inv_cancel_left, hx]
      rw [e2, e3, hΩ.weyl w hw, hΩ.weyl w hw]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only
      rw [hΩ.unip u b hb, hzero z]
  have hK' : (KOff D p S : Set (G D p)) ⊆ A' :=
    hS₁ S (fun v hv => hS (by simp [hv])) A' hA'c rfl hgen
  intro u hu h
  let A : Set (G D p) := {h | Ω (h * u) = Ω h}
  have hAc : IsClosed A := by
    have e : A = ⋂ y, {h | Ω (h * u) y = Ω h y} := by
      ext x; simp only [A, Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
    rw [e]
    exact isClosed_iInter fun y => isClosed_eq
      (hΩ.cont.comp ((continuous_mul_const u).prodMk continuous_const))
      (hΩ.cont.comp (continuous_id.prodMk continuous_const))
  have h1 : (1 : G D p) ∈ A := by
    show Ω (1 * u) = Ω 1
    rw [one_mul]; exact hK' hu
  have hA := hG D p A hAc h1 fun g hgt x hx => by
    show Ω (g * x * u) = Ω (g * x)
    have hx' : Ω (x * u) = Ω x := hx
    rcases hgt with ⟨b, hb⟩ | ⟨a, ha⟩ | hw
    · funext y; rw [mul_assoc, hΩ.unip g b hb, hΩ.unip g b hb, hx']
    · funext y; rw [mul_assoc, hΩ.levi g a ha, hΩ.levi g a ha, hx']
    · funext y; rw [mul_assoc, hΩ.weyl g hw, hΩ.weyl g hw, hx']
  have hh : h ∈ A := hA ▸ Set.mem_univ h
  exact hh

end PositivityTheory.Rg.Rsw.L

end
end
