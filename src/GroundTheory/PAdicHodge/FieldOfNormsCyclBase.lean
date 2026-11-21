import Mathlib
import GroundTheory.PAdicHodge.FieldOfNormsAPF
import GroundTheory.PAdicHodge.FWCyclotomic
import GroundTheory.LocalFields.KroneckerWeber

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField

section Def

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] {L : IntermediateField K Ω}

variable (K Ω L) in

abbrev FinSub : Type _ := {E : IntermediateField K Ω // E ≤ L ∧ FiniteDimensional K E}

abbrev inclAlgebra {E E' : IntermediateField K Ω} (h : E ≤ E') : Algebra E E' :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

open Classical in

def relNorm {E E' : IntermediateField K Ω} (h : E ≤ E') (y : Ω) : Ω :=
  if hy : y ∈ E' then ((@Algebra.norm E E' _ _ (inclAlgebra h) ⟨y, hy⟩ : E) : Ω) else 0

variable (K Ω L) in

def FieldOfNorms : Type _ :=
  {x : FinSub K Ω L → Ω //
    (∀ E, x E ∈ E.1) ∧ ∀ E E' : FinSub K Ω L, ∀ h : E.1 ≤ E'.1, relNorm h (x E') = x E}

theorem relNorm_of_mem {E E' : IntermediateField K Ω} (h : E ≤ E') {y : Ω} (hy : y ∈ E') :
    relNorm h y = ((@Algebra.norm E E' _ _ (inclAlgebra h) ⟨y, hy⟩ : E) : Ω) := by
  rw [relNorm, dif_pos hy]

theorem relNorm_mem {E E' : IntermediateField K Ω} (h : E ≤ E') (y : Ω) : relNorm h y ∈ E := by
  unfold relNorm
  split_ifs
  · exact SetLike.coe_mem _
  · exact zero_mem _

theorem isScalarTower_inclAlgebra {E E' E'' : IntermediateField K Ω} (h : E ≤ E') (h' : E' ≤ E'') :
    @IsScalarTower E E' E'' (inclAlgebra h).toSMul (inclAlgebra h').toSMul
      (inclAlgebra (h.trans h')).toSMul := by
  letI := inclAlgebra h
  letI := inclAlgebra h'
  letI := inclAlgebra (h.trans h')
  exact IsScalarTower.of_algebraMap_eq fun x ↦ rfl

theorem isScalarTower_base_inclAlgebra {E E' : IntermediateField K Ω} (h : E ≤ E') :
    @IsScalarTower K E E' _ (inclAlgebra h).toSMul _ := by
  letI := inclAlgebra h
  exact IsScalarTower.of_algebraMap_eq fun x ↦ rfl

theorem relNorm_trans {E E' E'' : IntermediateField K Ω} (h : E ≤ E') (h' : E' ≤ E'') {y : Ω}
    (hy : y ∈ E'') : relNorm (h.trans h') y = relNorm h (relNorm h' y) := by
  letI := inclAlgebra h
  letI := inclAlgebra h'
  letI := inclAlgebra (h.trans h')
  haveI := isScalarTower_inclAlgebra h h'
  rw [relNorm_of_mem _ hy, relNorm_of_mem h' hy, relNorm_of_mem h (SetLike.coe_mem _)]
  congr 1
  rw [Subtype.coe_eta]
  exact Algebra.norm_norm.symm

theorem relNorm_self {E : IntermediateField K Ω} (h : E ≤ E) {y : Ω} (hy : y ∈ E) :
    relNorm h y = y := by
  rw [relNorm_of_mem _ hy]
  have hA : inclAlgebra h = Algebra.id E := Algebra.algebra_ext _ _ fun _ ↦ rfl
  have key : @Algebra.norm E E _ _ (inclAlgebra h) = @Algebra.norm E E _ _ (Algebra.id E) := by
    rw [hA]
  rw [key, Algebra.norm_self]
  rfl

theorem relNorm_mul {E E' : IntermediateField K Ω} (h : E ≤ E') {y z : Ω} (hy : y ∈ E')
    (hz : z ∈ E') : relNorm h (y * z) = relNorm h y * relNorm h z := by
  letI := inclAlgebra h
  rw [relNorm_of_mem h (mul_mem hy hz), relNorm_of_mem h hy, relNorm_of_mem h hz]
  rw [← IntermediateField.coe_mul, ← map_mul]
  rfl

end Def

section Tower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}

namespace NormTower

variable (t : NormTower K Ω p) (L : IntermediateField K Ω)

theorem E_mono {m n : ℕ} (h : m ≤ n) : t.E m ≤ t.E n := t.mono h

structure IsTowerFor : Prop where
  le : ∀ n, t.E n ≤ L
  exists_mem : ∀ x ∈ L, ∃ n, x ∈ t.E n
  relNorm_eq : ∀ n, ∀ y ∈ t.E (n + 1), relNorm (t.E_mono (Nat.le_succ n)) y = t.N n y

variable {t L}

def IsTowerFor.finSub (ht : t.IsTowerFor L) (n : ℕ) : FinSub K Ω L :=
  ⟨t.E n, ht.le n, t.finiteDimensional n⟩

@[simp] theorem IsTowerFor.finSub_val (ht : t.IsTowerFor L) (n : ℕ) : (ht.finSub n).1 = t.E n := rfl

theorem IsTowerFor.exists_le (ht : t.IsTowerFor L) (E : FinSub K Ω L) : ∃ n, E.1 ≤ t.E n := by
  haveI := E.2.2
  let b := Module.finBasis K E.1
  have : ∀ i, ∃ n, (b i : Ω) ∈ t.E n := fun i ↦ ht.exists_mem _ (E.2.1 (b i).2)
  choose N hN using this
  refine ⟨Finset.univ.sup N, fun x hx ↦ ?_⟩
  obtain ⟨z, rfl⟩ : ∃ z : E.1, (z : Ω) = x := ⟨⟨x, hx⟩, rfl⟩
  rw [← b.sum_repr z, IntermediateField.coe_sum]
  refine sum_mem fun i _ ↦ ?_
  rw [IntermediateField.coe_smul]
  exact (t.E _).smul_mem (t.E_mono (Finset.le_sup (Finset.mem_univ i)) (hN i))

theorem IsTowerFor.relNorm_eq_Nto (ht : t.IsTowerFor L) (n m : ℕ) {y : Ω} (hy : y ∈ t.E (n + m)) :
    relNorm (t.E_mono (Nat.le_add_right n m)) y = t.Nto n m y := by
  induction m generalizing y with
  | zero => exact relNorm_self _ hy
  | succ m ih =>
    have hle : t.E (n + m) ≤ t.E (n + m + 1) := t.E_mono (Nat.le_succ _)
    rw [show t.E_mono (Nat.le_add_right n (m + 1)) = (t.E_mono (Nat.le_add_right n m)).trans hle
      from rfl, relNorm_trans (t.E_mono (Nat.le_add_right n m)) hle hy, ht.relNorm_eq (n + m) y hy,
      ih (t.N_mem _ hy), Nto_succ]

def IsTowerFor.toFam (ht : t.IsTowerFor L) (x : FieldOfNorms K Ω L) : t.Fam :=
  ⟨fun n ↦ x.1 (ht.finSub n), fun n ↦
    ⟨x.2.1 (ht.finSub n), by
      rw [← ht.relNorm_eq n _ (x.2.1 (ht.finSub (n + 1)))]
      exact x.2.2 (ht.finSub n) (ht.finSub (n + 1)) (t.E_mono (Nat.le_succ n))⟩⟩

theorem IsTowerFor.toFam_val (ht : t.IsTowerFor L) (x : FieldOfNorms K Ω L) (n : ℕ) :
    (ht.toFam x).1 n = x.1 (ht.finSub n) := rfl

theorem IsTowerFor.relNorm_indep (ht : t.IsTowerFor L) (z : t.Fam) {E : IntermediateField K Ω}
    {m n : ℕ} (hm : E ≤ t.E m) (hn : E ≤ t.E n) :
    relNorm hm (z.1 m) = relNorm hn (z.1 n) := by
  wlog hmn : m ≤ n generalizing m n
  · exact (this hn hm (le_of_not_ge hmn)).symm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [show hn = hm.trans (t.E_mono (Nat.le_add_right m j)) from rfl,
    relNorm_trans hm (t.E_mono (Nat.le_add_right m j)) (z.2 (m + j)).1,
    ht.relNorm_eq_Nto m j (z.2 (m + j)).1, z.2.Nto_eq]

open Classical in

def IsTowerFor.ofFamFun (ht : t.IsTowerFor L) (z : t.Fam) (E : FinSub K Ω L) : Ω :=
  relNorm (Nat.find_spec (ht.exists_le E)) (z.1 (Nat.find (ht.exists_le E)))

theorem IsTowerFor.ofFamFun_eq (ht : t.IsTowerFor L) (z : t.Fam) (E : FinSub K Ω L) {n : ℕ}
    (hn : E.1 ≤ t.E n) : ht.ofFamFun z E = relNorm hn (z.1 n) := by
  classical
  exact ht.relNorm_indep z _ hn

def IsTowerFor.ofFam (ht : t.IsTowerFor L) (z : t.Fam) : FieldOfNorms K Ω L :=
  ⟨ht.ofFamFun z, fun E ↦ by
    obtain ⟨n, hn⟩ := ht.exists_le E
    rw [ht.ofFamFun_eq z E hn]; exact relNorm_mem _ _, fun E E' h ↦ by
    obtain ⟨n, hn⟩ := ht.exists_le E'
    rw [ht.ofFamFun_eq z E' hn, ht.ofFamFun_eq z E (h.trans hn), relNorm_trans h hn (z.2 n).1]⟩

theorem IsTowerFor.ofFam_val (ht : t.IsTowerFor L) (z : t.Fam) (E : FinSub K Ω L) {n : ℕ}
    (hn : E.1 ≤ t.E n) : (ht.ofFam z).1 E = relNorm hn (z.1 n) :=
  ht.ofFamFun_eq z E hn

variable (t L) in

def IsTowerFor.equiv (ht : t.IsTowerFor L) : FieldOfNorms K Ω L ≃ t.Fam where
  toFun := ht.toFam
  invFun := ht.ofFam
  left_inv x := by
    refine Subtype.ext (funext fun E ↦ ?_)
    obtain ⟨n, hn⟩ := ht.exists_le E
    rw [ht.ofFam_val _ E hn, ht.toFam_val]
    exact x.2.2 E (ht.finSub n) hn
  right_inv z := by
    refine Subtype.ext (funext fun n ↦ ?_)
    rw [ht.toFam_val, ht.ofFam_val z _ (t.E_mono (Nat.le_succ n))]
    exact (ht.relNorm_eq n _ (z.2 (n + 1)).1).trans (z.2 n).2

end NormTower

end Tower

section GaloisNorm

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem relNorm_eq_prod_of_isGalois {E E' : IntermediateField K Ω} (h : E ≤ E') [FiniteDimensional K E']
    [IsGalois K E'] (H : Subgroup Gal(E'/K)) [Fintype H]
    (hH : ∀ g, g ∈ H ↔ ∀ z : E', (z : Ω) ∈ E → (g z : Ω) = z) {y : Ω} (hy : y ∈ E') :
    relNorm h y = ∏ g : H, ((g : Gal(E'/K)) ⟨y, hy⟩ : Ω) := by
  letI := inclAlgebra h
  haveI := isScalarTower_base_inclAlgebra h
  haveI : IsGalois E E' := IsGalois.tower_top_of_isGalois K E E'
  haveI : FiniteDimensional E E' := Module.Finite.of_restrictScalars_finite K E E'
  have hcoe : ∀ e : E, ((algebraMap E E' e : E') : Ω) = e := fun e ↦ rfl
  rw [relNorm_of_mem _ hy, ← hcoe, Algebra.norm_eq_prod_automorphisms, IntermediateField.coe_prod]
  have hmem : ∀ τ : Gal(E'/E), τ.restrictScalars K ∈ H := fun τ ↦ (hH _).mpr fun z hz ↦ by
    obtain ⟨e, rfl⟩ : ∃ e : E, algebraMap E E' e = z := ⟨⟨z, hz⟩, Subtype.ext rfl⟩
    rw [AlgEquiv.restrictScalars_apply, τ.commutes]
  let φ : Gal(E'/E) → H := fun τ ↦ ⟨τ.restrictScalars K, hmem τ⟩
  refine Fintype.prod_bijective φ ⟨fun τ₁ τ₂ h ↦ ?_, fun g ↦ ?_⟩ _ _ fun τ ↦ rfl
  · refine AlgEquiv.ext fun z ↦ ?_
    have := congrArg (fun g : H ↦ ((g : Gal(E'/K)) z)) h
    exact this
  · have hg : ∀ e : E, (g : Gal(E'/K)) (algebraMap E E' e) = algebraMap E E' e := fun e ↦
      Subtype.ext ((hH g).mp g.2 (algebraMap E E' e) (by rw [hcoe]; exact e.2))
    refine ⟨AlgEquiv.ofRingEquiv (f := (g : Gal(E'/K)).toRingEquiv) hg, Subtype.ext ?_⟩
    exact AlgEquiv.ext fun z ↦ rfl

end GaloisNorm

section APF

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
  {L : IntermediateField K Ω} [IsGalois K L]

namespace APFData

variable (d : APFData L)

theorem mem_H_iff (n : ℕ) (g : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) :
    g ∈ d.H n ↔ ∀ z : (d.F (n + 1) : IntermediateField K Ω),
      (z : Ω) ∈ (d.F n : IntermediateField K Ω) → (g z : Ω) = z := by
  constructor
  · intro hg z hz
    have hg' : g ∈ (upperSupFixing K Ω L (d.u n)).map
        (AlgEquiv.restrictNormalHom (upperFieldFG d.apf (d.u (n + 1)) : IntermediateField K Ω)) := by
      rw [map_upperSupFixing d.apf]; exact hg
    obtain ⟨σ, hσ, rfl⟩ := hg'
    rw [← fixingSubgroup_upperField d.apf] at hσ
    exact (AlgEquiv.restrictNormalHom_apply _ σ z).trans
      ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ hz)
  · intro hg
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K)
      (K₁ := (d.F (n + 1) : IntermediateField K Ω)) Ω g
    refine d.restrict_mem_H n ?_
    rw [← fixingSubgroup_upperField d.apf, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨z, rfl⟩ : ∃ z : (d.F (n + 1) : IntermediateField K Ω), (z : Ω) = x :=
      ⟨⟨x, upperField_mono (d.u_mono (Nat.le_succ n)) hx⟩, rfl⟩
    rw [← AlgEquiv.restrictNormalHom_apply]
    exact hg z hx

theorem prod_T_eq (n : ℕ) {y : Ω} (hy : y ∈ (d.F (n + 1) : IntermediateField K Ω)) :
    (∏ σ ∈ d.T n, σ y) =
      ∏ g : d.H n, ((g : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) ⟨y, hy⟩ : Ω) := by
  classical
  rw [T, Finset.prod_image (fun g _ g' _ h ↦ d.lift_injective n h)]
  exact Finset.prod_congr rfl fun g _ ↦ d.lift_apply n g hy

theorem F_le (n : ℕ) : (d.F n : IntermediateField K Ω) ≤ d.F (n + 1) :=
  upperField_mono (d.u_mono (Nat.le_succ n))

theorem relNorm_eq_prod (n : ℕ) {y : Ω} (hy : y ∈ (d.F (n + 1) : IntermediateField K Ω)) :
    relNorm (d.F_le n) y = ∏ σ ∈ d.T n, σ y := by
  rw [d.prod_T_eq n hy]
  exact relNorm_eq_prod_of_isGalois (d.F_le n) (d.H n) (d.mem_H_iff n) hy

theorem isTowerFor (hinf : ¬ FiniteDimensional K L) : (d.tower hinf).IsTowerFor L where
  le n := upperField_le _
  exists_mem x hx := by
    obtain ⟨v, hv⟩ := exists_mem_upperField d.apf hx
    obtain ⟨m, hm⟩ := d.exists_le_u v
    exact ⟨m, upperField_mono hm hv⟩
  relNorm_eq n y hy := d.relNorm_eq_prod n hy

end APFData

end APF

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
  {L : IntermediateField K Ω} [IsGalois K L]
  [hsapf : Fact (IsStrictlyAPF K Ω L)] [hinf : Fact (¬ FiniteDimensional K L)]

namespace FieldOfNorms

variable (K Ω L) in

def apfData : APFData L := Classical.choice (IsStrictlyAPF.nonempty_apfData hsapf.out)

variable (K Ω L) in

def tower : NormTower K Ω (ringChar 𝓀[K]) := (apfData K Ω L).tower hinf.out

theorem isTowerFor : (tower K Ω L).IsTowerFor L := (apfData K Ω L).isTowerFor hinf.out

variable (K Ω L) in

def equivFam : FieldOfNorms K Ω L ≃ (tower K Ω L).Fam := isTowerFor.equiv _ _

instance instField : Field (FieldOfNorms K Ω L) := (equivFam K Ω L).field

theorem equivFam_mul (x y : FieldOfNorms K Ω L) :
    equivFam K Ω L (x * y) = equivFam K Ω L x * equivFam K Ω L y :=
  (equivFam K Ω L).apply_symm_apply _

theorem equivFam_add (x y : FieldOfNorms K Ω L) :
    equivFam K Ω L (x + y) = equivFam K Ω L x + equivFam K Ω L y :=
  (equivFam K Ω L).apply_symm_apply _

theorem equivFam_sub (x y : FieldOfNorms K Ω L) :
    equivFam K Ω L (x - y) = equivFam K Ω L x - equivFam K Ω L y :=
  (equivFam K Ω L).apply_symm_apply _

theorem equivFam_zero : equivFam K Ω L (0 : FieldOfNorms K Ω L) = 0 :=
  (equivFam K Ω L).apply_symm_apply _

theorem equivFam_one : equivFam K Ω L (1 : FieldOfNorms K Ω L) = 1 :=
  (equivFam K Ω L).apply_symm_apply _

theorem equivFam_natCast (n : ℕ) : equivFam K Ω L (n : FieldOfNorms K Ω L) = n :=
  (equivFam K Ω L).apply_symm_apply _

variable (K Ω L) in

def ringEquivFam : FieldOfNorms K Ω L ≃+* (tower K Ω L).Fam where
  __ := equivFam K Ω L
  map_mul' := equivFam_mul
  map_add' := equivFam_add

theorem equivFam_val (x : FieldOfNorms K Ω L) (n : ℕ) :
    (equivFam K Ω L x).1 n = x.1 (isTowerFor.finSub n) := rfl

theorem mul_val (x y : FieldOfNorms K Ω L) (E : FinSub K Ω L) : (x * y).1 E = x.1 E * y.1 E := by
  obtain ⟨n, hn⟩ := (isTowerFor (L := L)).exists_le E
  have hx : ∀ z : FieldOfNorms K Ω L, z.1 E = relNorm hn ((equivFam K Ω L z).1 n) := fun z ↦ by
    rw [equivFam_val]; exact (z.2.2 E _ hn).symm
  rw [hx, hx x, hx y, equivFam_mul, NormTower.Fam.mul_val]
  exact relNorm_mul hn ((equivFam K Ω L x).2 n).1 ((equivFam K Ω L y).2 n).1

instance charP : CharP (FieldOfNorms K Ω L) (ringChar 𝓀[K]) :=
  (CharP.charP_iff_prime_eq_zero (APFData.fact_prime (K := K)).out).mpr (by
    apply (equivFam K Ω L).injective
    rw [equivFam_natCast, equivFam_zero]
    exact NormTower.Fam.natCast_p)

def abv : AbsoluteValue (FieldOfNorms K Ω L) ℝ where
  toFun x := ‖equivFam K Ω L x‖
  map_mul' x y := by simp only [equivFam_mul, norm_mul]
  nonneg' x := norm_nonneg _
  eq_zero' x := by
    rw [norm_eq_zero, ← equivFam_zero, (equivFam K Ω L).injective.eq_iff]
  add_le' x y := by simp only [equivFam_add]; exact norm_add_le _ _

instance instNormedField : NormedField (FieldOfNorms K Ω L) := (abv (K := K) (Ω := Ω) (L := L)).toNormedField

theorem norm_def (x : FieldOfNorms K Ω L) : ‖x‖ = ‖equivFam K Ω L x‖ := rfl

variable (K Ω L) in

def isometryEquivFam : FieldOfNorms K Ω L ≃ᵢ (tower K Ω L).Fam where
  __ := equivFam K Ω L
  isometry_toFun := Isometry.of_dist_eq fun x y ↦ by
    rw [dist_eq_norm, dist_eq_norm, norm_def, equivFam_sub]
    rfl

instance instIsUltrametricDist : IsUltrametricDist (FieldOfNorms K Ω L) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simp only [norm_def, equivFam_add]
    exact IsUltrametricDist.norm_add_le_max _ _

instance instNontriviallyNormedField : NontriviallyNormedField (FieldOfNorms K Ω L) where
  non_trivial := by
    obtain ⟨z, hz⟩ := NontriviallyNormedField.non_trivial (α := (tower K Ω L).Fam)
    exact ⟨(equivFam K Ω L).symm z, by rw [norm_def, Equiv.apply_symm_apply]; exact hz⟩

instance instLocallyCompactSpace : LocallyCompactSpace (FieldOfNorms K Ω L) :=
  ((isometryEquivFam K Ω L).toHomeomorph.locallyCompactSpace_iff).mpr inferInstance

instance instValuativeRel : ValuativeRel (FieldOfNorms K Ω L) :=
  ValuativeRel.ofValuation (NormedField.valuation (K := FieldOfNorms K Ω L))

theorem vle_iff_norm_le (x y : FieldOfNorms K Ω L) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  exact NNReal.coe_le_coe

instance instCompatible : (NormedField.valuation (K := FieldOfNorms K Ω L)).Compatible :=
  Valuation.Compatible.ofValuation _

instance instIsValuativeTopology : IsValuativeTopology (FieldOfNorms K Ω L) := by
  let : Valued (FieldOfNorms K Ω L) NNReal := NormedField.toValued
  have : (Valued.v : Valuation (FieldOfNorms K Ω L) NNReal).Compatible := instCompatible
  exact GroundTheory.LocalField.isValuativeTopology_of_valued

instance instIsNontrivial : IsNontrivial (FieldOfNorms K Ω L) := by
  obtain ⟨z, hz⟩ := NontriviallyNormedField.non_trivial (α := FieldOfNorms K Ω L)
  refine ⟨⟨valuation _ z, ?_, ?_⟩⟩
  · rw [ne_eq, Valuation.zero_iff, ← norm_eq_zero]
    linarith
  · intro h
    have h2 : z ≤ᵥ (1 : FieldOfNorms K Ω L) := by
      rw [Valuation.vle_iff_le (valuation _), h, map_one]
    rw [vle_iff_norm_le, norm_one] at h2
    linarith

instance instIsNonarchimedeanLocalField : IsNonarchimedeanLocalField (FieldOfNorms K Ω L) where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

end FieldOfNorms

section Limit

variable {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  {Ω' : Type*} [Field Ω'] [ValuativeRel Ω'] [TopologicalSpace Ω'] [IsValuativeTopology Ω']
  [Algebra K' Ω'] [ValuativeExtension K' Ω'] [Algebra.IsAlgebraic K' Ω']

variable {p : ℕ} {t : NormTower K' Ω' p}

end Limit

namespace FieldOfNorms

end FieldOfNorms

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField IsLocalRing

section Tower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}

theorem exists_pow_sub_lt_one (F : IntermediateField K Ω) [FiniteDimensional K F] (hp : p.Prime)
    (hp1 : nrm K (p : Ω) < 1) {y : Ω} (hy : y ∈ F) (hy1 : nrm K y ≤ 1) (j : ℕ) :
    ∃ b ∈ F, nrm K b ≤ 1 ∧ nrm K (b ^ (p ^ j) - y) < 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hres : ∀ z : 𝒪[F], residue 𝒪[F] z = 0 ↔ nrm K ((z : F) : Ω) < 1 := by
    intro z
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    rw [← map_one (valuation F), ← not_le, ← not_le, valuation_le_iff_nrm_le]
    simp
  haveI : CharP 𝓀[F] p := by
    refine (CharP.charP_iff_prime_eq_zero hp).mpr ?_
    have := (hres (p : 𝒪[F])).mpr (by simpa using hp1)
    simpa using this
  haveI : Finite 𝓀[F] := inferInstance
  obtain ⟨z, rfl⟩ : ∃ z : F, (z : Ω) = y := ⟨⟨y, hy⟩, rfl⟩
  have hz : z ∈ 𝒪[F] := (mem_integer_iff_nrm_le_one F z).mpr hy1
  obtain ⟨β, hβ⟩ := ((surjective_frobenius 𝓀[F] p).iterate j) (residue 𝒪[F] ⟨z, hz⟩)
  obtain ⟨b, rfl⟩ := residue_surjective β
  refine ⟨((b : F) : Ω), (b : F).2, (mem_integer_iff_nrm_le_one F _).mp b.2, ?_⟩
  rw [iterate_frobenius, ← map_pow, ← sub_eq_zero, ← map_sub] at hβ
  have := (hres _).mp hβ
  simpa using this

namespace NormTower

variable (t : NormTower K Ω p)

theorem exists_nrm_sub_lt_one (n : ℕ) {z : Ω} (hz : z ∈ t.intSet (n + 1)) :
    ∃ w ∈ t.intSet n, nrm K (z - w) < 1 := by
  haveI := t.finiteDimensional n
  set d := p ^ t.k n
  obtain ⟨w, hw, hw1, hwN⟩ := exists_pow_sub_lt_one (t.E n) t.prime t.nrm_p_lt_one
    (t.N_mem n hz.1) (t.nrm_N_le_one n hz.2) (t.k n)
  refine ⟨w, ⟨hw, hw1⟩, ?_⟩

  have h1 : nrm K (z ^ d - w ^ d) < 1 := by
    have e : z ^ d - w ^ d = (z ^ d - t.N n z) + -(w ^ d - t.N n z) := by ring
    rw [e]
    refine lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [nrm_sub_comm]; exact (t.nrm_N_sub_pow_le n hz.1 hz.2).trans_lt t.c_lt_one
    · rw [nrm_neg]; exact hwN
  have h2 : nrm K ((z - w) ^ d - (z ^ d - w ^ d)) < 1 := by
    have hm1 : nrm K (-w) ≤ 1 := by rw [nrm_neg]; exact hw1
    have h3 := nrm_add_pow_prime_pow_sub_le t.prime hz.2 hm1 (t.k n)
    have e : (z - w) ^ d - (z ^ d - w ^ d) =
        ((z + -w) ^ d - z ^ d - (-w) ^ d) + ((-w) ^ d + w ^ d) := by
      rw [sub_eq_add_neg z w]; ring
    rw [e]
    refine lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt (h3.trans_lt t.nrm_p_lt_one) ?_)

    rcases t.prime.eq_two_or_odd' with hp2 | hodd
    · rcases Nat.eq_zero_or_pos (t.k n) with hk | hk
      · simp only [d, hk, pow_zero, pow_one, neg_add_cancel, nrm_zero]; exact one_pos
      · have hev : Even d := by
          simp only [d, hp2]
          exact (Nat.even_pow.mpr ⟨even_two, hk.ne'⟩)
        rw [hev.neg_pow, ← two_mul, nrm_mul]
        have h2' : nrm K (2 : Ω) < 1 := by
          have := t.nrm_p_lt_one; rw [hp2] at this; exact_mod_cast this
        calc nrm K (2 : Ω) * nrm K (w ^ d) ≤ nrm K (2 : Ω) * 1 :=
              mul_le_mul_of_nonneg_left (nrm_le_one_of_pow hw1 _) (nrm_nonneg _)
          _ < 1 := by rw [mul_one]; exact h2'
    · have hodd' : Odd d := hodd.pow
      rw [hodd'.neg_pow, neg_add_cancel, nrm_zero]; exact one_pos
  have h4 : nrm K ((z - w) ^ d) < 1 := by
    have e : (z - w) ^ d = ((z - w) ^ d - (z ^ d - w ^ d)) + (z ^ d - w ^ d) := by ring
    rw [e]
    exact lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt h2 h1)
  rw [nrm_pow] at h4
  exact (pow_lt_one_iff_of_nonneg (nrm_nonneg _) (pow_pos t.prime.pos _).ne').mp h4

theorem exists_nrm_sub_lt_one_zero (n : ℕ) {z : Ω} (hz : z ∈ t.intSet n) :
    ∃ w ∈ t.intSet 0, nrm K (z - w) < 1 := by
  induction n generalizing z with
  | zero => exact ⟨z, hz, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw, hzw⟩ := t.exists_nrm_sub_lt_one n hz
    obtain ⟨w', hw', hww'⟩ := ih hw
    refine ⟨w', hw', ?_⟩
    have e : z - w' = (z - w) + (w - w') := by ring
    rw [e]
    exact lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt hzw hww')

theorem nrm_le_value_of_lt_one (n : ℕ) {y : Ω} (hy : y ∈ t.E n) (h : nrm K y < 1) :
    nrm K y ≤ t.value n := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [nrm_zero]; exact (t.value_pos n).le
  obtain ⟨j, hj⟩ := t.value_zpow n y hy hy0
  rw [hj] at h ⊢
  have hj1 : 1 ≤ j := by
    by_contra hcon
    push Not at hcon
    have : 1 ≤ t.value n ^ j :=
      one_le_zpow_of_nonpos₀ (t.value_pos n) (t.value_lt_one n).le (by omega)
    linarith
  calc t.value n ^ j ≤ t.value n ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ (t.value_pos n) (t.value_lt_one n).le hj1
    _ = t.value n := zpow_one _

theorem exists_plus_nrm_sub_lt_one {y : Ω} (hy : y ∈ t.intSet 0) :
    ∃ x : t.Plus, nrm K (x.1 0 - y) < 1 := by

  let C : ℕ → Set Ω := fun n ↦ {z | nrm K (z ^ t.D 0 n - y) ≤ t.value n}
  have hcl : ∀ n, IsClosed (C n) := fun n ↦
    isClosed_le ((continuous_nrm K Ω).comp ((continuous_pow _).sub continuous_const))
      continuous_const
  have hne : ∀ n, (t.intSet n ∩ C n).Nonempty := by
    intro n
    haveI := t.finiteDimensional 0
    have hD : ∃ j, t.D 0 n = p ^ j := ⟨∑ m ∈ Finset.range n, t.k (0 + m), by
      rw [D, Finset.prod_pow_eq_pow_sum]⟩
    obtain ⟨j, hj⟩ := hD
    obtain ⟨b, hb, hb1, hby⟩ := exists_pow_sub_lt_one (t.E 0) t.prime t.nrm_p_lt_one hy.1 hy.2 j
    refine ⟨b, ⟨t.E_mono (Nat.zero_le n) hb, hb1⟩, ?_⟩
    show nrm K (b ^ t.D 0 n - y) ≤ t.value n
    rw [hj]
    have hmem : b ^ p ^ j - y ∈ t.E n :=
      sub_mem (pow_mem (t.E_mono (Nat.zero_le n) hb) _) (t.E_mono (Nat.zero_le n) hy.1)
    exact t.nrm_le_value_of_lt_one n hmem hby
  have hN : ∀ n, ∀ z ∈ t.intSet (n + 1) ∩ C (n + 1), t.N n z ∈ C n := by
    intro n z hz
    obtain ⟨⟨hzE, hz1⟩, hzy⟩ := hz
    change nrm K (z ^ t.D 0 (n + 1) - y) ≤ t.value (n + 1) at hzy
    show nrm K (t.N n z ^ t.D 0 n - y) ≤ t.value n
    have hD : t.D 0 (n + 1) = t.D 0 n * p ^ t.k n := by rw [D_succ, zero_add]
    have h1 : nrm K (t.N n z ^ t.D 0 n - z ^ t.D 0 (n + 1)) ≤ t.c := by
      rw [hD, pow_mul']
      exact (nrm_pow_sub_pow_le (t.nrm_N_le_one n hz1) (nrm_le_one_of_pow hz1 _) _).trans
        (t.nrm_N_sub_pow_le n hzE hz1)
    have h2 : nrm K (t.N n z ^ t.D 0 n - y) < 1 := by
      have e : t.N n z ^ t.D 0 n - y =
          (t.N n z ^ t.D 0 n - z ^ t.D 0 (n + 1)) + (z ^ t.D 0 (n + 1) - y) := by ring
      rw [e]
      exact lt_of_le_of_lt (nrm_add_le_max _ _)
        (max_lt (h1.trans_lt t.c_lt_one) (hzy.trans_lt (t.value_lt_one _)))
    exact t.nrm_le_value_of_lt_one n
      (sub_mem (pow_mem (t.N_mem n hzE) _) (t.E_mono (Nat.zero_le n) hy.1)) h2
  obtain ⟨z, hz, hzC⟩ := t.exists_intFam_mem hcl hne hN
  refine ⟨⟨z, hz⟩, ?_⟩
  have := hzC 0
  change nrm K (z 0 ^ t.D 0 0 - y) ≤ t.value 0 at this
  have hD : t.D 0 0 = 1 := by simp [D]
  rw [hD, pow_one] at this
  exact this.trans_lt (t.value_lt_one 0)

end NormTower

end Tower

section FieldOfNorms

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
  {L : IntermediateField K Ω} [IsGalois K L]
  [hsapf : Fact (IsStrictlyAPF K Ω L)] [hinf : Fact (¬ FiniteDimensional K L)]

namespace FieldOfNorms

instance isLocalRing_integer_L : IsLocalRing 𝒪[L] :=
  inferInstanceAs (IsLocalRing (valuation L).valuationSubring)

theorem mem_integer_L_iff (z : L) : z ∈ 𝒪[L] ↔ nrm K (z : Ω) ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation L), ← (valuation L).vle_iff_le,
    ← IntermediateField.coe_vle_coe_iff, ← nrm_le_nrm_iff (K := K)]
  simp

theorem mem_maximalIdeal_L_iff (z : 𝒪[L]) : z ∈ maximalIdeal 𝒪[L] ↔ nrm K ((z : L) : Ω) < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
    ← map_one (valuation L), ← not_le, ← not_le, ← (valuation L).vle_iff_le,
    ← IntermediateField.coe_vle_coe_iff, ← nrm_le_nrm_iff (K := K)]
  simp

theorem mem_integer_iff (x : FieldOfNorms K Ω L) : x ∈ 𝒪[FieldOfNorms K Ω L] ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation _), ← (valuation _).vle_iff_le,
    vle_iff_norm_le, norm_one]

theorem mem_maximalIdeal_iff (x : 𝒪[FieldOfNorms K Ω L]) :
    x ∈ maximalIdeal 𝒪[FieldOfNorms K Ω L] ↔ ‖(x : FieldOfNorms K Ω L)‖ < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
    ← map_one (valuation _), ← not_le, ← not_le, ← (valuation _).vle_iff_le, vle_iff_norm_le,
    norm_one]

abbrev E₀ : FinSub K Ω L := (isTowerFor (L := L)).finSub 0

def toL (x : FieldOfNorms K Ω L) : L := ⟨x.1 E₀, E₀.2.1 (x.2.1 E₀)⟩

theorem nrm_toL (x : FieldOfNorms K Ω L) : nrm K ((toL x : L) : Ω) = ‖x‖ := rfl

theorem toL_mem (x : 𝒪[FieldOfNorms K Ω L]) : toL (x : FieldOfNorms K Ω L) ∈ 𝒪[L] := by
  rw [mem_integer_L_iff, nrm_toL, ← mem_integer_iff]; exact x.2

def toPlus (x : 𝒪[FieldOfNorms K Ω L]) : (tower K Ω L).Plus :=
  ⟨(equivFam K Ω L x).1, NormTower.Fam.isIntFam_of_nrm_le (by
    have := (mem_integer_iff _).mp x.2
    rw [norm_def, NormTower.Fam.norm_def] at this
    exact this)⟩

theorem equivFam_eq_toPlus (x : 𝒪[FieldOfNorms K Ω L]) :
    equivFam K Ω L (x : FieldOfNorms K Ω L) = (toPlus x).toFam := rfl

theorem add_val_cong (x y : 𝒪[FieldOfNorms K Ω L]) :
    nrm K (((x : FieldOfNorms K Ω L) + y).1 E₀ - (x.1.1 E₀ + y.1.1 E₀)) < 1 := by
  have h : equivFam K Ω L ((x : FieldOfNorms K Ω L) + y) = (toPlus x + toPlus y).toFam := by
    rw [equivFam_add, equivFam_eq_toPlus, equivFam_eq_toPlus, NormTower.Fam.toFam_add]
  have h2 := NormTower.Plus.add_cong (toPlus x) (toPlus y) 0
  have e : ((x : FieldOfNorms K Ω L) + y).1 E₀ = (toPlus x + toPlus y).1 0 := by
    rw [← equivFam_val, h]; rfl
  rw [e]
  exact h2.trans_lt (tower K Ω L).ρ_lt_one

def reduction : 𝒪[FieldOfNorms K Ω L] →+* 𝓀[L] where
  toFun x := residue 𝒪[L] ⟨toL (x : FieldOfNorms K Ω L), toL_mem x⟩
  map_one' := by
    rw [← map_one (residue 𝒪[L])]
    congr 1
    refine Subtype.ext (Subtype.ext ?_)
    show (1 : FieldOfNorms K Ω L).1 E₀ = 1
    rw [← equivFam_val, equivFam_one, NormTower.Fam.one_val]
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    refine Subtype.ext (Subtype.ext ?_)
    show ((x : FieldOfNorms K Ω L) * y).1 E₀ = x.1.1 E₀ * y.1.1 E₀
    exact mul_val _ _ _
  map_zero' := by
    rw [← map_zero (residue 𝒪[L])]
    congr 1
    refine Subtype.ext (Subtype.ext ?_)
    show (0 : FieldOfNorms K Ω L).1 E₀ = 0
    rw [← equivFam_val, equivFam_zero, NormTower.Fam.zero_val]
  map_add' x y := by
    rw [← map_add, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal_L_iff]
    exact add_val_cong x y

theorem reduction_eq_zero_iff (x : 𝒪[FieldOfNorms K Ω L]) :
    reduction (K := K) (Ω := Ω) (L := L) x = 0 ↔ x ∈ maximalIdeal 𝒪[FieldOfNorms K Ω L] := by
  show residue 𝒪[L] ⟨toL (x : FieldOfNorms K Ω L), toL_mem x⟩ = 0 ↔ _
  rw [residue_eq_zero_iff, mem_maximalIdeal_L_iff, mem_maximalIdeal_iff]
  rfl

theorem reduction_surjective : Function.Surjective (reduction (K := K) (Ω := Ω) (L := L)) := by
  intro r
  obtain ⟨⟨z, hz⟩, rfl⟩ := residue_surjective r
  have hz1 := (mem_integer_L_iff z).mp hz
  obtain ⟨n, hn⟩ := (isTowerFor (L := L)).exists_mem (z : Ω) z.2
  obtain ⟨w, hw, hzw⟩ := (tower K Ω L).exists_nrm_sub_lt_one_zero n ⟨hn, hz1⟩
  obtain ⟨a, ha⟩ := (tower K Ω L).exists_plus_nrm_sub_lt_one hw
  let x : FieldOfNorms K Ω L := (equivFam K Ω L).symm a.toFam
  have hx : equivFam K Ω L x = a.toFam := (equivFam K Ω L).apply_symm_apply _
  have hxval : x.1 E₀ = a.1 0 := by
    rw [← equivFam_val, hx]; rfl
  have hxint : x ∈ 𝒪[FieldOfNorms K Ω L] := by
    rw [mem_integer_iff, norm_def, hx, NormTower.Fam.norm_def]; exact a.nrm_le 0
  refine ⟨⟨x, hxint⟩, ?_⟩
  show residue 𝒪[L] _ = residue 𝒪[L] _
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal_L_iff]
  show nrm K (x.1 E₀ - (z : Ω)) < 1
  rw [hxval]
  have e : a.1 0 - (z : Ω) = (a.1 0 - w) - ((z : Ω) - w) := by ring
  rw [e]
  exact lt_of_le_of_lt (nrm_sub_le_max _ _) (max_lt ha hzw)

theorem ker_reduction : RingHom.ker (reduction (K := K) (Ω := Ω) (L := L)) =
    maximalIdeal 𝒪[FieldOfNorms K Ω L] := by
  ext x; rw [RingHom.mem_ker, reduction_eq_zero_iff]

def residueFieldEquiv : 𝓀[FieldOfNorms K Ω L] ≃+* 𝓀[L] :=
  (Ideal.quotEquivOfEq ker_reduction.symm).trans
    (RingHom.quotientKerEquivOfSurjective reduction_surjective)

end FieldOfNorms

end FieldOfNorms

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace CyclNorms

open GroundTheory.LocalField ValuativeRel

variable (p : ℕ) [Fact p.Prime]

scoped instance padicAlgCl_valuativeRel : ValuativeRel (PadicAlgCl p) :=
  ValuativeRel.ofValuation (NormedField.valuation (K := PadicAlgCl p))

variable {p}

theorem vle_iff_norm_le (x y : PadicAlgCl p) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  exact NNReal.coe_le_coe

scoped instance padicAlgCl_compatible : (NormedField.valuation (K := PadicAlgCl p)).Compatible :=
  Valuation.Compatible.ofValuation _

scoped instance padicAlgCl_isValuativeTopology : IsValuativeTopology (PadicAlgCl p) := by
  let : Valued (PadicAlgCl p) NNReal := NormedField.toValued
  have : (Valued.v : Valuation (PadicAlgCl p) NNReal).Compatible := padicAlgCl_compatible
  exact GroundTheory.LocalField.isValuativeTopology_of_valued

scoped instance padicAlgCl_valuativeExtension : ValuativeExtension ℚ_[p] (PadicAlgCl p) := by
  refine ⟨fun a b ↦ ?_⟩
  rw [vle_iff_norm_le, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le]

end CyclNorms

end GroundTheory.PAdicHodge
end
end
