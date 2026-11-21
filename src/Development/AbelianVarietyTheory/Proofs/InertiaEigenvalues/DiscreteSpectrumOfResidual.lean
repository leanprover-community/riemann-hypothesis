import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdealStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorForms

section
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.UnipKill

open Matrix

section General

variable {R S : Type} [CommRing R] [CommRing S] {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {N : ℕ}

theorem cornerGL_mem_unipRad (s : R →ₙ+* S) (e : (Σ a, m a) ≃ Fin N) {g : GL (Fin N) R}
    (hg : g ∈ unipRad R e) : cornerGL N s g ∈ unipRad S e := by
  rw [mem_unipRad] at hg ⊢
  have hval : ∀ i j, ((cornerGL N s g : GL (Fin N) S) : Matrix (Fin N) (Fin N) S) i j =
      (1 : Matrix (Fin N) (Fin N) S) i j - s ((1 : Matrix (Fin N) (Fin N) R) i j) +
        s ((g : Matrix (Fin N) (Fin N) R) i j) := fun i j => rfl
  refine ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    rw [hval, mem_parab.1 hg.1 i j hij]
    simp [Matrix.one_apply_ne hne]
  · rw [hval, hg.2 a i j]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : e ⟨a, i⟩ ≠ e ⟨a, j⟩ := fun h => hij (by simpa using e.injective h)
      simp [Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]

omit [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

def tv {p q : Fin N} (hpq : p ≠ q) (c : R) : GL (Fin N) R :=
  ⟨transvection p q c, transvection p q (-c),
    (transvection_mul_transvection_same p q hpq c (-c)).trans (by rw [add_neg_cancel, transvection_zero]),
    (transvection_mul_transvection_same p q hpq (-c) c).trans (by rw [neg_add_cancel, transvection_zero])⟩

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem ne_of_blk_lt (e : (Σ a, m a) ≃ Fin N) {p q : Fin N} (hpq : blk e p < blk e q) : p ≠ q := by
  rintro rfl; exact lt_irrefl _ hpq

theorem tv_mem_unipRad (e : (Σ a, m a) ≃ Fin N) {p q : Fin N} (hpq : blk e p < blk e q) (c : R) :
    tv (ne_of_blk_lt e hpq) c ∈ unipRad R e := by
  rw [mem_unipRad]
  refine ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    change (transvection p q c) i j = 0
    rw [transvection, Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.single_apply]
    rw [if_neg, zero_add]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hpq hij
  · change (transvection p q c) (e ⟨a, i⟩) (e ⟨a, j⟩) = _
    rw [transvection, Matrix.add_apply, Matrix.single_apply, if_neg, add_zero]
    · by_cases hij : i = j
      · subst hij; simp
      · have hne : e ⟨a, i⟩ ≠ e ⟨a, j⟩ := fun h => hij (by simpa using e.injective h)
        rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]
    · rintro ⟨h1, h2⟩
      have h1' : blk e p = a := by rw [h1]; simp
      have h2' : blk e q = a := by rw [h2]; simp
      rw [h1', h2'] at hpq
      exact lt_irrefl _ hpq

end General

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

theorem toL_tv {p q : Fin N} (hpq : p ≠ q) (x : Cinf E) (t : ℝ) :
    toL ((tv hpq (t • x) : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) =
      oneL E N + t • toL (Matrix.single p q x) := by
  funext i j
  change (transvection p q (t • x)) i j = (1 : Matrix (Fin N) (Fin N) (Cinf E)) i j + t • (Matrix.single p q x) i j
  rw [transvection, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem lieD_single_leviEmb {c : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N) (ψ : Sm E N)
    (hψ : ∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g) {p q : Fin N}
    (hpq : blk (stdBlocks n h) p < blk (stdBlocks n h) q) (x : Cinf E) (m : Levi (Ad E) fun i => Fin (n i)) :
    lieD (toL (Matrix.single p q x)) ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 := by
  set e := stdBlocks n h
  set g := leviEmb (Ad E) e m
  have hne := ne_of_blk_lt e hpq
  let u : ℝ → GL (Fin N) (Cinf E) := fun t => tv hne (t • x)
  have hu0 : u 0 = 1 := Units.ext (by
    show transvection p q ((0 : ℝ) • x) = 1
    rw [zero_smul, transvection_zero])
  have hline : HasDerivAt (fun t => toL (u t).val) (toL (Matrix.single p q x)) 0 := by
    have : (fun t => toL (u t).val) = fun t : ℝ => oneL E N + t • toL (Matrix.single p q x) :=
      funext fun t => toL_tv hne x t
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL (Matrix.single p q x))).const_add (oneL E N)
  have hc := hasDerivAt_curve ψ g u (toL (Matrix.single p q x)) hu0 hline
  have hconst : (fun t => ψ.1 (g * infGL E N (u t))) = fun _ => ψ.1 g := by
    funext t
    have hv : infGL E N (u t) ∈ unipRad (Ad E) e := cornerGL_mem_unipRad (sInf E) e (tv_mem_unipRad e hpq _)
    have hw : g * infGL E N (u t) * g⁻¹ ∈ unipRad (Ad E) e :=
      (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer (Ad E) e m) _).1 hv
    rw [← hψ _ hw g, inv_mul_cancel_right]
  rw [hconst] at hc
  exact hc.unique (hasDerivAt_const 0 _)

end Adelic

open Complex in

theorem eop_leviEmb_eq_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (ψ : Sm E N) (hψ : ∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g)
    (τ : E →+* ℂ) (p q : Fin N) (hpq : blk (stdBlocks n h) p < blk (stdBlocks n h) q) (m) :
    (Eop τ p q ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 := by
  have key := fun x => lieD_single_leviEmb h ψ hψ hpq x m
  change ((1 / 2 : ℂ) • (lieS E N p q (atEmb τ 1) - Complex.I • lieS E N p q (atEmb τ Complex.I)) ψ).1 _ = 0
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, lieS_apply, CuspRep.lie_apply, key, smul_zero, sub_zero]

end GlobalTheory.UnipKill
end
end

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperMatrixUnit_kills_unipotentInvariant_on_levi : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (ψ : Sm E N), (∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g) → ∀ (τ : E →+* ℂ) (p q : Fin N), blk (stdBlocks n h) p < blk (stdBlocks n h) q → ∀ m, (Eop τ p q ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 := by
  atlas_forward_decl GlobalTheory.UnipKill.eop_leviEmb_eq_zero
end

section
open NumberField IsDedekindDomain Formalism.L2.Host
open scoped ContDiff Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.BlockCap

open Matrix

theorem qdet_intertwine {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {k : ℕ}
    (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q, R ∘ₗ X p q = Y p q ∘ₗ R) (v : ℂ) :
    R ∘ₗ Formalism.REAL.qdet X v = Formalism.REAL.qdet Y v ∘ₗ R := by
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') :=
    { carrier := {z | R ∘ₗ z.1 = z.2 ∘ₗ R}
      mul_mem' := fun {x y} hx hy => by
        change R ∘ₗ (x.1 ∘ₗ y.1) = (x.2 ∘ₗ y.2) ∘ₗ R
        rw [← LinearMap.comp_assoc, hx, LinearMap.comp_assoc, hy, LinearMap.comp_assoc]
      add_mem' := fun {x y} hx hy => by
        change R ∘ₗ (x.1 + y.1) = (x.2 + y.2) ∘ₗ R
        rw [LinearMap.comp_add, LinearMap.add_comp, hx, hy]
      algebraMap_mem' := fun c => by
        change R ∘ₗ (algebraMap ℂ (Module.End ℂ M) c) = (algebraMap ℂ (Module.End ℂ M') c) ∘ₗ R
        ext φ; simp }
  let Z : Fin k → Fin k → S := fun p q => ⟨(X p q, Y p q), h p q⟩
  have h1 := map_qdet ((AlgHom.fst ℂ _ _).comp S.val) Z v
  have h2 := map_qdet ((AlgHom.snd ℂ _ _).comp S.val) Z v
  have hm : R ∘ₗ ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').1 =
      ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').2 ∘ₗ R := (Formalism.REAL.qdet Z v).2
  have e1 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').1 = Formalism.REAL.qdet X v := h1
  have e2 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').2 = Formalism.REAL.qdet Y v := h2
  rw [e1, e2] at hm
  exact hm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem tensorForms_update {c : ℕ} {n : Fin c → ℕ} (π : ∀ i, CuspSub E (n i)) (i : Fin c)
    (m : ∀ j, GA E (n j)) {F : (∀ j, GA E (n j)) → ℂ} (hF : F ∈ tensorForms π) :
    ∃ θ ∈ (π i).V, ∀ y, F (Function.update m i y) = θ.1 y := by
  classical
  let L : ((∀ j, GA E (n j)) → ℂ) →ₗ[ℂ] (GA E (n i) → ℂ) :=
    { toFun := fun F y => F (Function.update m i y), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hle : tensorForms π ≤ ((π i).V.map (Sm E (n i)).subtype).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, rfl⟩
    refine ⟨(∏ j ∈ Finset.univ.erase i, (φ j).1.1 (m j)) • (φ i).1, (π i).V.smul_mem _ (φ i).2, ?_⟩
    funext y
    change (∏ j ∈ Finset.univ.erase i, (φ j).1.1 (m j)) * (φ i).1.1 y =
      ∏ j, (φ j).1.1 (Function.update m i y j)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  obtain ⟨θ, hθ, e⟩ := hle hF
  exact ⟨θ, hθ, fun y => (congrFun e y).symm⟩

theorem map_leviEmb {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) {c N : ℕ} {n : Fin c → ℕ}
    (e : (Σ j, Fin (n j)) ≃ Fin N) (g : Levi R fun j => Fin (n j)) :
    GeneralLinearGroup.map p (leviEmb R e g) = leviEmb S e fun j => GeneralLinearGroup.map p (g j) := by
  ext a b
  obtain ⟨⟨j, x⟩, rfl⟩ := e.surjective a
  obtain ⟨⟨k, y⟩, rfl⟩ := e.surjective b
  by_cases hjk : j = k
  · subst hjk
    simp [leviEmb_apply_same]
  · simp [leviEmb_apply_ne _ e _ hjk]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} {n : Fin c → ℕ}

theorem leviEmb_update_infGL (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (y : GL (Fin (n i)) (Cinf E)) :
    leviEmb (Ad E) e (Function.update 1 i (infGL E (n i) y)) =
      infGL E N (leviEmb (Cinf E) e (Function.update 1 i y)) := by
  classical
  refine ga_ext ?_ ?_
  · rw [pInf_infGL, map_leviEmb]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  · rw [pFin_infGL, map_leviEmb]
    have : (fun j => GeneralLinearGroup.map (pFin E) (Function.update (1 : Levi (Ad E) fun j => Fin (n j)) i
        (infGL E (n i) y) j)) = 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [this, map_one]

theorem update_mul (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c) (g z : GA E (n i)) :
    Function.update m i (g * z) = Function.update m i g * Function.update (1 : Levi (Ad E) fun j => Fin (n j)) i z := by
  classical
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

def iota (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (x : Lie E (n i)) : Lie E N :=
  toL (reindex e e (blockDiagonal' (Function.update (fun j => (1 : Matrix (Fin (n j)) (Fin (n j)) (Cinf E))) i
    (Matrix.of x))))

theorem iota_val (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (y : GL (Fin (n i)) (Cinf E)) :
    iota e i (toL y.val) = toL (leviEmb (Cinf E) e (Function.update 1 i y)).val := by
  classical
  have h : (fun j => ((Function.update (1 : Levi (Cinf E) fun j => Fin (n j)) i y j : GL _ _) :
      Matrix (Fin (n j)) (Fin (n j)) (Cinf E))) =
      Function.update (fun j => (1 : Matrix (Fin (n j)) (Fin (n j)) (Cinf E))) i y.val := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp only [iota, leviEmb, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h]
  congr
  exact Subsingleton.elim _ _

def blockLin (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) : Lie E (n i) →ₗ[ℝ] Lie E N where
  toFun x := toL (reindex e e (blockDiagonal' (Pi.single (M := fun j => Matrix (Fin (n j)) (Fin (n j)) (Cinf E)) i
    (Matrix.of x))))
  map_add' x y := by
    rw [← Matrix.of_add_of, Pi.single_add, blockDiagonal'_add]
    rfl
  map_smul' r x := by
    ext a b
    obtain ⟨⟨j, p⟩, rfl⟩ := e.surjective a
    obtain ⟨⟨k, q⟩, rfl⟩ := e.surjective b
    by_cases hjk : j = k
    · subst hjk
      by_cases hj : j = i
      · subst hj
        simp [blockDiagonal'_apply_eq]
      · simp [blockDiagonal'_apply_eq, Pi.single_eq_of_ne hj]
    · simp [blockDiagonal'_apply_ne _ _ _ hjk]

def blockCLM (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) : Lie E (n i) →L[ℝ] Lie E N :=
  LinearMap.toContinuousLinearMap (blockLin e i)

theorem blockCLM_apply (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (x : Lie E (n i)) :
    blockCLM e i x = blockLin e i x := rfl

theorem iota_eq (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (x : Lie E (n i)) :
    iota e i x = iota e i 0 + blockCLM e i x := by
  classical
  have h : Function.update (fun j => (1 : Matrix (Fin (n j)) (Fin (n j)) (Cinf E))) i (Matrix.of x) =
      Function.update (fun j => (1 : Matrix (Fin (n j)) (Fin (n j)) (Cinf E))) i (Matrix.of 0) +
        Pi.single (M := fun j => Matrix (Fin (n j)) (Fin (n j)) (Cinf E)) i (Matrix.of x) := by
    funext j
    by_cases hj : j = i
    · subst hj; ext; simp
    · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]
  simp only [iota, blockCLM_apply, blockLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h, blockDiagonal'_add]
  rfl

theorem contDiff_iota (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) : ContDiff ℝ ∞ (iota (E := E) e i) := by
  have : iota (E := E) e i = fun x => iota e i 0 + blockCLM e i x := funext (iota_eq e i)
  rw [this]
  have h2 : ContDiff ℝ ∞ (blockCLM (E := E) e i) := (blockCLM (E := E) e i).contDiff
  exact contDiff_const.add h2

theorem hasFDerivAt_iota (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (x : Lie E (n i)) :
    HasFDerivAt (iota (E := E) e i) (blockCLM e i) x := by
  have : iota (E := E) e i = fun x => iota e i 0 + blockCLM e i x := funext (iota_eq e i)
  rw [this]
  exact (blockCLM e i).hasFDerivAt.const_add _

theorem iota_one (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) : iota (E := E) e i (oneL E (n i)) = oneL E N := by
  have h := iota_val (E := E) e i 1
  rw [show Function.update (1 : Levi (Cinf E) fun j => Fin (n j)) i 1 = 1 from Function.update_eq_self i 1,
    map_one] at h
  exact h

theorem iota_mem_invSet (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) {x : Lie E (n i)} (hx : x ∈ invSet E (n i)) :
    iota e i x ∈ invSet E N := by
  obtain ⟨u, hu⟩ := hx
  have e1 : x = toL u.val := hu.symm
  rw [e1, iota_val]
  exact val_mem_invSet _

theorem blockLin_single (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (p q : Fin (n i)) (x : Cinf E) :
    blockLin e i (toL (Matrix.single p q x)) = toL (Matrix.single (e ⟨i, p⟩) (e ⟨i, q⟩) x) := by
  funext a b
  obtain ⟨⟨j, p'⟩, rfl⟩ := e.surjective a
  obtain ⟨⟨k, q'⟩, rfl⟩ := e.surjective b
  by_cases hjk : j = k
  · subst hjk
    by_cases hj : j = i
    · subst hj
      simp only [blockLin, LinearMap.coe_mk, AddHom.coe_mk]
      change (blockDiagonal' _).submatrix e.symm e.symm (e ⟨j, p'⟩) (e ⟨j, q'⟩) =
        Matrix.single (e ⟨j, p⟩) (e ⟨j, q⟩) x (e ⟨j, p'⟩) (e ⟨j, q'⟩)
      rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, blockDiagonal'_apply_eq,
        Pi.single_eq_same, Matrix.single_apply, Matrix.of_apply]
      change Matrix.single p q x p' q' = _
      rw [Matrix.single_apply]
      simp
    · simp [blockLin, blockDiagonal'_apply_eq, Pi.single_eq_of_ne hj, Matrix.single_apply, Ne.symm hj]
  · simp only [blockLin, LinearMap.coe_mk, AddHom.coe_mk]
    change (blockDiagonal' _).submatrix e.symm e.symm (e ⟨j, p'⟩) (e ⟨k, q'⟩) =
      Matrix.single (e ⟨i, p⟩) (e ⟨i, q⟩) x (e ⟨j, p'⟩) (e ⟨k, q'⟩)
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, blockDiagonal'_apply_ne _ _ _ hjk,
      Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    exact hjk ((congrArg Sigma.fst (e.injective h1)).symm.trans (congrArg Sigma.fst (e.injective h2)))

def restr (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c) (φ : GA E N → ℂ) :
    GA E (n i) → ℂ := fun y => φ (leviEmb (Ad E) e (Function.update m i y))

theorem chart_restr (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c)
    (φ : GA E N → ℂ) (g : GA E (n i)) {x : Lie E (n i)} (hx : x ∈ invSet E (n i)) :
    chart (restr e m i φ) g x = chart φ (leviEmb (Ad E) e (Function.update m i g)) (iota e i x) := by
  obtain ⟨u, hu⟩ := hx
  have e1 : x = toL u.val := hu.symm
  subst e1
  rw [chart_val, iota_val, chart_val, restr, update_mul, map_mul, leviEmb_update_infGL]

theorem restr_mem_Sm (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c)
    {φ : GA E N → ℂ} (hφ : φ ∈ Sm E N) : restr e m i φ ∈ Sm E (n i) := fun g =>
  ((hφ _).comp (contDiff_iota e i).contDiffOn fun _ hx => iota_mem_invSet e i hx).congr
    fun _ hx => chart_restr e m i φ g hx

theorem lieD_restr (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c)
    {φ : GA E N → ℂ} (hφ : φ ∈ Sm E N) (X : Lie E (n i)) (y : GA E (n i)) :
    lieD X (restr e m i φ) y = lieD (blockCLM e i X) φ (leviEmb (Ad E) e (Function.update m i y)) := by
  have ev : chart (restr e m i φ) y =ᶠ[𝓝 (oneL E (n i))]
      chart φ (leviEmb (Ad E) e (Function.update m i y)) ∘ iota e i :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun _ hx => chart_restr e m i φ y hx
  have hd : HasFDerivAt (chart φ (leviEmb (Ad E) e (Function.update m i y)) ∘ iota e i)
      ((fderiv ℝ (chart φ (leviEmb (Ad E) e (Function.update m i y))) (oneL E N)).comp (blockCLM e i))
      (oneL E (n i)) := by
    have h1 := (differentiableAt_chart hφ (leviEmb (Ad E) e (Function.update m i y))).hasFDerivAt
    rw [← iota_one e i] at h1
    rw [← iota_one (E := E) e i]
    exact h1.comp _ (hasFDerivAt_iota e i _)
  rw [lieD, ev.fderiv_eq, hd.fderiv]
  rfl

def restrLin (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c) :
    Sm E N →ₗ[ℂ] Sm E (n i) where
  toFun ψ := ⟨restr e m i ψ.1, restr_mem_Sm e m i ψ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrLin_lie (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c)
    (X : Lie E (n i)) : restrLin e m i ∘ₗ lie E N (blockCLM e i X) = lie E (n i) X ∘ₗ restrLin e m i :=
  LinearMap.ext fun ψ => Subtype.ext <| funext fun y => (lieD_restr e m i ψ.2 X y).symm

theorem restrLin_Eop (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c)
    (τ : E →+* ℂ) (p q : Fin (n i)) :
    restrLin e m i ∘ₗ Eop (a := N) τ (e ⟨i, p⟩) (e ⟨i, q⟩) = Eop τ p q ∘ₗ restrLin e m i := by
  have hS : ∀ z : Cinf E, restrLin e m i ∘ₗ lieS E N (e ⟨i, p⟩) (e ⟨i, q⟩) z =
      lieS E (n i) p q z ∘ₗ restrLin e m i := by
    intro z
    rw [lieS_apply, lieS_apply, ← blockLin_single, ← blockCLM_apply, restrLin_lie]
  simp only [Eop]
  rw [LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_smul,
    LinearMap.smul_comp, hS, hS]

theorem qdet_block_levi : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (τ : E →+* ℂ) (i : Fin c) (M : Multiset ℂ),
    (π i).HasInfChar τ M → ∀ (u : ℂ) (ψ : Sm E N),
      (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorForms π → ∀ m,
        (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
          (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) =
          (M.map (u + ·)).prod * ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) := by
  intro E _ _ _ c N n h π τ i M hM u ψ hψ m
  obtain ⟨θ, hθ, hθe⟩ := tensorForms_update π i m hψ
  have hR : restrLin (stdBlocks n h) m i ψ = θ := Subtype.ext (funext fun y => hθe y)
  have key := LinearMap.congr_fun (qdet_intertwine (restrLin (stdBlocks n h) m i) _ (Eop τ)
    (restrLin_Eop (stdBlocks n h) m i τ) (u + ((n i : ℂ) - 1) / 2)) ψ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hR] at key
  have k2 := congrArg (fun φ : Sm E (n i) => φ.1 (m i)) key
  have hc : Formalism.REAL.qdet (Eop τ) (u + ((n i : ℂ) - 1) / 2) θ = (M.map (u + ·)).prod • θ := hM.2 u θ hθ
  have hm : Function.update m i (m i) = m := Function.update_eq_self i m
  simp only [hc] at k2
  have k3 : (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) (Function.update m i (m i))) =
      (M.map (u + ·)).prod * θ.1 (m i) := k2
  rw [hm, ← hθe, hm] at k3
  exact k3

end GlobalTheory.BlockCap
end
end

section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliDet_diagonalBlock_acts_by_infinitesimalCharacter : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (τ : E →+* ℂ) (i : Fin c) (M : Multiset ℂ), (π i).HasInfChar τ M → ∀ (u : ℂ) (ψ : Sm E N), (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorForms π → ∀ m, (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩)) (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) = (M.map (u + ·)).prod * ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) := by
  first | exact @GlobalTheory.BlockCap.qdet_block_levi | exact GlobalTheory.BlockCap.qdet_block_levi | (intros; apply GlobalTheory.BlockCap.qdet_block_levi <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGL_iwasawa_decomposition_standardParabolic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (x : GA E N), ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GA E (n i)) (k : Kinf E N) (g : GL (Fin N) (Af E)), x = u * leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g) := by
  first | exact @GlobalTheory.IwasawaAdelic.iwasawa | exact GlobalTheory.IwasawaAdelic.iwasawa | (intros; apply GlobalTheory.IwasawaAdelic.iwasawa <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.LieFin

theorem lie_mem_finVec : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (X : Lie E N) (φ : Sm E N),
    φ ∈ finVec (cptRep E N) → lie E N X φ ∈ finVec (cptRep E N) := by
  intro E _ _ _ N X φ hφ
  let S : Submodule ℂ (Sm E N) := Submodule.span ℂ (Set.range fun k => cptRep E N k φ)
  haveI : FiniteDimensional ℂ S := hφ
  let b := Module.finBasis ℝ (Lie E N)
  let T : Submodule ℂ (Sm E N) := ⨆ s, S.map (lie E N (b s))
  haveI : FiniteDimensional ℂ T := by
    haveI : ∀ s, FiniteDimensional ℂ (S.map (lie E N (b s))) := fun s => inferInstance
    exact Submodule.finiteDimensional_iSup _
  have key : ∀ (Z : Lie E N) (ψ : Sm E N), ψ ∈ S → lie E N Z ψ ∈ T := by
    intro Z ψ hψ
    rw [← b.sum_repr Z, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [map_smul, LinearMap.smul_apply]
    have h1 : lie E N (b s) ψ ∈ T :=
      (le_iSup (fun s => S.map (lie E N (b s))) s) (Submodule.mem_map_of_mem hψ)
    have h2 : ((b.repr Z s : ℝ) : ℂ) • lie E N (b s) ψ ∈ T := T.smul_mem _ h1
    simpa [Complex.coe_smul] using h2
  show FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k (lie E N X φ)))
  refine Submodule.finiteDimensional_of_le (S₂ := T) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  have e := congrArg (fun f : Module.End ℂ (Sm E N) => f φ) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))
  simp only [Module.End.mul_apply] at e
  change rt E N (infGL E N (Unitary.toUnits k)) (lie E N X φ) ∈ T
  have eX : toL (Matrix.of X) = X := rfl
  rw [eX] at e
  rw [e]
  exact key _ _ (Submodule.subset_span ⟨k, rfl⟩)

end GlobalTheory.LieFin
end

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_mem_compactFiniteVectors_of_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (X : Lie E N) (φ : Sm E N), φ ∈ finVec (cptRep E N) → lie E N X φ ∈ finVec (cptRep E N) := by
  atlas_forward_decl GlobalTheory.LieFin.lie_mem_finVec
end

section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_derivative_induced_tensor_forms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (X : Lie E N) (φ : Sm E N), φ ∈ indForms h π → ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)), (fun m => (lie E N X φ).1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g))) ∈ tensorForms π := by
  first | exact @GlobalTheory.LieTensor.lie_tensorForms | exact GlobalTheory.LieTensor.lie_tensorForms | (intros; apply GlobalTheory.LieTensor.lie_tensorForms <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.SpehInfChar

theorem lie_mem_finVec : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (X : Lie E N)
    (φ : Sm E N), φ ∈ finVec (cptRep E N) → lie E N X φ ∈ finVec (cptRep E N) :=
  GlobalTheory.T.lie_mem_compactFiniteVectors_of_mem

theorem lie_tensorForms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (X : Lie E N) (φ : Sm E N), φ ∈ indForms h π →
    ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)), (fun m => (lie E N X φ).1 (leviEmb (Ad E) (stdBlocks n h) m *
      (infGL E N (Unitary.toUnits k) * finGL E N g))) ∈ tensorForms π :=
  GlobalTheory.T.lie_derivative_induced_tensor_forms

theorem qdet_sub_blocks_mem : ∀ (A : Type) [Ring A] [Algebra ℂ A] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (X : Fin N → Fin N → A), Formalism.REAL.GlRel X → ∀ u : ℂ,
    Formalism.REAL.qdet X (u + ((N : ℂ) - 1) / 2) -
              (List.ofFn fun i : Fin c => Formalism.REAL.qdet (fun p q : Fin (n i) => X (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
                (u + ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod ∈
      Submodule.span ℂ {y : A | ∃ (p q : Fin N) (w : A), blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} :=
  GlobalTheory.T.capelliDet_block_levi_congr_mod_upperBlockIdeal

theorem Eop_leviEmb_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (ψ : Sm E N), (∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g) →
    ∀ (τ : E →+* ℂ) (p q : Fin N), blk (stdBlocks n h) p < blk (stdBlocks n h) q →
    ∀ m, (Eop τ p q ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 :=
  GlobalTheory.T.upperMatrixUnit_kills_unipotentInvariant_on_levi

theorem blockCap_leviEmb : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (τ : E →+* ℂ) (i : Fin c) (M : Multiset ℂ), (π i).HasInfChar τ M →
    ∀ (u : ℂ) (ψ : Sm E N), (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorForms π →
    ∀ m, (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) =
      (M.map (u + ·)).prod * ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) :=
  GlobalTheory.T.capelliDet_diagonalBlock_acts_by_infinitesimalCharacter

theorem exists_iwasawa : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (x : GA E N), ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GA E (n i)) (k : Kinf E N)
      (g : GL (Fin N) (Af E)), x = u * leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g) :=
  GlobalTheory.T.adelicGL_iwasawa_decomposition_standardParabolic

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem lie_leftInv {N : ℕ} (U : Subgroup (GA E N)) (X : Lie E N) {ψ : Sm E N}
    (hψ : ∀ u ∈ U, ∀ g, ψ.1 (u * g) = ψ.1 g) : ∀ u ∈ U, ∀ g, (lie E N X ψ).1 (u * g) = (lie E N X ψ).1 g := by
  intro u hu g
  have e : chart ψ.1 (u * g) = chart ψ.1 g := by
    funext x
    unfold chart
    split_ifs with hx
    · rw [mul_assoc, hψ u hu]
    · rfl
  simp only [lie_apply, lieD, e]

def leftInvAlg {N : ℕ} (U : Subgroup (GA E N)) : Subalgebra ℂ (Module.End ℂ (Sm E N)) where
  carrier := {z | ∀ ψ : Sm E N, (∀ u ∈ U, ∀ g, ψ.1 (u * g) = ψ.1 g) → ∀ u ∈ U, ∀ g, (z ψ).1 (u * g) = (z ψ).1 g}
  mul_mem' hx hy ψ hψ := hx _ (hy ψ hψ)
  add_mem' {x y} hx hy ψ hψ u hu g := by
    change (x ψ).1 (u * g) + (y ψ).1 (u * g) = (x ψ).1 g + (y ψ).1 g
    rw [hx ψ hψ u hu g, hy ψ hψ u hu g]
  algebraMap_mem' c ψ hψ u hu g := by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hψ u hu g]

theorem Eop_mem_leftInvAlg {N : ℕ} (U : Subgroup (GA E N)) (τ : E →+* ℂ) (p q : Fin N) : Eop τ p q ∈ leftInvAlg U := by
  have hL : ∀ X, lie E N X ∈ leftInvAlg U := fun X ψ hψ => lie_leftInv U X hψ
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (hL _) (Subalgebra.smul_mem _ (hL _) _)) _

theorem cap_comm_quot {N : ℕ} {I : Submodule ℂ (Sm E N)} (hI : ∀ X, ∀ φ ∈ I, lie E N X φ ∈ I)
    (f : Sm E N →ₗ[ℂ] Sm E N) (hf : ∀ o, ∀ φ ∈ I, f (act o φ) = act o (f φ)) (τ : E →+* ℂ) (u : ℂ) :
    ∀ φ ∈ I, f (cap τ u φ) = cap τ u (f φ) := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E N)) :=
    { carrier := {z | ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ)}
      mul_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hy φ hφ
        obtain ⟨h2, e2⟩ := hx _ h1
        exact ⟨h2, by simp only [Module.End.mul_apply]; rw [e2, e1]⟩
      add_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hx φ hφ
        obtain ⟨h2, e2⟩ := hy φ hφ
        exact ⟨add_mem h1 h2, by simp only [LinearMap.add_apply, map_add, e1, e2]⟩
      algebraMap_mem' := fun c φ hφ => ⟨by simpa only [Module.algebraMap_end_apply] using I.smul_mem c hφ,
        by simp only [Module.algebraMap_end_apply, map_smul]⟩ }
  have hL : ∀ X, lie E N X ∈ S := fun X φ hφ => ⟨hI X φ hφ, hf (.lie X) φ hφ⟩
  have hE : ∀ i j, Eop τ i j ∈ S := fun i j => S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  have : cap τ u ∈ S := by
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact fun φ hφ => (this φ hφ).2

theorem list_prod_along {ι : Type} {N : ℕ} (ℓ : ι → GA E N) (T : Submodule ℂ (ι → ℂ))
    (l : List (Module.End ℂ (Sm E N) × ℂ))
    (hl : ∀ x ∈ l, ∀ ψ : Sm E N, (fun m => ψ.1 (ℓ m)) ∈ T → ∀ m, (x.1 ψ).1 (ℓ m) = x.2 * ψ.1 (ℓ m)) :
    ∀ ψ : Sm E N, (fun m => ψ.1 (ℓ m)) ∈ T → ∀ m,
      ((l.map Prod.fst).prod ψ).1 (ℓ m) = (l.map Prod.snd).prod * ψ.1 (ℓ m) := by
  induction l with
  | nil => intro ψ _ m; simp
  | cons x l ih =>
    intro ψ hψ m
    have ih' := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have h2 : (fun m => ((l.map Prod.fst).prod ψ).1 (ℓ m)) ∈ T := by
      have : (fun m => ((l.map Prod.fst).prod ψ).1 (ℓ m)) = (l.map Prod.snd).prod • (fun m => ψ.1 (ℓ m)) :=
        funext fun m => by rw [ih' ψ hψ m]; rfl
      rw [this]
      exact T.smul_mem _ hψ
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [hl x (by simp) _ h2 m, ih' ψ hψ m, mul_assoc]

theorem lie_mem_smoothPart {N : ℕ} (X : Lie E N) {φ : Sm E N} (hφ : φ ∈ GlobalTheory.PRep.smoothPart (finRep E N)) :
    lie E N X φ ∈ GlobalTheory.PRep.smoothPart (finRep E N) := by
  have ho : IsOpen {k | finRep E N k φ = φ} := hφ
  refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun k hk => ?_)
  have hk' : finRep E N k φ = φ := hk
  change finRep E N k (lie E N X φ) = lie E N X φ
  have e := congrArg (fun z => z φ) (lie_rt_fin X k)
  simp only [Module.End.mul_apply] at e
  change lie E N X (finRep E N k φ) = finRep E N k (lie E N X φ) at e
  rw [← e, hk']

theorem lie_mem_indForms {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (X : Lie E N)
    (φ : Sm E N) (hφ : φ ∈ indForms h π) : lie E N X φ ∈ indForms h π :=
  ⟨lie_leftInv _ X hφ.1, lie_mem_smoothPart X hφ.2.1, lie_mem_finVec E X φ hφ.2.2.1,
    lie_tensorForms E n h π X φ hφ⟩

theorem cap_indForms {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (τ : E →+* ℂ)
    (M : Fin c → Multiset ℂ) (hM : ∀ i, (π i).HasInfChar τ (M i)) (u : ℂ) (φ : Sm E N) (hφ : φ ∈ indForms h π) :
    cap τ u φ = (∏ i, ((M i).map fun x => u + x - (modExp (fun i => Fin (n i)) i : ℂ) / 2).prod) • φ := by
  set e := stdBlocks n h with he
  set mE : Fin c → ℂ := fun i => (modExp (fun i => Fin (n i)) i : ℂ) / 2 with hmE
  let S : Subalgebra ℂ (Module.End ℂ (Sm E N)) :=
    Algebra.adjoin ℂ (Set.range fun pq : Fin N × Fin N => Eop τ pq.1 pq.2)
  have hSE : ∀ p q, Eop τ p q ∈ S := fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩
  have hSL : S ≤ leftInvAlg (unipRad (Ad E) e) :=
    Algebra.adjoin_le (by rintro _ ⟨pq, rfl⟩; exact Eop_mem_leftInvAlg _ τ pq.1 pq.2)
  let X : Fin N → Fin N → S := fun p q => ⟨Eop τ p q, hSE p q⟩
  have hX : Formalism.REAL.GlRel X := fun a b c' d => Subtype.ext (by
    have := glRel_Eop (a := N) τ a b c' d
    split_ifs at this ⊢ <;> simpa [X] using this)
  have key := qdet_sub_blocks_mem S n h X hX u

  let B : Fin c → Module.End ℂ (Sm E N) := fun i =>
    Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (e ⟨i, p⟩) (e ⟨i, q⟩)) (u + ((n i : ℂ) - 1) / 2 - mE i)
  let sc : Fin c → ℂ := fun i => ((M i).map fun x => u + x - mE i).prod
  have hval : S.val (List.ofFn fun i : Fin c => Formalism.REAL.qdet (fun p q : Fin (n i) => X (e ⟨i, p⟩) (e ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2 - mE i)).prod = (List.ofFn B).prod := by
    rw [map_list_prod, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun i => ?_)
    simp only [Function.comp_apply, B]
    rw [map_qdet]
    rfl
  have hcap : S.val (Formalism.REAL.qdet X (u + ((N : ℂ) - 1) / 2)) = cap τ u := by
    rw [map_qdet]
    rfl

  have hlevi : ∀ ψ : Sm E N, (∀ v ∈ unipRad (Ad E) e, ∀ g, ψ.1 (v * g) = ψ.1 g) →
      (fun m => ψ.1 (leviEmb (Ad E) e m)) ∈ tensorForms π → ∀ m,
      (cap τ u ψ).1 (leviEmb (Ad E) e m) = (∏ i, sc i) * ψ.1 (leviEmb (Ad E) e m) := by
    intro ψ hψ hT m
    let L : S →ₗ[ℂ] ℂ :=
      { toFun := fun w => ((w : Module.End ℂ (Sm E N)) ψ).1 (leviEmb (Ad E) e m)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hker : Submodule.span ℂ {y : S | ∃ (p q : Fin N) (w : S), blk e p < blk e q ∧ y = X p q * w} ≤
        LinearMap.ker L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨p, q, w, hpq, rfl⟩
      change (Eop τ p q ((w : Module.End ℂ (Sm E N)) ψ)).1 (leviEmb (Ad E) e m) = 0
      exact Eop_leviEmb_eq_zero E n h _ (hSL w.2 ψ hψ) τ p q hpq m
    have h1 := hker key
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
    change ((S.val (Formalism.REAL.qdet X _)) ψ).1 _ = ((S.val _) ψ).1 _ at h1
    rw [hcap, hval] at h1
    rw [h1]
    have hl := list_prod_along (leviEmb (Ad E) e) (tensorForms π) (List.ofFn fun i => (B i, sc i)) (by
      intro x hx ψ' hψ' m'
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      have := blockCap_leviEmb E n h π τ i (M i) (hM i) (u - mE i) ψ' hψ' m'
      have e1 : u - mE i + ((n i : ℂ) - 1) / 2 = u + ((n i : ℂ) - 1) / 2 - mE i := by ring
      have e2 : ((M i).map (u - mE i + ·)) = (M i).map fun x => u + x - mE i :=
        Multiset.map_congr rfl fun x _ => by ring
      rw [e1, e2] at this
      exact this) ψ hT m
    simp only [List.map_ofFn] at hl
    rw [List.prod_ofFn] at hl
    exact hl
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨v, hv, m, k, g, rfl⟩ := exists_iwasawa E n h x
  set y := infGL E N (Unitary.toUnits k) * finGL E N g
  have hcapInv : ∀ v ∈ unipRad (Ad E) e, ∀ g, (cap τ u φ).1 (v * g) = (cap τ u φ).1 g := by
    have : cap τ u ∈ S := by
      rw [← hcap]; exact (Formalism.REAL.qdet X _).2
    exact hSL this φ hφ.1
  have hcomm : Commute (cap τ u) (rt E N y) := by
    rw [map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E N τ u _).mul_right (commute_cap_finRep τ u g)
  set ψ := rt E N y φ
  have hψ : ∀ v ∈ unipRad (Ad E) e, ∀ g, ψ.1 (v * g) = ψ.1 g := fun v hv g => by
    simp only [ψ, rt_apply, mul_assoc]
    exact hφ.1 v hv _
  have hψT : (fun m => ψ.1 (leviEmb (Ad E) e m)) ∈ tensorForms π := hφ.2.2.2 k g
  have h3 := hlevi ψ hψ hψT m
  have h4 : (cap τ u ψ).1 (leviEmb (Ad E) e m) = (cap τ u φ).1 (leviEmb (Ad E) e m * y) := by
    rw [← rt_apply, ← Module.End.mul_apply, hcomm.eq]
    rfl
  rw [mul_assoc, hcapInv v hv, ← h4, h3]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ψ, rt_apply]
  rw [hφ.1 v hv]

theorem prod_map_finset_sum {ι : Type} (s : Finset ι) (A : ι → Multiset ℂ) (g : ℂ → ℂ) :
    ((∑ j ∈ s, A j).map g).prod = ∏ j ∈ s, ((A j).map g).prod := by
  classical
  refine Finset.induction_on s (by simp) fun j s hj ih => ?_
  rw [Finset.sum_insert hj, Finset.prod_insert hj, Multiset.map_add, Multiset.prod_add, ih]

theorem cap_commute_act {a : ℕ} (τ : E →+* ℂ) (u : ℂ) (o : Op E a) : Commute (cap (a := a) τ u) (act o) := by
  cases o with
  | fin k => exact commute_cap_finRep τ u k
  | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
  | lie X => exact commute_cap_lie τ u X

theorem hasInfCharGL_of_isSpehOf {N a d : ℕ} {V : Submodule ℂ (Sm E N)} {π : CuspSub E a} (hV : IsSpehOf V π d)
    (τ : E →+* ℂ) : ∃ m, π.HasInfChar τ m ∧ HasInfCharGL V τ (GlobalTheory.SphGal.spehInf d m) := by
  have hm : π.HasInfChar τ ((CG.mk π).infChar τ) :=
    hasInfChar_infChar_of_commute E a (fun τ u o => cap_commute_act τ u o) (CG.mk π) τ
  refine ⟨(CG.mk π).infChar τ, hm, ?_, fun u ψ hψ => ?_⟩
  · have hN := hV.mul_eq
    simp only [GlobalTheory.SphGal.spehInf, Multiset.card_sum, Multiset.card_map, hm.1, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    exact hN
  obtain ⟨hs, ν, hν, f, hfV, hf⟩ := hV
  set m := (CG.mk π).infChar τ
  have hI : ∀ X, ∀ φ ∈ indForms hs (fun i => π.twist (ν i)), lie E N X φ ∈ indForms hs (fun i => π.twist (ν i)) :=
    fun X φ hφ => lie_mem_indForms _ hs _ X φ hφ
  rw [← hfV] at hψ
  obtain ⟨φ, hφ, rfl⟩ := hψ
  have hexpo : ∀ i : Fin d, expo (ν i) τ = ((spehExp d i + a * spehExp d i : ℝ) : ℂ) := fun i =>
    (GlobalTheory.CuspRep.InfType.expo_of_infType E (ν i)).2.1 _ (hν i) τ
  have hmod : ∀ i : Fin d, ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 = ((a * spehExp d i : ℝ) : ℂ) := fun i => by
    rw [mul_spehExp]
    push_cast
    rfl
  have hc := cap_indForms (fun _ : Fin d => a) hs (fun i => π.twist (ν i)) τ (fun i => m.map (· + expo (ν i) τ))
    (fun i => hm.twist (ν i)) u φ hφ
  rw [cap_comm_quot hI f hf τ u φ hφ |>.symm, hc, map_smul]
  congr 1
  rw [GlobalTheory.SphGal.spehInf, prod_map_finset_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [Function.comp_apply]
  have h1 := hexpo i
  have h2 := hmod i
  have h3 : ((spehExp d i : ℝ) : ℂ) = ((d : ℂ) - 1) / 2 - ((i : ℕ) : ℂ) := by
    simp [spehExp]
  change u + (x + expo (ν i) τ) - ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 = u + (x + (((d : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)))
  rw [h1, h2, ← h3]
  push_cast
  ring

theorem discreteSpectrumGL_of_residual : GlobalTheory.Published.DiscreteSpectrumResidual → GlobalTheory.Published.DiscreteSpectrumGL := by
  intro H E _ _ _ N hN
  obtain ⟨h1, h2, h3, h4, h5⟩ := H E N hN
  exact ⟨h1, h2, h3, h4, fun V hV a d π hn e => ⟨fun w => (h5 V hV a d π hn e w).1, fun w => (h5 V hV a d π hn e w).2,
    hasInfCharGL_of_isSpehOf e⟩⟩

end GlobalTheory.SpehInfChar
end
end
