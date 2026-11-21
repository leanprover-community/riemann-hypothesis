import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CondExpEqZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalWhittakerDiagonalShiftRamifiedCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledLocalCharacterUnitConductorConductorExponeStatement

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
open scoped Classical

namespace GlobalTheory.RamShift

theorem whittaker_torusShift_add_factorisation_induction (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ)
    (hα : ∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) (φ) (hφV : φ ∈ π.V)
    (hφ : ∀ w ∉ T, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (hϖ : ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E))
    (x : GA E (m + 1)) (hx : x ∈ GlobalTheory.JSW.supS E (m + 1) T) (L : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ)) :
    (∀ w ∈ T, L w = 0) → (∀ w, 0 ≤ L w (Fin.last m)) →
      GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ ((shift m T ϖ).1 + L)) =
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (shift m T ϖ).1) *
          ∏ w ∈ L.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (L w)) := by
  induction L using Finsupp.induction with
  | zero => intro _ _; simp
  | single_add a b f ha hb ih =>
    intro hT hlast
    have hfa : f a = 0 := Finsupp.notMem_support_iff.1 ha
    have haT : a ∉ T := fun h => hb (by simpa [hfa] using hT a h)
    have hfT : ∀ w ∈ T, f w = 0 := fun w hw => by
      have hne : a ≠ w := fun e => haT (e ▸ hw)
      simpa [Finsupp.single_apply, hne] using hT w hw
    have hflast : ∀ w, 0 ≤ f w (Fin.last m) := fun w => by
      by_cases hw : a = w
      · subst hw; simp [hfa]
      · simpa [Finsupp.single_apply, hw] using hlast w
    have hblast : 0 ≤ b (Fin.last m) := by simpa [hfa] using hlast a
    set l₀ := (shift m T ϖ).1 with hl₀
    have hsplit : l₀ + (Finsupp.single a b + f) =
        (l₀ - Finsupp.single a (l₀ a) + f) + Finsupp.single a (l₀ a + b) := by
      ext w i
      by_cases hw : a = w
      · subst hw; simp [hfa]
      · simp [Finsupp.single_apply, hw]
    have hjoin : (l₀ - Finsupp.single a (l₀ a) + f) + Finsupp.single a (l₀ a) = l₀ + f := by
      ext w i
      by_cases hw : a = w
      · subst hw; simp [hfa]
      · simp [Finsupp.single_apply, hw]
    set g := x * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀ - Finsupp.single a (l₀ a) + f) with hg
    have hga : GeneralLinearGroup.map ((pLoc E a).comp (pFin E)) g = 1 := by
      change GlobalTheory.CellDec.compV E (m + 1) a g = 1
      rw [hg, map_mul, GlobalTheory.CellDec.compV_tl]
      have h0 : (l₀ - Finsupp.single a (l₀ a) + f) a = 0 := by simp [hfa]
      have hxa : GlobalTheory.CellDec.compV E (m + 1) a x = 1 := hx a haT
      rw [h0, hxa, GlobalTheory.IwaCell.tD_zero, one_mul]
    have hl₀a : l₀ a = fun i : Fin (m + 1) => condExp ϖ a * ((m : ℤ) - ((i : ℕ) : ℤ)) :=
      shift_apply_of_notMem m ϖ haT
    have key := GlobalTheory.T.sphericalWhittaker_diagonalShift_ramifiedCharacter E m π a (α ⟨a, haT⟩) (hα ⟨a, haT⟩) φ hφV (hφ a haT) (ϖ a) (hϖ a) (condExp ϖ a)
      (GlobalTheory.T.scaledLocalCharacter_unitConductor_conductorExponent E ϖ a (hϖ a)) g hga b hblast
    have h1 : l₀ a + b = fun i : Fin (m + 1) => condExp ϖ a * ((m : ℤ) - ((i : ℕ) : ℤ)) + b i := by
      rw [hl₀a]; rfl
    rw [hsplit, GlobalTheory.CellDec.tl_add, GlobalTheory.CellDec.tl_single, ← mul_assoc, ← hg, h1, key, ← hl₀a,
      ← GlobalTheory.CellDec.tl_single, hg, mul_assoc, ← GlobalTheory.CellDec.tl_add, hjoin, ih hfT hflast,
      Finsupp.support_single_add ha hb, Finset.prod_cons, dif_neg haT]
    have hval : (Finsupp.single a b + f) a = b := by simp [hfa]
    have hrest : ∏ w ∈ f.support, (if h : w ∈ T then 1 else
          GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) ((Finsupp.single a b + f) w)) =
        ∏ w ∈ f.support, (if h : w ∈ T then 1 else
          GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (f w)) := by
      refine Finset.prod_congr rfl fun w hw => ?_
      have hne : a ≠ w := fun e => ha (e ▸ hw)
      simp [Finsupp.single_apply, hne]
    rw [hval, hrest]
    change GlobalTheory.RSCell.sphZ (Ideal.absNorm a.asIdeal) _ b * _ = _
    ring

theorem whit_mul_tl_shift_add : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)) (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ x ∈ GlobalTheory.JSW.supS E (m + 1) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ ((GlobalTheory.RamShift.shift m T ϖ).1 + l.1)) =
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  intro E _ _ _ m T π α hα φ hφV hφ ϖ hϖ x hx l hl
  exact whittaker_torusShift_add_factorisation_induction E m T π α hα φ hφV hφ ϖ hϖ x hx l.1 l.2 hl

end GlobalTheory.RamShift
end
end

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_mul_torusShift_add_eq_sphericalProduct : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)) (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ x ∈ GlobalTheory.JSW.supS E (m + 1) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ ((GlobalTheory.RamShift.shift m T ϖ).1 + l.1)) =
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  atlas_forward_decl GlobalTheory.RamShift.whit_mul_tl_shift_add
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.JSW.NzSphRam

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne GlobalTheory.JSW.NzSph

variable {E : Type} [Field E] [NumberField E]

theorem diagPow_eq_tD {K : Type} [Field K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) :
    GlobalTheory.JSW.diagPow ϖ l = GlobalTheory.IwaCell.tD ϖ (fun i => ((l i : ℕ) : ℤ)) := by
  apply Units.ext
  unfold GlobalTheory.IwaCell.tD
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  simp [GlobalTheory.JSW.diagPow, Matrix.diagonal_apply]

variable [IsTotallyComplex E]

theorem exists_whittaker_ne_zero_induction_bad_places (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ)
    (hα : ∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (hϖ : ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E))
    (R : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) → ∀ g : GA E (m + 1),
      (∀ w ∉ T, w ∉ R → GlobalTheory.CellDec.compV E (m + 1) w
        ((GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1)⁻¹ * g) ∈ KGL w (m + 1)) → whit φ.1 g ≠ 0 →
      ∃ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧
        ∃ x ∈ GlobalTheory.JSW.supS E (m + 1) T,
          whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) ≠ 0 := by
  classical
  set t0 := GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1 with ht0
  induction R using Finset.induction_on with
  | empty =>
    intro φ hφV hφ g hg hW
    obtain ⟨k, hk1, hk2⟩ := exists_outside E (m + 1) T (GeneralLinearGroup.map (pFin E) (t0⁻¹ * g))
    have hinv : act (.fin k) φ = φ := act_fin_eq_of_outside E (m + 1) φ (π.cusp φ hφV).1 T hφ k
      (fun w hw => by rw [hk1 w hw, map_pLoc_pFin]; exact hg w hw (Finset.notMem_empty w)) hk2
    refine ⟨φ, hφV, hφ, g * (finGL E (m + 1) k)⁻¹ * t0⁻¹, fun w hw => ?_, ?_⟩
    · simp only [map_mul, map_inv]
      rw [comp_finGL, hk1 w hw, map_pLoc_pFin]
      simp only [map_mul, map_inv]
      group
    · have e : g * (finGL E (m + 1) k)⁻¹ * t0⁻¹ * t0 = g * (finGL E (m + 1) k)⁻¹ := by group
      rw [e]
      have e2 : g = g * (finGL E (m + 1) k)⁻¹ * finGL E (m + 1) k := by group
      rw [e2, ← whit_act_fin, hinv] at hW
      exact hW
  | insert w R hwR ih =>
    intro φ hφV hφ g hg hW
    by_cases hwT : w ∈ T
    · refine ih φ hφV hφ g (fun v hv hvR => hg v hv ?_) hW
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hv (h ▸ hwT), hvR⟩
    let gw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g
    obtain ⟨u, hu, N, l, k, hk, hdec⟩ := local_decomp E (m + 1) w (ϖ w) (hϖ w) gw
    let z := GlobalTheory.JSW.diagPow (ϖ w)⁻¹ (fun _ : Fin (m + 1) => N)
    let d := GlobalTheory.JSW.diagPow (ϖ w) l
    let F : GL (Fin (m + 1)) (w.adicCompletion E) →* GA E (m + 1) := (finGL E (m + 1)).comp (locGL E (m + 1) w)
    have hF : ∀ h, F h = finGL E (m + 1) (locGL E (m + 1) w h) := fun h => rfl
    let y := g * (F gw)⁻¹
    have hyw : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y = 1 := by
      show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (g * (finGL E (m + 1) (locGL E (m + 1) w gw))⁻¹) = 1
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL]; exact mul_inv_cancel _
    have hyv : ∀ v, v ≠ w → GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) y =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g := by
      intro v hv
      show GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (g * (finGL E (m + 1) (locGL E (m + 1) w gw))⁻¹) = _
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL_of_ne hv, inv_one, mul_one]
    have hg' : g = y * F u * F z * F d * F k := by
      have : F gw = F u * F z * F d * F k := by
        rw [hdec, map_mul, map_mul, map_mul]
      calc g = y * F gw := by simp only [y]; group
        _ = _ := by rw [this]; simp only [mul_assoc]
    have hcont : Continuous φ.1 := (π.cusp _ hφV).1.continuous
    have hleft : AutomorphicForm.IsLeftInvariant φ.1 := fun γ x => by
      rw [show AdelicGLn.diagonal E (m + 1) γ = ratGL E (m + 1) γ from Units.ext (Matrix.ext fun _ _ => rfl)]
      exact (π.cusp _ hφV).1.left γ x

    have h1 : whit φ.1 (y * F u * F z * F d) ≠ 0 := by
      rw [hg', hF k, ← whit_act_fin, hφ w hwT k hk] at hW
      exact hW

    have h2 : whit φ.1 (y * F z * F d) ≠ 0 := by
      have e : y * F u * F z * F d = F u * (y * F z * F d) := by
        rw [hF u, commute_finGL_locGL w hyw u]; group
      rw [e, hF u, finGL_locGL_eq_uGL w hu, whit, whittaker_uGL_mul hcont hleft] at h1
      exact right_ne_zero_of_mul h1

    let φ₁ := act (.fin (locGL E (m + 1) w z)) φ
    have hφ₁V : φ₁ ∈ π.V := π.stable _ φ hφV
    have hφ₁ : ∀ v ∉ T, ∀ k' ∈ KGL v (m + 1), act (.fin (locGL E (m + 1) v k')) φ₁ = φ₁ := by
      intro v hv k' hk'
      have hc : locGL E (m + 1) v k' * locGL E (m + 1) w z = locGL E (m + 1) w z * locGL E (m + 1) v k' := by
        by_cases hvw : v = w
        · subst hvw; rw [← map_mul, ← map_mul, diagPow_const_comm]
        · exact (GlobalTheory.CuspRep.LocSph.comm_locGL v (locGL E (m + 1) w z) (pLoc_locGL_of_ne hvw z) k').symm
      simp only [φ₁]
      rw [← act_fin_mul, hc, act_fin_mul, hφ v hv k' hk']
    have h3 : whit φ₁.1 (y * F d) ≠ 0 := by
      have e : y * F z * F d = y * F d * F z := by
        rw [mul_assoc y (F z), mul_assoc y (F d), ← map_mul, ← map_mul, diagPow_const_comm]
      rw [e, hF z, ← whit_act_fin] at h2
      exact h2

    let e0 : ℤ := GlobalTheory.RamShift.condExp ϖ w
    let d0 := GlobalTheory.IwaCell.tD (ϖ w) (fun i : Fin (m + 1) => e0 * ((m : ℤ) - ((i : ℕ) : ℤ)))
    let ν : Fin (m + 1) → ℤ := fun i => ((l i : ℕ) : ℤ) - e0 * ((m : ℤ) - ((i : ℕ) : ℤ))
    have hν : 0 ≤ ν (Fin.last m) := by simp [ν]
    have hloc := GlobalTheory.T.sphericalWhittaker_diagonalShift_ramifiedCharacter E m π w (α ⟨w, hwT⟩) (hα ⟨w, hwT⟩) φ₁ hφ₁V (hφ₁ w hwT) (ϖ w) (hϖ w) e0
      (GlobalTheory.T.scaledLocalCharacter_unitConductor_conductorExponent E ϖ w (hϖ w)) y hyw ν hν
    have htD : GlobalTheory.IwaCell.tD (ϖ w) (fun i : Fin (m + 1) => e0 * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i) = d := by
      simp only [d, diagPow_eq_tD]
      congr 1
      funext i
      simp only [ν]
      ring
    have h4 : whit φ₁.1 (y * F d0) ≠ 0 := by
      have h3' : whit φ₁.1 (y * finGL E (m + 1) (locGL E (m + 1) w
          (GlobalTheory.IwaCell.tD (ϖ w) (fun i : Fin (m + 1) => e0 * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) ≠ 0 := by
        rw [htD]; exact h3
      rw [hloc] at h3'
      exact right_ne_zero_of_mul h3'
    refine ih φ₁ hφ₁V hφ₁ (y * F d0) (fun v hv hvR => ?_) h4
    by_cases hvw : v = w
    · subst hvw
      have hc : GlobalTheory.CellDec.compV E (m + 1) v t0 = d0 := by
        rw [ht0, GlobalTheory.CellDec.compV_tl, GlobalTheory.RamShift.shift_apply_of_notMem m ϖ hv]
      have hy1 : GlobalTheory.CellDec.compV E (m + 1) v y = 1 := hyw
      rw [map_mul, map_inv, map_mul, hc, hy1, hF, GlobalTheory.CellDec.compV_finGL_locGL_same, one_mul, inv_mul_cancel]
      exact one_mem _
    · have hyv' : GlobalTheory.CellDec.compV E (m + 1) v y = GlobalTheory.CellDec.compV E (m + 1) v g := hyv v hvw
      have hgv := hg v hv (by rw [Finset.mem_insert, not_or]; exact ⟨hvw, hvR⟩)
      rw [map_mul, map_mul, hyv', hF, GlobalTheory.CellDec.compV_finGL_locGL_ne hvw, mul_one, ← map_mul]
      exact hgv

end GlobalTheory.JSW.NzSphRam

namespace GlobalTheory.JSW.NzSphRam

open GlobalTheory.JSW.NzSph

theorem exists_sph_whit_tl_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)) (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∃ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧
      ∃ x ∈ GlobalTheory.JSW.supS E (m + 1) T,
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) ≠ 0 := by
  intro E _ _ _ m T π α hα ϖ hϖ
  classical
  let B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ := fun w =>
    if h : w ∈ T then 0 else Finset.univ.val.map (α ⟨w, h⟩)
  obtain ⟨φ₀, hφ₀V, hφ₀0, hφ₀K⟩ := GlobalTheory.T.exists_global_spherical_vector_of_satake_family E (m + 1) π T B (fun w hw => by
    simp only [B, dif_neg hw]; exact hα ⟨w, hw⟩)
  obtain ⟨g, hg⟩ : ∃ g, whit φ₀.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ₀0 (GlobalTheory.T.cusp_form_eq_zero_of_whittaker_vanishing E (m + 1) φ₀ (π.cusp φ₀ hφ₀V) h)
  set t0 := GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1
  have hfin := finite_bad E (m + 1) (GeneralLinearGroup.map (pFin E) (t0⁻¹ * g))
  refine exists_whittaker_ne_zero_induction_bad_places m T π α hα ϖ hϖ hfin.toFinset φ₀ hφ₀V hφ₀K g (fun w _ hwR => ?_) hg
  by_contra h
  refine hwR (hfin.mem_toFinset.2 ?_)
  show GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (t0⁻¹ * g)) ∉ KGL w (m + 1)
  rw [map_pLoc_pFin]; exact h

end GlobalTheory.JSW.NzSphRam
end
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spherical_whittaker_torusElement_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)) (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∃ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧
      ∃ x ∈ GlobalTheory.JSW.supS E (m + 1) T,
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) ≠ 0 := by
  first | (exact @GlobalTheory.JSW.NzSphRam.exists_sph_whit_tl_ne_zero) | (exact GlobalTheory.JSW.NzSphRam.exists_sph_whit_tl_ne_zero) | (intros; apply GlobalTheory.JSW.NzSphRam.exists_sph_whit_tl_ne_zero  <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.RamShift

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

theorem eq_finGL_of_pInf {q : GA E n} (hq : GeneralLinearGroup.map (pInf E) q = 1) :
    q = finGL E n (GeneralLinearGroup.map (pFin E) q) := by
  have h := infGL_mul_finGL q
  rw [hq, map_one, one_mul] at h
  exact h.symm

theorem pInf_tl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl n ϖ l) = 1 := by
  unfold GlobalTheory.CellDec.tl
  exact pInf_finGL _

theorem compV_tl_of_eq_zero (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {v : HeightOneSpectrum (𝓞 E)} (hv : l v = 0) :
    GlobalTheory.CellDec.compV E n v (GlobalTheory.CellDec.tl n ϖ l) = 1 := by
  rw [GlobalTheory.CellDec.compV_tl, hv, GlobalTheory.IwaCell.tD_zero]

theorem one_mem_mirS (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : (1 : GA E (m + 1)) ∈ GlobalTheory.JSW.mirS E S m := by
  refine ⟨fun w _ => map_one _, fun j => ?_⟩
  rw [Units.val_one, Matrix.one_apply]
  by_cases h : j = Fin.last m
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem mem_NA_of_mem {u : GA E n} (hu : u ∈ GlobalTheory.JSW.NA E n) : u ∈ GlobalTheory.CellDec.NA E n :=
  (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => hu.1 i j hij, hu.2⟩

end GlobalTheory.RamShift

open GlobalTheory.RamShift in

theorem GlobalTheory.RamShift.exists_shifted_bump_shintani : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)), π.IsUnitary → ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∃ F ∈ GlobalTheory.JSW.mspanR π, ∃ l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, l₀.1 w (Fin.last m) = 0) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧
      (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
        (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, F (g * k) = F g) ∧
      GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E T m,
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) ∧
      ∀ p ∈ GlobalTheory.JSW.mirS E T m, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  intro E _ _ _ m T π _ α hα ϖ hϖ
  set l₀ := shift m T ϖ with hl₀
  set t₀ := GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 with ht₀def
  have ht₀inf : GeneralLinearGroup.map (pInf E) t₀ = 1 := pInf_tl ϖ l₀.1
  set D := GeneralLinearGroup.map (pFin E) t₀ with hD
  have ht₀ : t₀ = finGL E (m + 1) D := eq_finGL_of_pInf ht₀inf
  obtain ⟨b, hb1, hbN, hbC, hbU, hbS⟩ := GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic E m T
  obtain ⟨φ, hφV, hφK, x₀, hx₀, hW₀⟩ := GlobalTheory.T.exists_spherical_whittaker_torusElement_ne_zero E m T π α hα ϖ hϖ
  set φ' := act (.fin D) φ with hφ'def
  have hφ'V : φ' ∈ π.V := π.stable _ φ hφV
  have hφ' : ∀ g, φ'.1 g = φ.1 (g * t₀) := fun g => by rw [ht₀]; rfl
  have hWφ' : ∀ y, whit φ'.1 y = whit φ.1 (y * t₀) := fun y => by
    rw [whit_mul_right]
    congr 1
    funext z
    exact hφ' z
  obtain ⟨F₀, hF₀V, hF₀b, hF₀U, hF₀inv, hF₀rel⟩ :=
    GlobalTheory.T.kirillov_semilocal_smooth_bump E m T b hbN hbC hbU hbS π φ' hφ'V ⟨x₀, hx₀, by rw [hWφ']; exact hW₀⟩
  have hWF : ∀ y, whit (fun g => F₀ (g * t₀⁻¹)) y = whit F₀ (y * t₀⁻¹) := fun y =>
    (whit_mul_right F₀ y t₀⁻¹).symm
  refine ⟨fun g => F₀ (g * t₀⁻¹), mspanR_rt hF₀V _, l₀, fun w => shift_last m T ϖ w, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨U, hUo, hU⟩ := hF₀U
    refine ⟨U.comap (MulAut.conj D).toMonoidHom, ?_, fun u hu g => ?_⟩
    · exact hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have e : g * finGL E (m + 1) u * t₀⁻¹ = g * t₀⁻¹ * finGL E (m + 1) (D * u * D⁻¹) := by
        rw [ht₀, map_mul, map_mul, map_inv]; group
      show F₀ (g * finGL E (m + 1) u * t₀⁻¹) = F₀ (g * t₀⁻¹)
      rw [e]
      exact hU _ hu _
  ·
    intro k hk hkinf hkT g
    have hkf := eq_finGL_of_pInf hkinf
    set kf := GeneralLinearGroup.map (pFin E) k with hkfdef
    have hφk : act (.fin kf) φ = φ := GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed E (m + 1) φ (π.cusp φ hφV).1 T hφK kf
      (fun w hw => by
        have := GlobalTheory.CellDec.mem_US.1 hk w hw
        exact this)
      (fun w hw => hkT w hw)
    have e : g * k * t₀⁻¹ = g * t₀⁻¹ * (t₀ * k * t₀⁻¹) := by group
    show F₀ (g * k * t₀⁻¹) = F₀ (g * t₀⁻¹)
    rw [e]
    refine hF₀inv _ ?_ ?_ ?_ _
    · rw [map_mul, map_mul, map_inv, ht₀inf, hkinf]; simp
    · intro w hw
      change GlobalTheory.CellDec.compV E (m + 1) w (t₀ * k * t₀⁻¹) = 1
      rw [map_mul, map_mul, map_inv, compV_tl_of_eq_zero ϖ l₀.1 (l₀.2 w hw), hkT w hw]; simp
    · intro y
      rw [hφ', hφ']
      have e2 : y * (t₀ * k * t₀⁻¹) * t₀ = y * t₀ * finGL E (m + 1) kf := by rw [← hkf]; group
      rw [e2]
      exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 (y * t₀)) hφk
  ·
    rw [hWF, mul_inv_cancel, hF₀b 1 (one_mem_mirS T m), hb1]
    exact one_ne_zero
  ·
    obtain ⟨C, hC, hCp⟩ := hbC
    refine ⟨C, hC, fun p hp hne => ?_⟩
    rw [hWF, mul_inv_cancel_right, hF₀b p hp] at hne
    obtain ⟨u, hu, hup⟩ := hCp p hp hne
    exact ⟨u⁻¹, inv_mem (mem_NA_of_mem hu), hup⟩
  ·
    intro p hp l hl
    have hcomm : GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1) = GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * t₀ := by
      rw [add_comm l₀.1 l.1, GlobalTheory.CellDec.tl_add]
    rw [hWF, hWF, hcomm, ← mul_assoc, mul_inv_cancel_right, mul_inv_cancel_right]
    rw [hF₀rel (GlobalTheory.CellDec.tl (m + 1) ϖ l.1) _ (pInf_tl ϖ l.1)
      (fun w hw => compV_tl_of_eq_zero ϖ l.1 (l.2 w hw)) (fun x hx => ?_) p hp.1, mul_comm]
    rw [hWφ', hWφ', mul_assoc, ← GlobalTheory.CellDec.tl_add, add_comm l.1 l₀.1, GlobalTheory.T.whittaker_mul_torusShift_add_eq_sphericalProduct E m T π α hα φ hφV hφK ϖ hϖ x hx l hl, mul_comm]
end

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shifted_vector_shintani_formula_ramified : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)), π.IsUnitary → ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∃ F ∈ GlobalTheory.JSW.mspanR π, ∃ l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, l₀.1 w (Fin.last m) = 0) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧
      (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
        (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, F (g * k) = F g) ∧
      GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E T m,
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) ∧
      ∀ p ∈ GlobalTheory.JSW.mirS E T m, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  atlas_forward_decl GlobalTheory.RamShift.exists_shifted_bump_shintani
end
