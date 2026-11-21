import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZeroStatement
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalMirabolicWhittakerStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1)) := by
  first | exact @GlobalTheory.WhitBump.exists_bump | exact GlobalTheory.WhitBump.exists_bump | (intros; apply GlobalTheory.WhitBump.exists_bump <;> assumption)
end

section
section
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW

theorem map_pLoc_pFin_finGL_locGL_of_ne {E : Type} [Field E] [NumberField E] {a : ℕ}
    {v w : HeightOneSpectrum (𝓞 E)} (h : v ≠ w) (k : GL (Fin a) (w.adicCompletion E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a (locGL E a w k)) = 1 := by
  have e : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a (locGL E a w k)) =
      GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) (finGL E a (locGL E a w k))) := by
    ext; rfl
  rw [e, pFin_finGL, pLoc_locGL_of_ne h]

theorem whit_mul_list_prod (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ) (φ) (hφV : φ ∈ π.V)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) → Fin a → ℕ)
    (L : List (HeightOneSpectrum (𝓞 E))) (hL : L.Nodup)
    (hw : ∀ w ∈ L, (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) ∧
      HasSatGL w (π.locRep w) (Finset.univ.val.map (α w)) ∧
      (∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) ∧ IsUnifV E w (ϖ w : w.adicCompletion E)) :
    ∀ g : GA E a, (∀ w ∈ L, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1) →
      GlobalTheory.JSW.whit φ.1 (g * (L.map fun w => finGL E a (locGL E a w (diagPow (ϖ w) (l w)))).prod) =
        (L.map fun w => GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)).prod * GlobalTheory.JSW.whit φ.1 g := by
  induction L with
  | nil => intro g _; simp
  | cons w L ih =>
    intro g hg
    rw [List.nodup_cons] at hL
    have hw0 := hw w (List.mem_cons_self ..)
    have ih' := ih hL.2 (fun v hv => hw v (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, ih' (g * finGL E a (locGL E a w (diagPow (ϖ w) (l w)))) ?_,
      whit_mul_locGL_diagPow E a π w (α w) hw0.1 hw0.2.1 φ hφV hw0.2.2.1 g (hg w (List.mem_cons_self ..))
        (ϖ w) hw0.2.2.2 (l w)]
    · ring
    · intro v hv
      have hne : v ≠ w := fun h => hL.1 (h ▸ hv)
      rw [map_mul, hg v (List.mem_cons_of_mem _ hv), map_pLoc_pFin_finGL_locGL_of_ne hne, one_mul]

theorem whit_mul_tl : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) → ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ x ∈ GlobalTheory.JSW.supS E a S, GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.JSW.tl ϖ l) = (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ.1 x := by
  intro E _ _ _ a S hψ π α hα φ hφV hφ ϖ hϖ l hl x hx
  have hmem : ∀ w ∈ l.support.toList, w ∉ S := fun w hw => hl w (Finset.mem_toList.1 hw)
  rw [tl, whit_mul_list_prod E a π α φ hφV ϖ l l.support.toList (Finset.nodup_toList _)
      (fun w hw => ⟨hψ w (hmem w hw), hα w (hmem w hw), hφ w (hmem w hw), hϖ w⟩) x
      (fun w hw => hx w (hmem w hw))]
  congr 1
  exact Finset.prod_map_toList _ _

end GlobalTheory.JSW
end
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_mul_torus_iterated_factorisation : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) → ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ x ∈ GlobalTheory.JSW.supS E a S, GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.JSW.tl ϖ l) = (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ.1 x := by
  atlas_forward_decl GlobalTheory.JSW.whit_mul_tl
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.IwasawaLast

theorem exists_unitary_lastRow {n : ℕ} (ℓ : Fin (n + 1) → ℂ) (hℓ : ℓ ≠ 0) :
    ∃ r : ℂ, r ≠ 0 ∧ ∃ k ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ l, ℓ l = r * k (Fin.last n) l := by
  set x : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 (star ℓ) with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply hℓ
    have : star ℓ = 0 := by
      have := congrArg WithLp.ofLp h
      simpa [hx] using this
    simpa using congrArg star this
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  set w : EuclideanSpace ℂ (Fin (n + 1)) := ((‖x‖ : ℂ)⁻¹) • x with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul]
    simp [hn]
  have hon : Orthonormal ℂ (({Fin.last n} : Set (Fin (n + 1))).domRestrict (fun _ => w)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp [Set.domRestrict, inner_self_eq_norm_sq_to_K, hw1]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hbl : b (Fin.last n) = w := hb _ (Set.mem_singleton _)
  set M := (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toBasis.toMatrix b with hM
  have hMu : M ∈ unitaryGroup (Fin (n + 1)) ℂ :=
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _
  refine ⟨(‖x‖ : ℂ), by exact_mod_cast hn, star M, ?_, ?_⟩
  · exact Unitary.star_mem hMu
  · intro l
    simp [hM, Matrix.star_apply, Module.Basis.toMatrix_apply, hbl, hw, hx]
    have hn' : ((‖WithLp.toLp 2 (star ℓ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← mul_assoc, mul_inv_cancel₀ hn', one_mul]

end GlobalTheory.IwasawaLast

namespace GlobalTheory.IwasawaLast

theorem iwasawa_lastRow : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (y : GL (Fin (m + 1)) (Cinf E)), ∃ (p : GL (Fin (m + 1)) (Cinf E)) (ρ : (Cinf E)ˣ) (k : Kinf E (m + 1)), (∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧ y = p * Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom ρ * Unitary.toUnits k := by
  intro E _ _ _ m y
  set Y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E) := (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) with hY
  set ℓ : InfinitePlace E → Fin (m + 1) → ℂ := fun v j => Y (Fin.last m) j v with hℓdef
  have hne : ∀ v, ℓ v ≠ 0 := by
    intro v h
    have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp (Units.isUnit y)
    have hv : IsUnit (Y.det v) := (Pi.isUnit_iff.mp hdet) v
    have hmap : Y.det v = ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).mapMatrix Y).det :=
      RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) Y
    have h0 : ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).mapMatrix Y).det = 0 :=
      Matrix.det_eq_zero_of_row_eq_zero (Fin.last m) (fun j => by
        simpa [hℓdef] using congrFun h j)
    rw [hmap, h0] at hv
    exact not_isUnit_zero hv
  choose r hr kv hkv hℓ using fun v => exists_unitary_lastRow (ℓ v) (hne v)
  set K : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E) := Matrix.of fun i j v => kv v i j with hKdef
  have hK : K ∈ unitaryGroup (Fin (m + 1)) (Cinf E) := by
    rw [mem_unitaryGroup_iff]
    ext i j v
    have := congrFun (congrFun (mem_unitaryGroup_iff.mp (hkv v)) i) j
    by_cases hij : i = j <;> simp [hKdef, Matrix.mul_apply, Finset.sum_apply, Matrix.star_apply, Matrix.one_apply, hij] at this ⊢ <;> exact this
  have hρ : IsUnit (fun v => r v : Cinf E) := Pi.isUnit_iff.mpr fun v => (hr v).isUnit
  refine ⟨y * (Unitary.toUnits (⟨K, hK⟩ : Kinf E (m + 1)))⁻¹ *
      (Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom hρ.unit)⁻¹,
    hρ.unit, ⟨K, hK⟩, ?_, by group⟩
  intro j
  ext v
  have hinv : (((Unitary.toUnits (⟨K, hK⟩ : Kinf E (m + 1)))⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) = star K := rfl
  have hρv : ((hρ.unit⁻¹ : (Cinf E)ˣ) : Cinf E) v = (r v)⁻¹ := by
    have h1 := congrFun hρ.unit.inv_mul v
    simp only [Units.val_mul, Pi.mul_apply, IsUnit.unit_spec, Units.val_one, Pi.one_apply] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hrow : ∀ l, Y (Fin.last m) l v = r v * kv v (Fin.last m) l := fun l => hℓ v l
  have hu := congrFun (congrFun (mem_unitaryGroup_iff.mp (hkv v)) (Fin.last m)) j
  simp only [Units.val_mul, Units.coe_map_inv, MonoidHom.coe_coe, hinv]
  rw [← hY]
  show (Y * star K * Matrix.scalar (Fin (m + 1)) ((hρ.unit⁻¹ : (Cinf E)ˣ) : Cinf E)) (Fin.last m) j v = _
  rw [Matrix.scalar_apply, Matrix.mul_diagonal]
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Pi.mul_apply, hρv, Matrix.mul_apply, Finset.sum_apply, hrow, Matrix.star_apply, Pi.star_apply, hKdef, Matrix.of_apply] at hu ⊢
  have hs : ∑ x, r v * kv v (Fin.last m) x * star (kv v j x) = r v * ∑ x, kv v (Fin.last m) x * star (kv v j x) := by
    rw [Finset.mul_sum]; simp [mul_assoc]
  rw [hs, hu, Matrix.one_apply]
  by_cases hj : j = Fin.last m
  · subst hj; simp [hr v]
  · simp [hj, Ne.symm hj]

end GlobalTheory.IwasawaLast
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mirabolic_scalar_unitary_decomposition_archimedean : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (y : GL (Fin (m + 1)) (Cinf E)), ∃ (p : GL (Fin (m + 1)) (Cinf E)) (ρ : (Cinf E)ˣ) (k : Kinf E (m + 1)), (∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧ y = p * Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom ρ * Unitary.toUnits k := by
  atlas_forward_decl GlobalTheory.IwasawaLast.iwasawa_lastRow
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.JSW

theorem continuous_whit_infGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g h : GA E a,
      Continuous (fun y : GL (Fin a) (Cinf E) => GlobalTheory.JSW.whit φ.1 (g * infGL E a y * h)) := by
  intro E _ _ _ a φ hφ g h
  have hc : Continuous φ.1 := hφ.continuous
  have hW : Continuous (GlobalTheory.JSW.whit φ.1) := by
    have : GlobalTheory.JSW.whit φ.1 = GroundTheory.Automorphic.FourierWhittaker.partialCoeff φ.1 0 := by
      funext x
      exact GroundTheory.Automorphic.FourierWhittaker.whittaker_eq_partialCoeff_zero hc x
    rw [this]
    exact GroundTheory.Automorphic.FourierWhittaker.continuous_partialCoeff hc 0
  exact hW.comp ((continuous_const.mul GlobalTheory.ConstTermSmooth.continuous_infGL).mul continuous_const)

end GlobalTheory.JSW
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_globalWhittakerCoefficient_archimedean : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ g h : GA E a, Continuous (fun y : GL (Fin a) (Cinf E) => GlobalTheory.JSW.whit φ.1 (g * infGL E a y * h)) := by
  atlas_forward_decl GlobalTheory.JSW.continuous_whit_infGL
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.UnitsDense

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem denseRange_embeddings' : DenseRange fun (x : E) (w : InfinitePlace E) => w.embedding x := by
  have h1 := NumberField.InfiniteAdeleRing.denseRange_algebraMap E
  have hs : Function.Surjective
      (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) := by
    intro y
    choose x hx using fun w : InfinitePlace E =>
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (y w)
    exact ⟨x, funext hx⟩
  have hc : Continuous (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) :=
    continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have := hs.denseRange.comp h1 hc
  convert this using 1
  funext x w
  change w.embedding x = InfinitePlace.Completion.extensionEmbedding w (algebraMap E (InfiniteAdeleRing E) x w)
  rw [InfiniteAdeleRing.algebraMap_apply]
  have := InfinitePlace.Completion.extensionEmbedding_coe (v := w) ((WithAbs.equiv w.1).symm x)
  simp only [RingEquiv.apply_symm_apply] at this
  rw [← this]
  rfl

theorem exists_unit_mem_open :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (V : Set (Cinf E)ˣ), IsOpen V → V.Nonempty →
      ∃ α : Eˣ, Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom α ∈ V := by
  intro E _ _ _ V hV ⟨v, hv⟩
  have hU : IsOpen (Units.val '' V) := Units.isOpenEmbedding_val.isOpenMap V hV
  have hd : DenseRange fun x : E => pInf E (algebraMap E (Ad E) x) := by
    have : (fun x : E => pInf E (algebraMap E (Ad E) x)) = fun (x : E) (w : InfinitePlace E) => w.embedding x := by
      funext x w; exact pInf_algebraMap x w
    rw [this]; exact denseRange_embeddings'
  obtain ⟨x, u, hu, hxu⟩ := hd.exists_mem_open hU ⟨v.1, v, hv, rfl⟩
  have hx : x ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hxu
    haveI : Nonempty (InfinitePlace E) := inferInstance
    exact u.ne_zero hxu
  refine ⟨Units.mk0 x hx, ?_⟩
  convert hu using 1
  ext
  simp [hxu]

end GlobalTheory.UnitsDense
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_unit_mem_open_archimedean_units : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (V : Set (Cinf E)ˣ), IsOpen V → V.Nonempty → ∃ α : Eˣ, Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom α ∈ V := by
  atlas_forward_decl GlobalTheory.UnitsDense.exists_unit_mem_open
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW.KirSemi

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem gl_af_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ w, GeneralLinearGroup.map (pLoc E w) g = GeneralLinearGroup.map (pLoc E w) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w => ?_))
  exact congrArg (fun x : GL (Fin a) (w.adicCompletion E) => x.1 i j) (H w)

theorem map_loc_fin (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) =
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g := by
  ext; rfl

theorem comm_of_supp (S : Finset (HeightOneSpectrum (𝓞 E))) {s t : GA E a} (hs : s ∈ supS E a S)
    (h1 : GeneralLinearGroup.map (pInf E) t = 1)
    (h2 : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) : s * t = t * s := by
  apply ga_ext
  · simp [map_mul, h1]
  · apply gl_af_ext
    intro w
    simp only [map_mul, map_loc_fin]
    by_cases hw : w ∈ S
    · rw [h2 w hw]; simp
    · rw [hs w hw]; simp

theorem supS_mul (S : Finset (HeightOneSpectrum (𝓞 E))) {x y : GA E a} (hx : x ∈ supS E a S)
    (hy : y ∈ supS E a S) : x * y ∈ supS E a S := by
  intro w hw
  rw [map_mul, hx w hw, hy w hw, one_mul]

theorem whit_rt (F : GA E a → ℂ) (h g : GA E a) : whit (fun y => F (y * h)) g = whit F (g * h) := by
  simp only [whit, GroundTheory.Automorphic.FourierWhittaker.whittaker, mul_assoc]

theorem ratGL_scalar_val (α : Eˣ) :
    ((ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) : GA E a) :
      Matrix (Fin a) (Fin a) (Ad E)) = Matrix.scalar (Fin a) (algebraMap E (Ad E) (α : E)) := by
  ext i j
  by_cases h : i = j <;> simp [ratGL, Matrix.scalar_apply, Matrix.diagonal_apply, h]

theorem aut_central {φ : Sm E a} (hφ : IsAutForm φ) (α : Eˣ) (g : GA E a) :
    φ.1 (g * ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α)) = φ.1 g := by
  have hc : g * ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) =
      ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) * g := by
    apply Units.ext
    simp only [Units.val_mul, ratGL_scalar_val]
    exact ((Matrix.scalar_commute _ (fun r => Commute.all _ r) _)).symm
  rw [hc, hφ.left]

theorem exists_mirabolic_nonzero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ ψ ∈ π.V, (∃ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit ψ.1 p ≠ 0) ∧ (∀ k : GA E (m + 1), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, φ.1 (g * k) = φ.1 g) → ∀ g, ψ.1 (g * k) = ψ.1 g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit ψ.1 (x * t) = c * GlobalTheory.JSW.whit ψ.1 x := by
  intro E _ _ _ m S π φ hφ ⟨x, hxS, hx⟩
  have haut : IsAutForm φ := (π.cusp φ hφ).1
  set xf := GeneralLinearGroup.map (pFin E) x with hxf
  obtain ⟨p0, ρ, k, hp0, hy⟩ := GlobalTheory.T.exists_mirabolic_scalar_unitary_decomposition_archimedean E m (GeneralLinearGroup.map (pInf E) x)
  let sc : (Cinf E)ˣ →* GL (Fin (m + 1)) (Cinf E) :=
    Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom
  have hsc : Continuous sc := by
    apply Continuous.units_map
    show Continuous (fun c : Cinf E => Matrix.scalar (Fin (m + 1)) c)
    simp only [Matrix.scalar_apply]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  let ζ : (Cinf E)ˣ → ℂ := fun c =>
    whit φ.1 (infGL E (m + 1) p0 * infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf)
  have hζc : Continuous ζ :=
    (GlobalTheory.T.continuous_globalWhittakerCoefficient_archimedean E (m + 1) φ haut _ _).comp (hsc.mul continuous_const)
  have hζρ : ζ ρ ≠ 0 := by
    have hx' : infGL E (m + 1) p0 * infGL E (m + 1) (sc ρ * Unitary.toUnits k) * finGL E (m + 1) xf = x := by
      rw [← map_mul, ← mul_assoc]
      rw [show p0 * sc ρ * Unitary.toUnits k = GeneralLinearGroup.map (pInf E) x from hy.symm]
      exact infGL_mul_finGL x
    show whit φ.1 _ ≠ 0
    rw [hx']
    exact hx
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_field_unit_mem_open_archimedean_units E {c | ζ c ≠ 0} (isOpen_ne_fun hζc continuous_const) ⟨ρ, hζρ⟩
  set c := Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β with hc
  let zE : GL (Fin (m + 1)) E := Units.map (Matrix.scalar (Fin (m + 1)) : E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) E).toMonoidHom β⁻¹
  set s := infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf with hs
  have hcen : ∀ g : GL (Fin (m + 1)) (Cinf E), sc c * g = g * sc c := by
    intro g
    apply Units.ext
    exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _
  have hzinf : GeneralLinearGroup.map (pInf E) (ratGL E (m + 1) zE) = (sc c)⁻¹ := by
    have hci : (sc c)⁻¹ = sc (Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β⁻¹) := by
      simp only [hc, map_inv]
    rw [hci]
    apply Units.ext
    show ((ratGL E (m + 1) zE : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map (pInf E) =
      Matrix.scalar (Fin (m + 1)) (((Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β⁻¹ : (Cinf E)ˣ)) : Cinf E)
    rw [ratGL_scalar_val]
    simp [Matrix.scalar_apply, Matrix.diagonal_map]
    funext v
    simp [pInf_algebraMap, map_inv₀]
  set z := GeneralLinearGroup.map (pFin E) (ratGL E (m + 1) zE) with hz
  have hsz : s * ratGL E (m + 1) zE = infGL E (m + 1) (Unitary.toUnits k) * finGL E (m + 1) (xf * z) := by
    apply ga_ext
    · simp only [hs, map_mul, pInf_infGL, hzinf]
      simp
      rw [hcen]; group
    · simp [hs, hz, mul_assoc]
  let ψ : Sm E (m + 1) := act (Op.cpt k) (act (Op.fin (xf * z)) φ)
  have hψV : ψ ∈ π.V := π.stable _ _ (π.stable _ _ hφ)
  have hψ : ∀ g, ψ.1 g = φ.1 (g * s) := by
    intro g
    have h0 : ψ.1 g = φ.1 (g * infGL E (m + 1) (Unitary.toUnits k) * finGL E (m + 1) (xf * z)) := rfl
    rw [h0, mul_assoc, ← hsz, ← mul_assoc, aut_central haut β⁻¹]
  have hψf : ψ.1 = fun g => φ.1 (g * s) := funext hψ
  have hsS : s ∈ supS E (m + 1) S := by
    intro w hw
    rw [← map_loc_fin, hs, map_mul, pFin_infGL, pFin_finGL, one_mul, hxf, map_loc_fin]
    exact hxS w hw
  refine ⟨ψ, hψV, ⟨infGL E (m + 1) p0, ⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro w hw
    rw [← map_loc_fin]
    simp
  · intro j
    have h1 : pInf E (((infGL E (m + 1) p0 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) =
        (p0 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j :=
      congrArg (fun y : GL (Fin (m + 1)) (Cinf E) => (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j)
        (pInf_infGL (E := E) p0)
    have h2 : pFin E (((infGL E (m + 1) p0 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) =
        ((1 : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j :=
      congrArg (fun y : GL (Fin (m + 1)) (Af E) => (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j)
        (pFin_infGL (E := E) p0)
    rw [hp0 j] at h1
    apply ad_ext
    · rw [h1]; split_ifs <;> simp
    · rw [h2]; split_ifs with h <;> simp [Matrix.one_apply, h, eq_comm]
  · rw [hψf, whit_rt]
    have : infGL E (m + 1) p0 * s = infGL E (m + 1) p0 * infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf := by
      rw [hs, mul_assoc]
    rw [this]
    exact hβ
  · intro k' h1 h2 hk g
    rw [hψ, hψ, mul_assoc, ← comm_of_supp S hsS h1 h2, ← mul_assoc, hk]
  · intro t c' h1 h2 hrel y hy
    rw [hψf, whit_rt, whit_rt, mul_assoc, ← comm_of_supp S hsS h1 h2, ← mul_assoc]
    exact hrel (y * s) (supS_mul S hy hsS)

theorem kirillov_semilocal_bump : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ t : GA E (m + 1), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ g, φ.1 (g * t) = φ.1 g) → ∀ g, F (g * t) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  intro E _ _ _ m S b hb hC hU hsm π φ hφ hx
  obtain ⟨ψ, hψ, hp, hk, hrel⟩ := exists_mirabolic_nonzero E m S π φ hφ hx
  obtain ⟨F, hF, hFb, hFU, hFk, hFrel⟩ := GlobalTheory.T.kirillov_semilocal_mirabolic_whittaker E m S b hb hC hU hsm π ψ hψ hp
  exact ⟨F, hF, hFb, hFU, fun k h1 h2 h3 => hFk k h1 h2 (hk k h1 h2 h3),
    fun t c h1 h2 h3 => hFrel t c h1 h2 (hrel t c h1 h2 h3)⟩

end GlobalTheory.JSW.KirSemi
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kirillov_semilocal_smooth_bump : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ t : GA E (m + 1), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ g, φ.1 (g * t) = φ.1 g) → ∀ g, F (g * t) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  first | (exact @GlobalTheory.JSW.KirSemi.kirillov_semilocal_bump) | (exact GlobalTheory.JSW.KirSemi.kirillov_semilocal_bump) | (intros; apply GlobalTheory.JSW.KirSemi.kirillov_semilocal_bump  <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW.BumpShintani

theorem map_comp_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := by
  ext i j; rfl

theorem pInf_tl {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) :
    GeneralLinearGroup.map (pInf E) (GlobalTheory.JSW.tl ϖ l) = 1 := by
  unfold GlobalTheory.JSW.tl
  rw [map_list_prod]
  apply List.prod_eq_one
  intro x hx
  simp only [List.map_map, List.mem_map] at hx
  obtain ⟨w, _, rfl⟩ := hx
  simp

theorem loc_tl {E : Type} [Field E] [NumberField E] {a : ℕ} (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) (v : HeightOneSpectrum (𝓞 E)) (hv : v ∉ l.support) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l) = 1 := by
  unfold GlobalTheory.JSW.tl
  rw [map_list_prod]
  apply List.prod_eq_one
  intro x hx
  simp only [List.map_map, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hne : v ≠ w := fun h => hv (h ▸ (Finset.mem_toList.1 hw))
  simp only [Function.comp_apply, map_comp_eq, pFin_finGL]
  exact pLoc_locGL_of_ne hne _

theorem exists_bump_shintani : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) ∧ ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) ∧ ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit F (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w) := by
  intro E _ _ _ m S hcond
  obtain ⟨b, hb1, hbN, hbC, hbU, hbS⟩ := GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic E m S
  refine ⟨b, hb1, hbN, hbC, ?_⟩
  intro π α hSat
  obtain ⟨φ, hφV, hφK, hφx⟩ := GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero E m S hcond π α hSat
  obtain ⟨F, hFV, hFb, hFU, hFinv, hFeig⟩ := GlobalTheory.T.kirillov_semilocal_smooth_bump E m S b hbN hbC hbU hbS π φ hφV hφx
  refine ⟨F, hFV, hFU, ?_, ?_⟩
  · intro w hw k hk g
    refine hFinv _ (pInf_finGL _) ?_ ?_ g
    · intro w' hw'
      have hne : w' ≠ w := fun h => hw (h ▸ hw')
      rw [map_comp_eq, pFin_finGL]
      exact pLoc_locGL_of_ne hne _
    · intro g'
      exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 g') (hφK w hw k hk)
  · intro ϖ hϖ l hl p hp
    have hC := GlobalTheory.T.whittaker_mul_torus_iterated_factorisation E (m + 1) S hcond π α hSat φ hφV hφK ϖ hϖ l hl
    have hS : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l) = 1 :=
      fun w hw => loc_tl ϖ l w (fun h => hl w h hw)
    rw [hFeig _ _ (pInf_tl ϖ l) hS hC p hp.1, hFb p hp, mul_comm]

end GlobalTheory.JSW.BumpShintani
end
