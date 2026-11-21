import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCompactificationInteriorPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptIsoCompareStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeCptFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HodgeCompactPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeHostAutPermutation
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeCptCompare
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.JNormal
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

section
open GlobalTheory.CompanionTheory.Ar Matrix

namespace PositivityTheory.UnitarySelfGeneration.GF

variable {r : ℕ}

def trunc {R : Type} [CommRing R] (k : Fin r) (A : Matrix (Fin r) (Fin r) R) : Matrix (Fin r) (Fin r) R :=
  Matrix.of fun i j => if i ≤ k ∧ j ≤ k then A i j else if i = j then 1 else 0

def Uni {R : Type} [CommRing R] (L : Matrix (Fin r) (Fin r) R) : Prop :=
  (∀ k, L k k = 1) ∧ ∀ l k, l < k → L l k = 0

def Up {R : Type} [CommRing R] (C : Matrix (Fin r) (Fin r) R) : Prop := ∀ l k, k < l → C l k = 0

section Ring

variable {R R' : Type} [CommRing R] [CommRing R']

theorem trunc_map (φ : R →+* R') (k : Fin r) (A : Matrix (Fin r) (Fin r) R) :
    trunc k (A.map φ) = (trunc k A).map φ := by
  ext i j
  simp only [trunc, of_apply, map_apply]
  split_ifs <;> simp

theorem det_trunc_map (φ : R →+* R') (k : Fin r) (A : Matrix (Fin r) (Fin r) R) :
    (trunc k (A.map φ)).det = φ (trunc k A).det := by
  rw [trunc_map, RingHom.map_det, RingHom.mapMatrix_apply]

theorem Uni.map {L : Matrix (Fin r) (Fin r) R} (h : Uni L) (φ : R →+* R') : Uni (L.map φ) :=
  ⟨fun k => by simp [h.1], fun l k hlk => by simp [h.2 l k hlk]⟩

theorem Up.map {L : Matrix (Fin r) (Fin r) R} (h : Up L) (φ : R →+* R') : Up (L.map φ) :=
  fun l k hlk => by simp [h l k hlk]

theorem Uni.det {L : Matrix (Fin r) (Fin r) R} (h : Uni L) : L.det = 1 := by
  rw [det_of_isLowerTriangular L (fun i j hij => h.2 i j hij)]
  simp [h.1]

theorem Uni.trunc {L : Matrix (Fin r) (Fin r) R} (h : Uni L) (k : Fin r) : Uni (trunc k L) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp [GF.trunc, h.1]
  · simp [GF.trunc, h.2 i j hij, hij.ne]

theorem uni_one : Uni (1 : Matrix (Fin r) (Fin r) R) :=
  ⟨fun k => by simp, fun l k h => by simp [h.ne]⟩

theorem trunc_mul (k : Fin r) (A C : Matrix (Fin r) (Fin r) R) (hC : Up C) :
    trunc k (A * C) = trunc k A * trunc k C := by
  ext i j
  simp only [trunc, of_apply, mul_apply]
  by_cases hi : i ≤ k
  · by_cases hj : j ≤ k
    · simp only [hi, hj, and_self, if_true, true_and, and_true]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : l ≤ k
      · simp [hl]
      · have h1 : j < l := lt_of_le_of_lt hj (not_le.1 hl)
        simp [hl, hC l j h1, h1.ne']
    · have hij : i ≠ j := fun e => hj (e ▸ hi)
      simp only [hi, hj, and_false, if_false, true_and, hij]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hl : l = j
      · subst hl; simp [hj, hij]
      · simp [hl]
  · simp only [hi, false_and, if_false]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro l _ hl; simp [Ne.symm hl]
    · simp

theorem Up.mul {A B : Matrix (Fin r) (Fin r) R} (hA : Up A) (hB : Up B) : Up (A * B) := by
  have h : BlockTriangular (A * B) id :=
    BlockTriangular.mul (fun i j h => hA i j h) (fun i j h => hB i j h)
  exact fun i j hij => h hij

end Ring

variable {F F' : Type} [Field F] [Field F']

theorem Up.inv {A : Matrix (Fin r) (Fin r) F} (hA : Up A) (h0 : A.det ≠ 0) : Up A⁻¹ := by
  let _ := A.invertibleOfIsUnitDet (IsUnit.mk0 _ h0)
  have h : BlockTriangular A⁻¹ id := blockTriangular_inv_of_blockTriangular (fun i j h => hA i j h)
  exact fun i j hij => h hij

theorem exists_lu (A : Matrix (Fin r) (Fin r) F) (h : ∀ k, (trunc k A).det ≠ 0) :
    ∃ C, Up C ∧ Uni (A * C) := by
  have hx : ∀ k, ∃ x : Fin r → F, trunc k A *ᵥ x = Pi.single k 1 := fun k =>
    ⟨(trunc k A)⁻¹ *ᵥ Pi.single k 1, by
      rw [mulVec_mulVec, mul_nonsing_inv _ (IsUnit.mk0 _ (h k)), one_mulVec]⟩
  choose x hx using hx
  have hup : ∀ l k, k < l → x k l = 0 := by
    intro l k hkl
    have := congrFun (hx k) l
    simp only [mulVec, dotProduct, trunc, of_apply, not_le.2 hkl, false_and, if_false] at this
    rw [Finset.sum_eq_single l] at this
    · simpa [hkl.ne'] using this
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have key : ∀ l k, l ≤ k → (A * Matrix.of fun l k => x k l) l k = (Pi.single k 1 : Fin r → F) l := by
    intro l k hlk
    rw [← congrFun (hx k) l]
    simp only [mul_apply, mulVec, dotProduct, trunc, of_apply, hlk, true_and]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ≤ k
    · simp [hb]
    · simp [hup b k (not_le.1 hb)]
  refine ⟨Matrix.of fun l k => x k l, hup, fun k => ?_, fun l k hlk => ?_⟩
  · rw [key k k le_rfl]; simp
  · rw [key l k hlk.le]; simp [hlk.ne]

theorem dets_of_lu {A C : Matrix (Fin r) (Fin r) F} (hC : Up C) (h : Uni (A * C)) :
    A.det ≠ 0 ∧ C.det ≠ 0 ∧ ∀ k, (trunc k A).det ≠ 0 ∧ (trunc k C).det ≠ 0 := by
  have h1 := h.det
  rw [det_mul] at h1
  refine ⟨left_ne_zero_of_mul_eq_one h1, right_ne_zero_of_mul_eq_one h1, fun k => ?_⟩
  have h2 := (h.trunc k).det
  rw [trunc_mul k A C hC, det_mul] at h2
  exact ⟨left_ne_zero_of_mul_eq_one h2, right_ne_zero_of_mul_eq_one h2⟩

theorem uni_mul_up {L W : Matrix (Fin r) (Fin r) F} (hL : Uni L) (hW : Up W) (h : Uni (L * W)) : W = 1 := by
  have hL0 : L.det ≠ 0 := by rw [hL.det]; exact one_ne_zero
  have h1 : Up (Lᵀ) := fun i j hij => hL.2 j i hij
  have h2 : Up ((L * W)ᵀ) := fun i j hij => h.2 j i hij
  have h3 : Up ((L * W)ᵀ * (Lᵀ)⁻¹) := h2.mul (h1.inv (by rwa [det_transpose]))
  rw [transpose_mul, Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ (by rwa [det_transpose])),
    Matrix.mul_one] at h3
  have hoff : ∀ i j, i ≠ j → W i j = 0 := fun i j hij =>
    (lt_or_gt_of_ne hij).elim (fun h => h3 j i h) (fun h => hW i j h)
  ext i j
  by_cases hij : i = j
  · subst hij
    have := h.1 i
    rw [mul_apply, Finset.sum_eq_single i] at this
    · simpa [hL.1] using this
    · intro b _ hb; simp [hoff b i hb]
    · simp
  · rw [hoff i j hij, one_apply_ne hij]

theorem lu_unique {A C C' : Matrix (Fin r) (Fin r) F} (hC : Up C) (h : Uni (A * C)) (hC' : Up C')
    (h' : Uni (A * C')) : A * C = A * C' := by
  have h0 := (dets_of_lu hC h).2.1
  have e : A * C' = A * C * (C⁻¹ * C') := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, mul_nonsing_inv _ (IsUnit.mk0 _ h0), Matrix.one_mul]
  have := uni_mul_up h ((hC.inv h0).mul hC') (e ▸ h')
  rw [e, this, Matrix.mul_one]

theorem lu_mem (K : Subfield F) {A C : Matrix (Fin r) (Fin r) F} (hC : Up C) (h : Uni (A * C))
    (hA : ∀ i j, A i j ∈ K) : ∀ i j, (A * C) i j ∈ K := by
  let A₀ : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have e : A₀.map K.subtype = A := rfl
  obtain ⟨C₀, h1, h2⟩ := exists_lu A₀ fun k h0 => ((dets_of_lu hC h).2.2 k).1 (by
    rw [← e, det_trunc_map, h0, map_zero])
  have h3 := h2.map K.subtype
  have e2 : (A₀ * C₀).map K.subtype = A * C₀.map K.subtype := by rw [Matrix.map_mul, e]
  rw [e2] at h3
  rw [lu_unique hC h (h1.map K.subtype) h3, ← e2]
  exact fun i j => ((A₀ * C₀) i j).2

theorem exists_general (g : Matrix (Fin r) (Fin r) F) (hg : g.det ≠ 0) :
    ∃ w : Matrix (Fin r) (Fin r) (RatFunc F), Uni w ∧
      ∀ k, (trunc k (g.map (algebraMap F (RatFunc F)) * w)).det ≠ 0 := by
  let N : Matrix (Fin r) (Fin r) (Polynomial F) :=
    (Polynomial.X : Polynomial F) • 1 + (1 - Polynomial.X : Polynomial F) • (g⁻¹).map Polynomial.C
  let φ := algebraMap (Polynomial F) (RatFunc F)
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have e1 : N.map (Polynomial.evalRingHom (1 : F)) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [N, h, one_apply]
  have e0 : (g.map Polynomial.C * N).map (Polynomial.evalRingHom (0 : F)) = 1 := by
    rw [Matrix.map_mul, ← mul_nonsing_inv g (IsUnit.mk0 _ hg)]
    congr 1
    · ext i j; simp
    · ext i j
      by_cases h : i = j <;> simp [N, h, one_apply]
  have nz : ∀ (M : Matrix (Fin r) (Fin r) (Polynomial F)) (a : F), M.map (Polynomial.evalRingHom a) = 1 →
      ∀ k, (trunc k (M.map φ)).det ≠ 0 := by
    intro M a hM k h0
    rw [det_trunc_map, map_eq_zero_iff _ hφ] at h0
    have := det_trunc_map (Polynomial.evalRingHom a) k M
    rw [hM, h0, map_zero, (uni_one.trunc k).det] at this
    exact one_ne_zero this
  obtain ⟨C, hC, hU⟩ := exists_lu (N.map φ) (nz N 1 e1)
  refine ⟨_, hU, fun k => ?_⟩
  have e : g.map (algebraMap F (RatFunc F)) * N.map φ = (g.map Polynomial.C * N).map φ := by
    rw [Matrix.map_mul, Matrix.map_map]
    rfl
  rw [← Matrix.mul_assoc, trunc_mul _ _ _ hC, det_mul, e]
  exact mul_ne_zero (nz _ 0 e0 k) ((dets_of_lu hC hU).2.2 k).2

def fl (M : Matrix (Fin r) (Fin r) F) (i : ℕ) : Submodule F (Fin r → F) := flagStep F (fun k l => M l k) i

theorem fl_mul_le (M C : Matrix (Fin r) (Fin r) F) (hC : Up C) (i : ℕ) : fl (M * C) i ≤ fl M i := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have : (fun l => (M * C) l k) = ∑ b, C b k • fun l => M l b := by
    funext l
    simp [mul_apply, Finset.sum_apply, mul_comm]
  simp only [this]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : k < b
  · rw [hC b k hb, zero_smul]; exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ?_, rfl⟩)
    exact lt_of_le_of_lt (Fin.le_def.1 (not_lt.1 hb)) hk

theorem fl_mul (M C : Matrix (Fin r) (Fin r) F) (hC : Up C) (h0 : C.det ≠ 0) (i : ℕ) : fl (M * C) i = fl M i := by
  refine le_antisymm (fl_mul_le M C hC i) ?_
  have := fl_mul_le (M * C) C⁻¹ (hC.inv h0) i
  rwa [Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ h0), Matrix.mul_one] at this

theorem flagStep_map {E E' : Type} [AddCommGroup E] [Module F E] [AddCommGroup E'] [Module F E'] (f : E →ₗ[F] E')
    (b : Fin r → E) (i : ℕ) : (flagStep F b i).map f = flagStep F (fun k => f (b k)) i := by
  unfold flagStep
  rw [Submodule.map_span, Set.image_image]

theorem fl_of_indep {E : Type} [AddCommGroup E] [Module F E] {e : Fin r → E} (he : LinearIndependent F e)
    {M N : Matrix (Fin r) (Fin r) F} {i : ℕ}
    (h : flagStep F (fun k => ∑ l, M l k • e l) i = flagStep F (fun k => ∑ l, N l k • e l) i) : fl M i = fl N i := by
  apply Submodule.map_injective_of_injective (f := Fintype.linearCombination F e)
    (he.fintypeLinearCombination_injective)
  unfold fl
  rw [flagStep_map, flagStep_map]
  simpa only [Fintype.linearCombination_apply] using h

end PositivityTheory.UnitarySelfGeneration.GF
end

section
open GlobalTheory.CompanionTheory.Ar Matrix

namespace PositivityTheory.UnitarySelfGeneration.GF

variable {S : Type} {r : S → ℕ} {Ω : Type} [Field Ω]

abbrev Idx (r : S → ℕ) : Type := Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1}

abbrev ent {F : Type} (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F) : Idx r → F := fun q => u q.1 q.2.1.1 q.2.1.2

noncomputable def gen (Ω : Type) [Field Ω] (r : S → ℕ) (σ : S) :
    Matrix (Fin (r σ)) (Fin (r σ)) (MvPolynomial (Idx r) Ω) :=
  Matrix.of fun l k => if h : k < l then MvPolynomial.X ⟨σ, ⟨(l, k), h⟩⟩ else if l = k then 1 else 0

theorem gen_map {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (σ : S) :
    (gen Ω r σ).map (MvPolynomial.aeval (R := Ω) (ent u)).toRingHom = u σ := by
  ext l k
  simp only [gen, map_apply, of_apply]
  split_ifs with h1 h2
  · simp [ent]
  · subst h2; simp [(hu σ).1]
  · simp [(hu σ).2 l k (lt_of_le_of_ne (not_lt.1 h1) h2)]

theorem general_of_indep {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (hi : AlgebraicIndependent Ω (ent u)) (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω)
    (hg : ∀ σ, (g σ).det ≠ 0) (σ : S) (k : Fin (r σ)) :
    (trunc k ((g σ).map (algebraMap Ω F) * u σ)).det ≠ 0 := by
  choose w hw hw' using fun σ => exists_general (g σ) (hg σ)
  have key : ∀ (F : Type) [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F),
      (∀ σ, Uni (u σ)) → (trunc k ((g σ).map (algebraMap Ω F) * u σ)).det =
        MvPolynomial.aeval (R := Ω) (ent u) (trunc k ((g σ).map MvPolynomial.C * gen Ω r σ)).det := by
    intro F _ _ u hu
    have := det_trunc_map (MvPolynomial.aeval (R := Ω) (ent u)).toRingHom k ((g σ).map MvPolynomial.C * gen Ω r σ)
    rw [Matrix.map_mul, gen_map u hu σ, Matrix.map_map] at this
    have e : (⇑(MvPolynomial.aeval (R := Ω) (ent u)).toRingHom ∘ ⇑MvPolynomial.C) = algebraMap Ω F := by
      funext a
      simp
    rw [e] at this
    exact this
  intro h0
  rw [key F u hu, map_eq_zero_iff _ hi] at h0
  exact hw' σ k (by rw [key _ w hw, h0, map_zero])

theorem mem_adjoin_ent {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (σ : S) (l k : Fin (r σ)) : u σ l k ∈ IntermediateField.adjoin Ω (Set.range (ent u)) := by
  rcases lt_trichotomy l k with h | h | h
  · rw [(hu σ).2 l k h]; exact zero_mem _
  · rw [h, (hu σ).1]; exact one_mem _
  · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l, k), h⟩⟩, rfl⟩

theorem adjoin_all {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) :
    IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω (Set.range (ent u)) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    exact mem_adjoin_ent u hu _ _ _
  · apply IntermediateField.adjoin.mono
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨q.1, q.2.1⟩, rfl⟩

theorem adjoin_le {F : Type} [Field F] [Algebra Ω F] (u u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (hu' : ∀ σ, Uni (u' σ)) (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω)
    (C : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F) (hC : ∀ σ, Up (C σ))
    (e : ∀ σ, u' σ = (g σ).map (algebraMap Ω F) * u σ * C σ) :
    IntermediateField.adjoin Ω (Set.range (ent u')) ≤ IntermediateField.adjoin Ω (Set.range (ent u)) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨q, rfl⟩
  have := lu_mem (IntermediateField.adjoin Ω (Set.range (ent u))).toSubfield (hC q.1) (e q.1 ▸ hu' q.1)
    (fun i j => by
      rw [mul_apply]
      exact sum_mem fun l _ => mul_mem (IntermediateField.algebraMap_mem _ _) (mem_adjoin_ent u hu _ _ _))
  rw [← e q.1] at this
  exact this _ _

theorem change [Finite S] {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (hi : AlgebraicIndependent Ω (ent u))
    (hf : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (ent u))) F)
    (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω) (hg : ∀ σ, (g σ).det ≠ 0) :
    ∃ u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F, (∀ σ, Uni (u' σ)) ∧ AlgebraicIndependent Ω (ent u') ∧
      IntermediateField.adjoin Ω (Set.range (ent u')) = IntermediateField.adjoin Ω (Set.range (ent u)) ∧
      ∀ σ i, fl (u' σ) i = fl ((g σ).map (algebraMap Ω F) * u σ) i := by
  choose C hC hU using fun σ => exists_lu _ (general_of_indep u hu hi g hg σ)
  have hC0 := fun σ => (dets_of_lu (hC σ) (hU σ)).2.1
  let u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F := fun σ => (g σ).map (algebraMap Ω F) * u σ * C σ
  have heq : IntermediateField.adjoin Ω (Set.range (ent u')) = IntermediateField.adjoin Ω (Set.range (ent u)) := by
    refine le_antisymm (adjoin_le u u' hu hU g C hC fun _ => rfl)
      (adjoin_le u' u hU hu (fun σ => (g σ)⁻¹) (fun σ => (C σ)⁻¹) (fun σ => (hC σ).inv (hC0 σ)) fun σ => ?_)
    simp only [u']
    rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ (hC0 σ)), Matrix.mul_one,
      ← Matrix.mul_assoc, ← Matrix.map_mul, nonsing_inv_mul _ (IsUnit.mk0 _ (hg σ)),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  refine ⟨u', hU, ?_, heq, fun σ i => fl_mul _ _ (hC σ) (hC0 σ) i⟩
  have a1 : Algebra.IsAlgebraic (IntermediateField.adjoin Ω (Set.range (ent u))) F := inferInstance
  have a2 : Algebra.IsAlgebraic (IntermediateField.adjoin Ω (Set.range (ent u'))) F := by rw [heq]; exact a1
  rw [IntermediateField.isAlgebraic_adjoin_iff_top] at a1 a2
  have b1 := hi.isTranscendenceBasis_iff_isAlgebraic.2 a1
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω (ent u') b1.cardinalMk_eq_trdeg.le).1

theorem compositum (K Ω₁ Ω₂ : Type) [Field K] [Field Ω₁] [Field Ω₂] [Algebra K Ω₁] [Algebra K Ω₂]
    [FiniteDimensional K Ω₁] [FiniteDimensional K Ω₂] :
    ∃ (Ω₃ : Type) (_ : Field Ω₃) (i₁ : Ω₁ →+* Ω₃) (i₂ : Ω₂ →+* Ω₃),
      (∀ x, i₁ (algebraMap K Ω₁ x) = i₂ (algebraMap K Ω₂ x)) ∧
      ∃ n₁ n₂ : ℕ, 0 < n₁ ∧ n₁ * Module.finrank K Ω₁ = n₂ * Module.finrank K Ω₂ ∧
        Module.finrank i₁.fieldRange Ω₃ = n₁ ∧ Module.finrank i₂.fieldRange Ω₃ = n₂ := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct K Ω₁ Ω₂)
  let Ω₃ := TensorProduct K Ω₁ Ω₂ ⧸ M
  let _ : Field Ω₃ := Ideal.Quotient.field M
  have fin : FiniteDimensional K Ω₃ :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)
  let j₁ : Ω₁ →ₐ[K] Ω₃ := (Ideal.Quotient.mkₐ K M).comp Algebra.TensorProduct.includeLeft
  let j₂ : Ω₂ →ₐ[K] Ω₃ := (Ideal.Quotient.mkₐ K M).comp Algebra.TensorProduct.includeRight
  have e₁ := Module.finrank_mul_finrank K j₁.fieldRange Ω₃
  have e₂ := Module.finrank_mul_finrank K j₂.fieldRange Ω₃
  have q₁ : Module.finrank K Ω₁ = Module.finrank K j₁.fieldRange :=
    (AlgEquiv.ofInjectiveField j₁).toLinearEquiv.finrank_eq
  have q₂ : Module.finrank K Ω₂ = Module.finrank K j₂.fieldRange :=
    (AlgEquiv.ofInjectiveField j₂).toLinearEquiv.finrank_eq
  rw [← q₁] at e₁
  rw [← q₂] at e₂
  refine ⟨Ω₃, inferInstance, j₁.toRingHom, j₂.toRingHom, fun x => (j₁.commutes x).trans (j₂.commutes x).symm,
    Module.finrank j₁.fieldRange Ω₃, Module.finrank j₂.fieldRange Ω₃, Module.finrank_pos, ?_, rfl, rfl⟩
  rw [mul_comm, e₁, mul_comm, e₂]

theorem compositum' {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [Algebra Ω Ω₁] [Algebra Ω Ω₂] {I : Type}
    (x₁ : I → Ω₁) (x₂ : I → Ω₂) (h₁ : AlgebraicIndependent Ω x₁) (h₂ : AlgebraicIndependent Ω x₂)
    (f₁ : FiniteDimensional (IntermediateField.adjoin Ω (Set.range x₁)) Ω₁)
    (f₂ : FiniteDimensional (IntermediateField.adjoin Ω (Set.range x₂)) Ω₂) :
    ∃ (Ω₃ : Type) (_ : Field Ω₃) (i₁ : Ω₁ →+* Ω₃) (i₂ : Ω₂ →+* Ω₃),
      (∀ a, i₁ (algebraMap Ω Ω₁ a) = i₂ (algebraMap Ω Ω₂ a)) ∧ (∀ q, i₁ (x₁ q) = i₂ (x₂ q)) ∧
      ∃ n₁ n₂ : ℕ, 0 < n₁ ∧ n₁ * Module.finrank (IntermediateField.adjoin Ω (Set.range x₁)) Ω₁ =
          n₂ * Module.finrank (IntermediateField.adjoin Ω (Set.range x₂)) Ω₂ ∧
        Module.finrank i₁.fieldRange Ω₃ = n₁ ∧ Module.finrank i₂.fieldRange Ω₃ = n₂ := by
  let K₁ := IntermediateField.adjoin Ω (Set.range x₁)
  let K₂ := IntermediateField.adjoin Ω (Set.range x₂)
  let e : K₁ ≃ₐ[Ω] K₂ := h₁.aevalEquivField.symm.trans h₂.aevalEquivField
  let _ : Algebra K₁ Ω₂ := ((algebraMap K₂ Ω₂).comp e.toRingEquiv.toRingHom).toAlgebra
  have hr : Module.finrank K₁ Ω₂ = Module.finrank K₂ Ω₂ :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl _) rfl
  have : FiniteDimensional K₁ Ω₂ := Module.finite_of_finrank_pos (by rw [hr]; exact Module.finrank_pos)
  obtain ⟨Ω₃, _, i₁, i₂, h, n₁, n₂, hn, e', e₁, e₂⟩ := compositum K₁ Ω₁ Ω₂
  refine ⟨Ω₃, inferInstance, i₁, i₂, fun a => ?_, fun q => ?_, n₁, n₂, hn, hr ▸ e', e₁, e₂⟩
  · refine (h (algebraMap Ω K₁ a)).trans ?_
    congr 1
    change ((e (algebraMap Ω K₁ a) : K₂) : Ω₂) = _
    rw [e.commutes]
    rfl
  · have := h (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)))
    change i₁ (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) : Ω₁) =
      i₂ (e (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))) : Ω₂) at this
    simp only [e, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] at this
    rw [h₁.aevalEquivField_algebraMap_apply_coe, h₂.aevalEquivField_algebraMap_apply_coe] at this
    simpa using this

theorem fl_coord {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E']
    [Module Ω' E'] (j : E →+ E') (hj : ∀ (a : Ω) e, j (a • e) = algebraMap Ω Ω' a • j e) {n : ℕ} {c c' : Fin n → E}
    (hc' : LinearIndependent Ω' fun k => j (c' k)) {h : Matrix (Fin n) (Fin n) Ω} (hh : ∀ k, c k = ∑ l, h l k • c' l)
    {b : Fin n → E'} {m u : Matrix (Fin n) (Fin n) Ω'} (hb : ∀ k, b k = ∑ l, m l k • j (c l)) {i : ℕ}
    (hf : flagStep Ω' b i = flagStep Ω' (fun k => ∑ l, u l k • j (c' l)) i) :
    fl (h.map (algebraMap Ω Ω') * m) i = fl u i := by
  refine fl_of_indep hc' ?_
  rw [← hf]
  congr 1
  funext k
  simp only [hb, hh, map_sum, hj, Finset.smul_sum, smul_smul, mul_apply, map_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

end PositivityTheory.UnitarySelfGeneration.GF
end

section
open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

namespace PositivityTheory.UnitarySelfGeneration

private theorem l_genflag_lemma_0 {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {n : ℕ}
    (c'' c' c : Fin n → E) {A B : Matrix (Fin n) (Fin n) Ω} (hA : ∀ k, c'' k = ∑ l, A l k • c' l)
    (hB : ∀ k, c' k = ∑ l, B l k • c l) : ∀ k, c'' k = ∑ p, (B * A) p k • c p := by
  intro k
  rw [hA k]
  simp_rw [hB, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

private theorem l_genflag_lemma {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {n : ℕ}
    (c c' : Fin n → E) (hc : ∀ k, c k ∈ Submodule.span Ω (Set.range c')) :
    ∃ h : Matrix (Fin n) (Fin n) Ω, ∀ k, c k = ∑ l, h l k • c' l := by
  choose f hf using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hc k)
  exact ⟨Matrix.of fun l k => f k l, fun k => by simp only [Matrix.of_apply]; exact (hf k).symm⟩

private theorem l_genflag_lemma_2 {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {n : ℕ}
    (c c' : Fin n → E) (hc : LinearIndependent Ω c) {h P : Matrix (Fin n) (Fin n) Ω}
    (hh : ∀ k, c k = ∑ l, h l k • c' l) (hP : ∀ k, c' k = ∑ l, P l k • c l) : P * h = 1 := by
  have key := l_genflag_lemma_0 c c' c hh hP
  ext p k
  have := Fintype.linearIndependent_iff.1 hc (fun p => (P * h) p k - (1 : Matrix (Fin n) (Fin n) Ω) p k)
    (by simp [sub_smul, Finset.sum_sub_distrib, ← key k, Matrix.one_apply]) p
  exact sub_eq_zero.1 this

private theorem l_genflag_lemma_3 {F K : Type} [Field F] [Field K] (f : F →+* K) {n : ℕ} (S : Set (Fin n → F)) :
    Submodule.span K ((fun v l => f (v l)) '' (Submodule.span F S : Set (Fin n → F))) =
      Submodule.span K ((fun v l => f (v l)) '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe]
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      convert (Submodule.span K ((fun v l => f (v l)) '' S)).zero_mem using 1
      funext l
      simp
    | add x y _ _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1
      funext l
      simp
    | smul a x _ hx =>
      convert Submodule.smul_mem _ (f a) hx using 1
      funext l
      simp
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

private theorem l_genflag_lemma_4 {F K : Type} [Field F] [Field K] (f : F →+* K) {n : ℕ}
    {M M' : Matrix (Fin n) (Fin n) F} {t : ℕ} (h : GF.fl M t = GF.fl M' t) :
    GF.fl (M.map f) t = GF.fl (M'.map f) t := by
  have key : ∀ N : Matrix (Fin n) (Fin n) F, GF.fl (N.map f) t =
      Submodule.span K ((fun v l => f (v l)) '' (GF.fl N t : Set (Fin n → F))) := by
    intro N
    simp only [GF.fl, flagStep]
    rw [l_genflag_lemma_3, Set.image_image]
    rfl
  rw [key, key, h]

private theorem l_genflag_lemma_5 {F : Type} [Field F] {n : ℕ} (N : Matrix (Fin n) (Fin n) F)
    {M M' : Matrix (Fin n) (Fin n) F} {t : ℕ} (h : GF.fl M t = GF.fl M' t) :
    GF.fl (N * M) t = GF.fl (N * M') t := by
  have key : ∀ M : Matrix (Fin n) (Fin n) F, GF.fl (N * M) t = (GF.fl M t).map (Matrix.mulVecLin N) := by
    intro M
    simp only [GF.fl, flagStep, Submodule.map_span, Set.image_image]
    congr 2
  rw [key, key, h]

open GF in
theorem l_genflag : ∀ (Ω Ω₁ Ω₂ : Type) [Field Ω] [Field Ω₁] [Field Ω₂] [Algebra Ω Ω₁] [Algebra Ω Ω₂] (E E₁ E₂ : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω₁ E₁] [AddCommGroup E₂] [Module Ω₂ E₂] (j₁ : E →+ E₁) (j₂ : E →+ E₂) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (b₁ : ∀ s, Fin (r s) → E₁) (b₂ : ∀ s, Fin (r s) → E₂) (d₁ d₂ : ℕ), IsGenericFlag (Ω' := Ω₁) j₁ V b₁ d₁ → IsGenericFlag (Ω' := Ω₂) j₂ V b₂ d₂ → ∃ (Ω₃ : Type) (_ : Field Ω₃) (i₁ : Ω₁ →+* Ω₃) (i₂ : Ω₂ →+* Ω₃), i₁.comp (algebraMap Ω Ω₁) = i₂.comp (algebraMap Ω Ω₂) ∧ (∃ n₁ n₂ : ℕ, 0 < n₁ ∧ n₁ * d₁ = n₂ * d₂ ∧ Module.finrank i₁.fieldRange Ω₃ = n₁ ∧ Module.finrank i₂.fieldRange Ω₃ = n₂) ∧ ∀ s (c : Fin (r s) → E) (m₁ : Matrix (Fin (r s)) (Fin (r s)) Ω₁) (m₂ : Matrix (Fin (r s)) (Fin (r s)) Ω₂), LinearIndependent Ω c → Submodule.span Ω (Set.range c) = V s → (∀ k, b₁ s k = ∑ l, m₁ l k • j₁ (c l)) → (∀ k, b₂ s k = ∑ l, m₂ l k • j₂ (c l)) → ∀ i, flagStep Ω₃ (fun k l => i₁ (m₁ l k) : Fin (r s) → Fin (r s) → Ω₃) i = flagStep Ω₃ (fun k l => i₂ (m₂ l k) : Fin (r s) → Fin (r s) → Ω₃) i := by
  intro Ω Ω₁ Ω₂ _ _ _ _ _ E E₁ E₂ _ _ _ _ _ _ j₁ j₂ S _ r V b₁ b₂ d₁ d₂ hG1 hG2
  unfold IsGenericFlag at hG1 hG2
  obtain ⟨c1, u1, hc1, hj1, hjc1, -, hd1, hup1, hfl1, hai1, hdpos1, hrk1⟩ := hG1
  obtain ⟨c2, u2, hc2, hj2, hjc2, -, hd2, hup2, hfl2, hai2, hdpos2, hrk2⟩ := hG2
  have hU1 : ∀ σ, GF.Uni (u1 σ) := fun σ => ⟨hd1 σ, hup1 σ⟩
  have hU2 : ∀ σ, GF.Uni (u2 σ) := fun σ => ⟨hd2 σ, hup2 σ⟩
  rw [GF.adjoin_all u1 hU1] at hrk1
  rw [GF.adjoin_all u2 hU2] at hrk2
  have hfd1 : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u1))) Ω₁ :=
    Module.finite_of_finrank_pos (by rw [hrk1]; exact hdpos1)
  have hfd2 : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u2))) Ω₂ :=
    Module.finite_of_finrank_pos (by rw [hrk2]; exact hdpos2)
  have hA : ∀ σ, ∃ A : Matrix (Fin (r σ)) (Fin (r σ)) Ω,
      (∀ k, c2 σ k = ∑ l, A l k • c1 σ l) ∧ A.det ≠ 0 := by
    intro σ
    obtain ⟨A, hA⟩ := l_genflag_lemma (c2 σ) (c1 σ)
      (fun k => by rw [(hc1 σ).2, ← (hc2 σ).2]; exact Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨B, hB⟩ := l_genflag_lemma (c1 σ) (c2 σ)
      (fun k => by rw [(hc2 σ).2, ← (hc1 σ).2]; exact Submodule.subset_span ⟨k, rfl⟩)
    refine ⟨A, hA, fun h0 => ?_⟩
    have hBA := congrArg Matrix.det (l_genflag_lemma_2 (c2 σ) (c1 σ) (hc2 σ).1 hA hB)
    rw [Matrix.det_mul, Matrix.det_one, h0, mul_zero] at hBA
    exact zero_ne_one hBA
  choose A hAc hAdet using hA
  obtain ⟨u2', hU2', hai2', hadj, hfl2'⟩ := GF.change u2 hU2 hai2 hfd2 A hAdet
  have hfd2' : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u2'))) Ω₂ := by
    rw [hadj]; exact hfd2
  have hrk2' : Module.finrank (IntermediateField.adjoin Ω (Set.range (GF.ent u2'))) Ω₂ = d₂ := by
    rw [hadj]; exact hrk2
  obtain ⟨Ω₃, hF3, i₁, i₂, hα, hq, n₁, n₂, hn, hdeg, hr1, hr2⟩ :=
    GF.compositum' (GF.ent u1) (GF.ent u2') hai1 hai2' hfd1 hfd2'
  have hU : ∀ σ, (u1 σ).map i₁ = (u2' σ).map i₂ := by
    intro σ
    ext l k
    simp only [Matrix.map_apply]
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · exact hq ⟨σ, ⟨(l, k), hkl⟩⟩
    · rw [(hU1 σ).1 k, (hU2' σ).1 k, map_one, map_one]
    · rw [(hU1 σ).2 l k hlk, (hU2' σ).2 l k hlk, map_zero, map_zero]
  refine ⟨Ω₃, hF3, i₁, i₂, RingHom.ext hα, ⟨n₁, n₂, hn, ?_, hr1, hr2⟩, ?_⟩
  · rw [← hrk1, ← hrk2', hdeg]
  intro s c m₁ m₂ hc hspan hb1 hb2 i
  obtain ⟨h1, hh1⟩ := l_genflag_lemma c (c1 s)
    (fun k => by rw [(hc1 s).2, ← hspan]; exact Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨P1, hP1⟩ := l_genflag_lemma (c1 s) c
    (fun k => by rw [hspan, ← (hc1 s).2]; exact Submodule.subset_span ⟨k, rfl⟩)
  have hP2 : ∀ k, c2 s k = ∑ p, (P1 * A s) p k • c p := l_genflag_lemma_0 (c2 s) (c1 s) c (hAc s) hP1
  obtain ⟨h2, hh2⟩ := l_genflag_lemma c (c2 s)
    (fun k => by rw [(hc2 s).2, ← hspan]; exact Submodule.subset_span ⟨k, rfl⟩)
  have e1 : P1 * h1 = 1 := l_genflag_lemma_2 c (c1 s) hc hh1 hP1
  have e2 : (P1 * A s) * h2 = 1 := l_genflag_lemma_2 c (c2 s) hc hh2 hP2
  have f1 := GF.fl_coord j₁ hj1 (hjc1 s) hh1 hb1 (hfl1 s i)
  have f2 := GF.fl_coord j₂ hj2 (hjc2 s) hh2 hb2 (hfl2 s i)
  have g1 : GF.fl m₁ i = GF.fl (P1.map (algebraMap Ω Ω₁) * u1 s) i := by
    have := l_genflag_lemma_5 (P1.map (algebraMap Ω Ω₁)) f1
    rwa [← mul_assoc, ← Matrix.map_mul, e1, Matrix.map_one _ (map_zero _) (map_one _), one_mul] at this
  have g2 : GF.fl m₂ i = GF.fl ((P1 * A s).map (algebraMap Ω Ω₂) * u2 s) i := by
    have := l_genflag_lemma_5 ((P1 * A s).map (algebraMap Ω Ω₂)) f2
    rwa [← mul_assoc, ← Matrix.map_mul, e2, Matrix.map_one _ (map_zero _) (map_one _), one_mul] at this
  change GF.fl (m₁.map i₁) i = GF.fl (m₂.map i₂) i
  rw [l_genflag_lemma_4 i₁ g1, l_genflag_lemma_4 i₂ g2]
  have hPβ : (P1.map (algebraMap Ω Ω₁)).map i₁ = (P1.map (algebraMap Ω Ω₂)).map i₂ := by
    ext l k
    exact hα (P1 l k)
  have L : (P1.map (algebraMap Ω Ω₁) * u1 s).map i₁ =
      (P1.map (algebraMap Ω Ω₂)).map i₂ * (u2' s).map i₂ := by
    rw [Matrix.map_mul, hPβ, hU s]
  have R : ((P1 * A s).map (algebraMap Ω Ω₂) * u2 s).map i₂ =
      (P1.map (algebraMap Ω Ω₂)).map i₂ * (((A s).map (algebraMap Ω Ω₂) * u2 s).map i₂) := by
    simp only [Matrix.map_mul, mul_assoc]
  rw [L, R]
  exact l_genflag_lemma_5 _ (l_genflag_lemma_4 i₂ (hfl2' s i))

end PositivityTheory.UnitarySelfGeneration
end

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem t_ideal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω Ω' : Type) [Field Ω] [CharZero Ω] [Field Ω'] [CharZero Ω'] (φ : Ω →+* Ω') (y : (Σ k, ι k) → Ω), mCoordIdeal (fun p => φ (y p)) = mCoordIdeal y ∧ (blockFnField (fun p => φ (y p))).toSubfield = (blockFnField y).toSubfield.map φ ∧ (Function.Surjective φ → Birational y → Birational (fun p => φ (y p))) ∧ ∀ (s : MRing ι), aeval (fun p => φ (y p)) s = φ (aeval y s) := by
  intro K _ ι _ Ω Ω' _ _ _ _ φ y
  have key : ∀ (s : MRing ι), aeval (fun p => φ (y p)) s = φ (aeval y s) := by
    intro s
    have h := MvPolynomial.comp_aeval_apply (R := ℤ) y (φ.toIntAlgHom) s
    simpa using h.symm
  have cone : ∀ (s : MRing ι), mConeMap (fun p => φ (y p)) s = MvPolynomial.map φ (mConeMap y s) := by
    intro s
    induction s using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p n hp => rw [map_mul, map_mul, hp, map_mul]; simp [mConeMap]
  refine ⟨?_, ?_, ?_, key⟩
  · ext s
    simp only [mCoordIdeal, RingHom.mem_ker]
    rw [cone]
    constructor
    · intro hs
      apply MvPolynomial.map_injective φ φ.injective
      rw [hs, map_zero]
    · intro hs
      rw [hs, map_zero]
  · have e := IntermediateField.adjoin_map ℚ {t : Ω | ∃ (p : (k : K) × ι k) (q : (k : K) × ι k), p.fst = q.fst ∧ t = y p / y q} (φ.toRatAlgHom)
    have e2 := congrArg IntermediateField.toSubfield e
    rw [IntermediateField.toSubfield_map] at e2
    have hs : (φ.toRatAlgHom) '' {t : Ω | ∃ (p : (k : K) × ι k) (q : (k : K) × ι k), p.fst = q.fst ∧ t = y p / y q}
        = {t : Ω' | ∃ (p : (k : K) × ι k) (q : (k : K) × ι k), p.fst = q.fst ∧ t = φ (y p) / φ (y q)} := by
      ext t
      constructor
      · rintro ⟨u, ⟨p, q, hpq, rfl⟩, rfl⟩
        exact ⟨p, q, hpq, by simp [map_div₀]⟩
      · rintro ⟨p, q, hpq, rfl⟩
        exact ⟨y p / y q, ⟨p, q, hpq, rfl⟩, by simp [map_div₀]⟩
    rw [hs] at e2
    unfold blockFnField
    exact e2.symm
  · intro hsurj hb s'
    obtain ⟨s, rfl⟩ := hsurj s'
    obtain ⟨d, g, h, hg, hh, hne, heq⟩ := hb s
    refine ⟨d, g, h, hg, hh, ?_, ?_⟩
    · rw [key]
      exact fun h0 => hne (φ.injective (by rw [h0, map_zero]))
    · rw [key, key, heq, map_mul]

end PositivityTheory.UnitarySelfGeneration
end

section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PairIsoK

theorem finrank_congr {F₁ F₂ L : Type} [Field F₁] [Field F₂] [Field L] [Algebra F₁ L] [Algebra F₂ L]
    (A : IntermediateField F₁ L) (B : IntermediateField F₂ L) (h : A.toSubfield = B.toSubfield) :
    Module.finrank A L = Module.finrank B L := by
  have e1 : Module.finrank A L = Module.finrank A.toSubfield L := rfl
  have e2 : Module.finrank B L = Module.finrank B.toSubfield L := rfl
  rw [e1, e2, h]

theorem isGenericFlag_transport {Ωa Ωb Ω' E₁ E₂ E' : Type} [Field Ωa] [Field Ωb] [Field Ω'] [Algebra Ωa Ω'] [Algebra Ωb Ω']
    [AddCommGroup E₁] [Module Ωa E₁] [AddCommGroup E₂] [Module Ωb E₂] [AddCommGroup E'] [Module Ω' E']
    (ψ : Ωb ≃+* Ωa) (hψ : ∀ a, algebraMap Ωa Ω' (ψ a) = algebraMap Ωb Ω' a)
    (θ : E₁ ≃+ E₂) (hθ : ∀ (a : Ωb) e, θ (ψ a • e) = a • θ e) (j : E₂ →+ E') {S S' : Type} {r : S → ℕ} {r' : S' → ℕ}
    (p : S ≃ S') (hr : ∀ s, r' (p s) = r s) (V : S → Submodule Ωa E₁) (V' : S' → Submodule Ωb E₂)
    (hV : ∀ s e, e ∈ V s ↔ θ e ∈ V' (p s)) (b' : ∀ s', Fin (r' s') → E') (d : ℕ) (h : IsGenericFlag (Ω' := Ω') j V' b' d) :
    IsGenericFlag (Ω' := Ω') (j.comp θ.toAddMonoidHom) V (fun s k => b' (p s) (Fin.cast (hr s).symm k)) d := by
  obtain rfl : r = fun s => r' (p s) := funext fun s => (hr s).symm
  obtain ⟨c, u, hc, hj, hjc, hb, hu1, hu0, hst, hai, hd, hfr⟩ := h
  have hθ' : ∀ (a : Ωa) e, θ (a • e) = ψ.symm a • θ e := fun a e => by
    have := hθ (ψ.symm a) e
    rwa [ψ.apply_symm_apply] at this
  have hθi : ∀ (a : Ωb) e, θ.symm (a • e) = ψ a • θ.symm e := fun a e => by
    apply θ.injective
    rw [hθ a, θ.apply_symm_apply, θ.apply_symm_apply]
  have hsp : ∀ s, Submodule.span Ωa (Set.range fun k => θ.symm (c (p s) k)) = V s := by
    intro s
    ext e
    rw [hV, ← (hc (p s)).2]
    constructor
    · intro he
      induction he using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rw [θ.apply_symm_apply]
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx => rw [hθ']; exact Submodule.smul_mem _ _ hx
    · intro he
      have : ∀ x ∈ Submodule.span Ωb (Set.range (c (p s))),
          θ.symm x ∈ Submodule.span Ωa (Set.range fun k => θ.symm (c (p s) k)) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨k, rfl⟩ := hx
          exact Submodule.subset_span ⟨k, rfl⟩
        | zero => rw [map_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
        | smul a x _ hx => rw [hθi]; exact Submodule.smul_mem _ _ hx
      simpa using this _ he
  refine ⟨fun s k => θ.symm (c (p s) k), fun s => u (p s), fun s => ⟨?_, hsp s⟩, ?_, ?_, fun s => hb (p s), fun s => hu1 (p s),
    fun s => hu0 (p s), ?_, ?_, hd, ?_⟩
  · refine (hc (p s)).1.map_of_injective_injective (⇑ψ.symm) θ.symm.toAddMonoidHom
      (fun a h => by simpa using h) (fun m h => by simpa using h) ?_
    intro a m
    show θ.symm (ψ.symm a • m) = a • θ.symm m
    rw [hθi, ψ.apply_symm_apply]
  · intro a e
    show j (θ (a • e)) = _ • j (θ e)
    rw [hθ', hj, ← hψ, ψ.apply_symm_apply]
  · intro s
    simpa using hjc (p s)
  · intro s i
    simpa using hst (p s) i
  · have h1 := hai.comp (fun q : (Σ s, {lk : Fin (r' (p s)) × Fin (r' (p s)) // lk.2 < lk.1}) =>
      (⟨p q.1, q.2⟩ : Σ s', {lk : Fin (r' s') × Fin (r' s') // lk.2 < lk.1})) (by
        rintro ⟨s, a⟩ ⟨s', a'⟩ h
        obtain rfl : s = s' := p.injective (congrArg Sigma.fst h)
        simpa using h)
    exact h1.ringHom_of_comp_eq (f := ψ.toRingHom) (g := RingHom.id Ω') ψ.surjective Function.injective_id
      (RingHom.ext hψ)
  · have hrange : (Set.range fun q : Σ s, Fin (r' (p s)) × Fin (r' (p s)) => u (p q.1) q.2.1 q.2.2) =
        Set.range fun q : Σ s', Fin (r' s') × Fin (r' s') => u q.1 q.2.1 q.2.2 := by
      ext t
      constructor
      · rintro ⟨⟨s, a⟩, rfl⟩
        exact ⟨⟨p s, a⟩, rfl⟩
      · rintro ⟨⟨s', a⟩, rfl⟩
        obtain ⟨s, rfl⟩ := p.surjective s'
        exact ⟨⟨s, a⟩, rfl⟩
    rw [hrange, ← hfr]
    refine finrank_congr _ _ ?_
    rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield]
    congr 2
    ext t
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨ψ.symm a, by rw [← hψ, ψ.apply_symm_apply]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨ψ a, hψ a⟩

theorem IsGenericFlag_deg_pos {Ωa Ω' E₁ E' : Type} [Field Ωa] [Field Ω'] [Algebra Ωa Ω'] [AddCommGroup E₁] [Module Ωa E₁]
    [AddCommGroup E'] [Module Ω' E'] {j : E₁ →+ E'} {S : Type} {r : S → ℕ} {V : S → Submodule Ωa E₁}
    {b : ∀ s, Fin (r s) → E'} {d : ℕ} (h : IsGenericFlag (Ω' := Ω') j V b d) : 0 < d := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hd, _⟩ := h
  exact hd

theorem exists_coeff {Ωa Ω' E₁ E' : Type} [Field Ωa] [Field Ω'] [Algebra Ωa Ω'] [AddCommGroup E₁] [Module Ωa E₁]
    [AddCommGroup E'] [Module Ω' E'] {j : E₁ →+ E'} {S : Type} {r : S → ℕ} {V : S → Submodule Ωa E₁}
    {b : ∀ s, Fin (r s) → E'} {d : ℕ} (h : IsGenericFlag (Ω' := Ω') j V b d) (s : S) {n : ℕ} (c : Fin n → E₁)
    (hc : Submodule.span Ωa (Set.range c) = V s) :
    ∃ m : Matrix (Fin n) (Fin (r s)) Ω', ∀ k, b s k = ∑ l, m l k • j (c l) := by
  obtain ⟨c', u, hc', hj, -, -, -, -, hst, -⟩ := h
  have h1 : ∀ l, j (c' s l) ∈ Submodule.span Ω' (Set.range fun l => j (c l)) := by
    intro l
    have hm : c' s l ∈ Submodule.span Ωa (Set.range c) := by
      rw [hc, ← (hc' s).2]
      exact Submodule.subset_span ⟨l, rfl⟩
    have key : ∀ x ∈ Submodule.span Ωa (Set.range c), j x ∈ Submodule.span Ω' (Set.range fun l => j (c l)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨q, rfl⟩ := hx
        exact Submodule.subset_span ⟨q, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx => rw [hj]; exact Submodule.smul_mem _ _ hx
    exact key _ hm
  have h2 : ∀ k, b s k ∈ Submodule.span Ω' (Set.range fun l => j (c l)) := by
    intro k
    have hk : b s k ∈ flagStep Ω' (b s) (k + 1) := Submodule.subset_span ⟨k, by simp, rfl⟩
    rw [hst] at hk
    refine (Submodule.span_le.2 ?_ : flagStep Ω' _ _ ≤ _) hk
    rintro _ ⟨a, -, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (h1 l)
  have h3 := fun k => (Submodule.mem_span_range_iff_exists_fun Ω').1 (h2 k)
  choose m hm using h3
  exact ⟨fun l k => m k l, fun k => (hm k).symm⟩

theorem exists_basis {Ωa Ω' E₁ E' : Type} [Field Ωa] [Field Ω'] [Algebra Ωa Ω'] [AddCommGroup E₁] [Module Ωa E₁]
    [AddCommGroup E'] [Module Ω' E'] {j : E₁ →+ E'} {S : Type} {r : S → ℕ} {V : S → Submodule Ωa E₁}
    {b : ∀ s, Fin (r s) → E'} {d : ℕ} (h : IsGenericFlag (Ω' := Ω') j V b d) (s : S) :
    ∃ c : Fin (r s) → E₁, LinearIndependent Ωa c ∧ Submodule.span Ωa (Set.range c) = V s := by
  obtain ⟨c, _, hc, _⟩ := h
  exact ⟨c s, hc s⟩

theorem flagStep_rows {Ω₃ F : Type} [Field Ω₃] [AddCommGroup F] [Module Ω₃ F] {r : ℕ} (f : Fin r → F)
    (m m' : Fin r → Fin r → Ω₃) (h : ∀ i, flagStep Ω₃ (fun k l => m l k : Fin r → Fin r → Ω₃) i =
      flagStep Ω₃ (fun k l => m' l k : Fin r → Fin r → Ω₃) i) (i : ℕ) :
    flagStep Ω₃ (fun k => ∑ l, m l k • f l) i = flagStep Ω₃ (fun k => ∑ l, m' l k • f l) i := by
  have := GlobalTheory.CompanionTheory.Ar.FlagPull.flagStep_map_eq (i := RingHom.id Ω₃)
    (j := (Fintype.linearCombination Ω₃ f).toAddMonoidHom) (fun a e => by simp) h i
  simpa [Fintype.linearCombination_apply] using this

theorem flagStep_cast {Ω₃ F : Type} [Field Ω₃] [AddCommGroup F] [Module Ω₃ F] {r r' : ℕ} (h : r = r') (b : Fin r' → F)
    (i : ℕ) : flagStep Ω₃ (fun a : Fin r => b (Fin.cast h a)) i = flagStep Ω₃ b i := by
  subst h
  rfl

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem pull_both {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type}
    {J' : K' → Type} [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}
    (A : HodgeCpt Y S y) (Fl : A.Flag) (x : Sp Ω ⟶ Xo.XF c) (Z : Scheme.{0}) (ξ' : Sp Ω' ⟶ Z) (h : Z ⟶ A.X)
    (κ : K → K') (v : (Σ k, J k) → (Σ k, J' k))
    (hx : A.ξ ≫ A.f = x ≫ Y.j) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S)
    (hvb : ∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn
      {q | InFibre A.ξ p q} (labelRk D s) ⊤)
    (hall : ∀ q : Z, genPt ξ' ⤳ q) (htie : CoordTie ℤ ξ' (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩))
    (hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i) (hb : IsBlockMap κ v)
    (hy : ∀ q, y' (v q) = i (y q)) (hfd : FiniteDimensional i.fieldRange Ω') :
    ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (Fl' : A'.Flag) (ψ' : A.Ω₀ ≃+* A'.Ω₀) (θ' : Fl.Li₀ ≃+ Fl'.Li₀)
      (j : A.Li →+ A'.Li),
      A'.ξ ≫ e.hom = ξ' ∧ A'.f = e.hom ≫ h ≫ A.f ∧ A'.cst = i.comp A.cst ∧ A'.R = A.R ∧ IsExtOver i j ∧
      (∀ s k, Fl'.b s k = j (Fl.b s k)) ∧ A'.fn.comp ψ'.toRingHom = i.comp A.fn ∧
      (∀ e, (Fl'.M₀.pt (θ' e)).left = spMap (dualMap ψ'.toRingHom) ≫ (Fl.M₀.pt e).left) ∧
      (∀ e, Fl'.j (θ' e) = j (Fl.j e)) ∧
      (∀ xdeg e, Fl.RootLines xdeg e → Fl'.RootLines (fun r => pullDeg κ (xdeg r)) (fun r => i (e r))) ∧
      ∀ r (e₀ : Ω) (L : HermLine J) (L' : HermLine J'), Fl.IsHodgeLine r e₀ L → IsPullHerm κ v L L' →
        Fl'.IsHodgeLine r (i e₀) L' := by
  obtain ⟨A', e, j, m, h1, h2, h3, h4, h5, h6, h7, -, h9⟩ :=
    PositivityTheory.UnitarySelfGeneration.hodge_compact_pullback E H D l Xo c O β Y S Ω Ω' i K K' J J' y y' A x Z ξ' h hx hdisc hvb hall htie hnorm hd
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ (e.hom ≫ h) i := by
    show A'.ξ ≫ e.hom ≫ h = _
    rw [← Category.assoc, h1]
    exact hd
  have hf : A'.f = (e.hom ≫ h) ≫ A.f := by rw [h2, Category.assoc]
  obtain ⟨Fl', hb', -, ⟨ψ', θ', q1, -, q3, q4⟩, q5⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagPull.flag_pull E H D l Xo c O β Y S Ω Ω' i K K' J J' y y' A A' (e.hom ≫ h) j m κ v Fl hb hy hdom hf h3
      h4 h6 h7 h9 hfd
  refine ⟨A', e, Fl', ψ', θ', j, h1, h2, h4, h5, h6, hb', q1, q3, q4, q5, fun r e₀ L L' hL hP => ?_⟩
  exact GlobalTheory.T.hodge_cpt_finite_extension E H D l Xo c O β Y S Ω Ω' i K K' J J' y y' A A' (e.hom ≫ h) j m κ v Fl hb hy hdom hf h3 h4 h6 h7 h9
    Fl' hb' r e₀ L L' hL hP

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem twTan_pre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    {g : HostAut H} {Φ : Xo.X ⟶ Xo.X} {n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ} {Y : Model Xo c β}
    {Y' : Model Xo c β'} {T T' : Scheme.{0}} {u₁ : T ⟶ Y.t.G.left} {u₂ : T ⟶ Y'.t.G.left} (w : T' ⟶ T)
    (h : TwTan n Y Y' u₁ u₂) : TwTan n Y Y' (w ≫ u₁) (w ≫ u₂) := by
  obtain ⟨u, u', h1, h2, h3, h4⟩ := h
  refine ⟨w ≫ u, w ≫ u', ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, h1]
  · rw [Category.assoc, h2]
  · rw [Category.assoc, h3, Category.assoc]
  · simp only [Category.assoc, h4]

theorem pair_iso : HodgeComparisonCompatibility → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ) (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'), Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) → IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ : M.K → K) (v : (Σ k, M.ι k) → Σ k, ι k) (κ' : M'.K → K) (v' : (Σ k, M'.ι k) → Σ k, ι k) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, ι k) → Ω) (b : MRing ι) (d : K → ℕ), IsBlockMap κ v ∧ IsBlockMap κ' v' ∧ mCoordIdeal (y ∘ v) = M.P ∧ mCoordIdeal (y ∘ v') = M'.P ∧ IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * T.Fl.deg = IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * T'.Fl.deg ∧ ∀ (r : CMType H × Fin (D.p + D.q)) (L L' : HermLine ι), IsPullHerm κ v (T.sing r) L → IsPullHerm κ' v' (T'.sing (π r.1, r.2)) L' → IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} L L' := by
  intro hCmp hTh E _ _ _ H D l Xo c O _ β Y g Φ n π S nn M M' T T' hβ hs hπ himg hR
  obtain ⟨x₀, x₀', ψ, hξ, hξ', hfst, hsnd, hcst, hcst'⟩ := himg
  obtain ⟨π₀, hπ₀, hlab⟩ := GlobalTheory.T.cm_type_host_aut_permutation E H l c g
  have hππ : π₀ = π := Equiv.ext fun τ => Subtype.ext ((hπ₀ τ).trans (hπ τ).symm)
  subst hππ
  obtain ⟨θ, hθs, hθt, hθV⟩ := GlobalTheory.T.twisted_hodge_cpt_compare E H D l Xo c O O β β Y Y g Φ n S M.Ω M'.Ω M.K M'.K M.ι M'.ι M.y M'.y T.A T'.A
    T.Fl T'.Fl ψ x₀ x₀' hβ hβ hξ hξ' hfst hsnd

  letI a₁ : Algebra T.A.Ω₀ M.Ω := T.A.fn.toAlgebra
  letI a₂ : Algebra T.A.Ω₀ M'.Ω := (T'.A.fn.comp ψ.symm.toRingHom).toAlgebra
  letI a₃ : Algebra T'.A.Ω₀ M'.Ω := T'.A.fn.toAlgebra
  have hrl : ∀ s, labelRk D (Sum.map π₀ π₀ s) = labelRk D s := by rintro (τ | τ) <;> rfl
  have g₁ : IsGenericFlag (Ω' := M.Ω) T.Fl.j T.Fl.V₀ T.Fl.b T.Fl.deg := T.Fl.generic
  have g₂ : IsGenericFlag (Ω' := M'.Ω) (T'.Fl.j.comp θ.toAddMonoidHom) T.Fl.V₀
      (fun s k => T'.Fl.b (Equiv.sumCongr π₀ π₀ s) (Fin.cast (hrl s).symm k)) T'.Fl.deg :=
    isGenericFlag_transport ψ (fun a => by
        show T'.A.fn (ψ.symm (ψ a)) = T'.A.fn a
        rw [ψ.symm_apply_apply]) θ (fun a e => hθs a e) T'.Fl.j (Equiv.sumCongr π₀ π₀) hrl T.Fl.V₀ T'.Fl.V₀
      (fun s e => hθV s _ (by simpa [Equiv.sumCongr] using (hlab s)) e) T'.Fl.b T'.Fl.deg T'.Fl.generic
  obtain ⟨Ω₃, fΩ, i₁, i₂, hi, ⟨n₁, n₂, hn₁, hn, hf₁, hf₂⟩, hflag⟩ := PositivityTheory.UnitarySelfGeneration.l_genflag T.A.Ω₀ M.Ω M'.Ω T.Fl.Li₀ T.A.Li T'.A.Li
    T.Fl.j (T'.Fl.j.comp θ.toAddMonoidHom) (CMType H ⊕ CMType H) (labelRk D) T.Fl.V₀ T.Fl.b _ T.Fl.deg T'.Fl.deg g₁ g₂
  have hn₂ : 0 < n₂ := by
    have := Nat.mul_pos hn₁ (IsGenericFlag_deg_pos g₁)
    rw [hn] at this
    exact Nat.pos_of_mul_pos_right this
  haveI : CharZero M.Ω := charZero_of_injective_ringHom T.A.cst.injective
  haveI : CharZero M'.Ω := charZero_of_injective_ringHom T'.A.cst.injective
  haveI : CharZero Ω₃ := charZero_of_injective_ringHom i₁.injective
  have hfd₁ : FiniteDimensional i₁.fieldRange Ω₃ := FiniteDimensional.of_finrank_pos (by omega)
  have hfd₂ : FiniteDimensional i₂.fieldRange Ω₃ := FiniteDimensional.of_finrank_pos (by omega)
  obtain ⟨K, hK, ι, hι, κ₁, v₁, κ₂, v₂, y, Z, ξ, h₁, h₂, hb₁, hb₂, hy₁, hy₂, harith, hbir, hall, htie, hnorm, hd₁, hd₂, hr₁, hr₂⟩ :=
    PositivityTheory.UnitarySelfGeneration.j_normal M.K M.ι M'.K M'.ι M.Ω M'.Ω Ω₃ i₁ i₂ M.y M'.y (Top.dimFl (CMType H) (D.p + D.q) + 1) T.A.X T'.A.X T.A.ξ T'.A.ξ
      M.arith M'.arith M.birational M'.birational hfd₁ hfd₂ T.A.all T'.A.all T.A.tie T'.A.tie
  have hx₁ : T.A.ξ ≫ T.A.f = (spMap T.A.fn ≫ x₀) ≫ Y.j := by
    rw [Category.assoc, ← hξ]; exact T.A.fn_over
  have hx₂ : T'.A.ξ ≫ T'.A.f = (spMap T'.A.fn ≫ x₀') ≫ Y.j := by
    rw [Category.assoc, ← hξ']; exact T'.A.fn_over
  obtain ⟨A₁, e₁, Fl₁, ψ₁, θ₁, j₁, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ :=
    pull_both i₁ T.A T.Fl (spMap T.A.fn ≫ x₀) Z ξ h₁ κ₁ v₁ hx₁ T.discr T.ht_vb hall htie hnorm hd₁ hb₁
      (fun q => congrFun hy₁ q) hfd₁
  obtain ⟨A₂, e₂, Fl₂, ψ₂, θ₂, j₂, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
    pull_both i₂ T'.A T'.Fl (spMap T'.A.fn ≫ x₀') Z ξ h₂ κ₂ v₂ hx₂ T'.discr T'.ht_vb hall htie hnorm hd₂ hb₂
      (fun q => congrFun hy₂ q) hfd₂

  have hi' : i₁.comp (T.A.fn.comp ψ.toRingHom) = i₂.comp T'.A.fn := by
    ext a
    have := congrArg (fun f => f (ψ a)) hi
    simpa [a₁, a₂, RingHom.algebraMap_toAlgebra] using this
  have hkey : spMap i₁ ≫ spMap T.A.fn ≫ spMap ψ.toRingHom = spMap i₂ ≫ spMap T'.A.fn := by
    rw [spMap_spMap, spMap_spMap, spMap_spMap, hi']
  have hk3 : ∀ {W : Scheme.{0}} (t : Sp T'.A.Ω₀ ⟶ W), spMap i₂ ≫ spMap T'.A.fn ≫ t =
      spMap i₁ ≫ spMap T.A.fn ≫ spMap ψ.toRingHom ≫ t := by
    intro W t
    rw [← Category.assoc, ← hkey]
    simp only [Category.assoc]
  have hX₁ : A₁.ξ ≫ A₁.f = (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Y.j := by
    have hd : ξ ≫ h₁ = spMap i₁ ≫ T.A.ξ := hd₁
    calc A₁.ξ ≫ A₁.f = (A₁.ξ ≫ e₁.hom) ≫ h₁ ≫ T.A.f := by rw [p2, Category.assoc]
      _ = (ξ ≫ h₁) ≫ T.A.f := by rw [p1, Category.assoc]
      _ = spMap i₁ ≫ T.A.ξ ≫ T.A.f := by rw [hd, Category.assoc]
      _ = _ := by rw [hx₁]; simp only [Category.assoc]
  have hX₂ : A₂.ξ ≫ A₂.f = (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Y.j := by
    have hd : ξ ≫ h₂ = spMap i₂ ≫ T'.A.ξ := hd₂
    calc A₂.ξ ≫ A₂.f = (A₂.ξ ≫ e₂.hom) ≫ h₂ ≫ T'.A.f := by rw [q2, Category.assoc]
      _ = (ξ ≫ h₂) ≫ T'.A.f := by rw [q1, Category.assoc]
      _ = spMap i₂ ≫ T'.A.ξ ≫ T'.A.f := by rw [hd, Category.assoc]
      _ = _ := by rw [hx₂]; simp only [Category.assoc]
  have hfst₃ : (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Limits.pullback.fst _ _ =
      (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Limits.pullback.fst _ _ ≫ Φ.hom := by
    simp only [Category.assoc]
    rw [hk3, hfst]
  have hsnd₃ : (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Limits.pullback.snd _ _ =
      (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Limits.pullback.snd _ _ := by
    simp only [Category.assoc]
    rw [hk3, hsnd]
  have hc₁ : (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Limits.pullback.snd _ _ = spMap A₁.cst := by
    rw [p3, ← spMap_spMap, ← hcst]
    simp only [Category.assoc]
  have hc₂ : (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Limits.pullback.snd _ _ = spMap A₂.cst := by
    rw [q3, ← spMap_spMap, ← hcst']
    simp only [Category.assoc]
  have hAc : A₁.cst = A₂.cst := spMap_inj (by rw [← hc₁, ← hc₂, hsnd₃])
  have hξe : A₂.ξ ≫ (e₂ ≪≫ e₁.symm).hom = A₁.ξ := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, q1, ← p1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨φ, hφt, -, hφV, hφz⟩ := hCmp E H D l Xo c O O β β Y Y g Φ n S Ω₃ K ι y A₁ A₂ (e₂ ≪≫ e₁.symm) _ _ hβ hβ hs hξe hX₁ hX₂
    hfst₃ hsnd₃ hAc hc₁ (fun p hp => by rw [q4, p4]; exact hR p hp)

  let ψ₃ : A₂.Ω₀ ≃+* A₁.Ω₀ := ψ₂.symm.trans (ψ.trans ψ₁)
  let θ₃ : Fl₁.Li₀ ≃+ Fl₂.Li₀ := θ₁.symm.trans (θ.trans θ₂)
  have hθ₃ : ∀ e, θ₃ (θ₁ e) = θ₂ (θ e) := fun e => by simp [θ₃]
  have hfn : A₁.fn.comp ψ₃.toRingHom = A₂.fn := by
    ext a
    have h1 := congrArg (fun f => f (ψ (ψ₂.symm a))) p7
    have h2 := congrArg (fun f => f (ψ₂.symm a)) hi'
    have h3 := congrArg (fun f => f (ψ₂.symm a)) q7
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] at h1 h2 h3
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ψ₃, RingEquiv.trans_apply]
    rw [h1, h2, ← h3]
  have hψc : (dualMap ψ₃.toRingHom).comp (dualMap ψ₂.toRingHom) = (dualMap ψ₁.toRingHom).comp (dualMap ψ.toRingHom) := by
    rw [← GlobalTheory.CompanionTheory.Ar.FlagPull.dualMap_comp, ← GlobalTheory.CompanionTheory.Ar.FlagPull.dualMap_comp]
    congr 1
    ext a
    simp [ψ₃]
  have htw : ∀ e, TwTan n Y Y (Fl₁.M₀.pt e).left (spMap (dualMap ψ₃.toRingHom) ≫ (Fl₂.M₀.pt (θ₃ e)).left) := by
    intro e
    obtain ⟨e₀, rfl⟩ := θ₁.surjective e
    rw [hθ₃, q8, p8, ← Category.assoc, spMap_spMap, hψc, ← spMap_spMap, Category.assoc]
    exact twTan_pre _ (hθt e₀)
  obtain ⟨-, hsteps⟩ := GlobalTheory.T.twisted_hodge_cpt_flag E H D l Xo c O O β β Y Y g Φ n S Ω₃ K ι y A₁ A₂ Fl₁ Fl₂ ψ₃ θ₃ φ hβ hβ hfn hφt htw
  have hst : ∀ s k, (flagStep Ω₃ (Fl₁.b s) k).map (φ : A₁.Li →ₗ[Ω₃] A₂.Li) =
      flagStep Ω₃ (Fl₂.b (Equiv.sumCongr π₀ π₀ s)) k := by
    intro s
    obtain ⟨cc, hcl, hcs⟩ := exists_basis g₁ s
    obtain ⟨m₁, hm₁⟩ := exists_coeff g₁ s cc hcs
    obtain ⟨m₂, hm₂⟩ := exists_coeff g₂ s cc hcs
    have hrow := hflag s cc m₁ m₂ hcl hcs hm₁ hm₂
    refine hsteps s (Equiv.sumCongr π₀ π₀ s) _ (fun q => θ₁ (cc q)) (fun q a => i₁ (m₁ q a)) ?_ ?_
    · intro k
      congr 1
      funext a
      rw [p6, hm₁ a, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [p5.1, p9]
    · intro k
      refine (flagStep_cast (hrl s).symm (Fl₂.b (Equiv.sumCongr π₀ π₀ s)) k).symm.trans ?_
      have e1 : (fun a => Fl₂.b (Equiv.sumCongr π₀ π₀ s) (Fin.cast (hrl s).symm a)) =
          fun a => ∑ q, i₂ (m₂ q a) • Fl₂.j (θ₃ (θ₁ (cc q))) := by
        funext a
        rw [q6, hm₂ a, map_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [q5.1, hθ₃, q9]
        rfl
      exact (congrArg (fun f => flagStep Ω₃ f k) e1).trans
        (flagStep_rows (fun q => Fl₂.j (θ₃ (θ₁ (cc q)))) (fun q a => i₂ (m₂ q a)) (fun q a => i₁ (m₁ q a))
          (fun i => (hrow i).symm) k)
  have hemb : ∀ s, A₂.emb (Equiv.sumCongr π₀ π₀ s) = (A₁.emb s).comp g.s.toRingHom := by
    intro s
    show A₂.cst.comp (labelEmb c (Sum.map π₀ π₀ s)) = (A₁.cst.comp (labelEmb c s)).comp g.s.toRingHom
    rw [hlab s, hAc]
    rfl
  have hgram := GlobalTheory.T.hodge_compactification_interior_point hTh E H D l Xo c O β Y S Ω₃ K ι y A₁ Fl₁ hβ
  obtain ⟨b, d, hbm, hbn, hbz⟩ := GlobalTheory.T.hodge_cpt_multihomog_form E H D l Xo c O β Y S Ω₃ K ι y A₁ _ hX₁ hβ
  refine ⟨K, hK, ι, hι, κ₁, v₁, κ₂, v₂, Ω₃, fΩ, inferInstance, y, b, d, hb₁, hb₂, ?_, ?_, harith, hbm, hbn, ?_, ?_, ?_⟩
  · rw [hy₁]
    exact (PositivityTheory.UnitarySelfGeneration.t_ideal M.K M.ι M.Ω Ω₃ i₁ M.y).1
  · rw [hy₂]
    exact (PositivityTheory.UnitarySelfGeneration.t_ideal M'.K M'.ι M'.Ω Ω₃ i₂ M'.y).1
  · rw [hr₁, hf₁]
    exact hn₁.ne'
  · rw [hr₁, hr₂, hf₁, hf₂]
    exact hn
  · intro r L L' hL hL'
    have hdeg : (Fl₁.rootLat (r.1, r.2)).IsDegOn Set.univ y L.a (i₁ (T.e r)) := by
      have := p10 _ _ T.roots r
      rw [hL.1, T.sing_deg]
      exact this
    have hdeg' : (Fl₂.rootLat (π₀ r.1, r.2)).IsDegOn Set.univ y L'.a (i₂ (T'.e (π₀ r.1, r.2))) := by
      have := q10 _ _ T'.roots (π₀ r.1, r.2)
      rw [hL'.1, T'.sing_deg]
      exact this
    have hH := p11 r (T.e r) (T.sing r) L (T.hodge r) hL
    have hH' := q11 (π₀ r.1, r.2) (T'.e (π₀ r.1, r.2)) (T'.sing (π₀ r.1, r.2)) L' (T'.hodge _) hL'
    obtain ⟨f, f', hiso, hdef⟩ := GlobalTheory.T.hodge_cpt_iso_compare E H D l Xo c O O β β Y Y S Ω₃ K ι y A₁ A₂ (e₂ ≪≫ e₁.symm) φ Fl₁ Fl₂ r.1 (π₀ r.1) r.2
      (i₁ (T.e r)) (i₂ (T'.e (π₀ r.1, r.2))) L L' hbir hξe
      (fun q h v => ⟨hφV (.inl r.1) (.inl (π₀ r.1)) (hemb (.inl r.1)) q h v, hφV (.inr r.1) (.inr (π₀ r.1)) (hemb (.inr r.1)) q h v⟩)
      (fun k => ⟨hst (.inl r.1) k, hst (.inr r.1) k⟩) hφz hdeg hdeg' hH hH' hgram
    exact ⟨f, f', hiso, fun w hw => hdef w (hbz w hw.1 hw.2)⟩

end GlobalTheory.CompanionTheory.Ar.PairIsoK

namespace PositivityTheory.UnitarySelfGeneration

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

theorem pair_iso : HodgeComparisonCompatibility → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ) (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'), Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) → IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ : M.K → K) (v : (Σ k, M.ι k) → Σ k, ι k) (κ' : M'.K → K) (v' : (Σ k, M'.ι k) → Σ k, ι k) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, ι k) → Ω) (b : MRing ι) (d : K → ℕ), IsBlockMap κ v ∧ IsBlockMap κ' v' ∧ mCoordIdeal (y ∘ v) = M.P ∧ mCoordIdeal (y ∘ v') = M'.P ∧ IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * T.Fl.deg = IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * T'.Fl.deg ∧ ∀ (r : CMType H × Fin (D.p + D.q)) (L L' : HermLine ι), IsPullHerm κ v (T.sing r) L → IsPullHerm κ' v' (T'.sing (π r.1, r.2)) L' → IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} L L' :=
  @GlobalTheory.CompanionTheory.Ar.PairIsoK.pair_iso

end PositivityTheory.UnitarySelfGeneration
end
end
