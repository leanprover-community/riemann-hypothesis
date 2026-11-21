import Mathlib
import GroundTheory.LocalFields.FormalGroups.OverUnramified
import GroundTheory.LocalFields.LubinTateTorsion
import GroundTheory.LocalFields.CompletedUnramified
import GroundTheory.LocalFields.LubinTateTower
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.DescentPowerSubgroups

section
noncomputable section

namespace GroundTheory.LocalField

open PowerSeries

section HomExt

variable {B S : Type*} [CommRing B] [CommRing S]

theorem powerSeries_ringHom_ext {J : Ideal S} (hJ : ∀ z : S, (∀ k : ℕ, z ∈ J ^ k) → z = 0)
    {Φ₁ Φ₂ : B⟦X⟧ →+* S} (hC : ∀ b : B, Φ₁ (C b) = Φ₂ (C b)) (hX : Φ₁ X = Φ₂ X)
    (hXJ : Φ₁ X ∈ J) : Φ₁ = Φ₂ := by
  have hpoly : Φ₁.comp (Polynomial.coeToPowerSeries.ringHom (R := B)) =
      Φ₂.comp (Polynomial.coeToPowerSeries.ringHom (R := B)) := by
    apply Polynomial.ringHom_ext
    · intro b
      simpa using hC b
    · simpa using hX
  have hp : ∀ p : Polynomial B, Φ₁ (p : B⟦X⟧) = Φ₂ (p : B⟦X⟧) := fun p =>
    congrArg (fun Φ : Polynomial B →+* S => Φ p) hpoly
  ext F
  refine sub_eq_zero.mp (hJ _ fun k => ?_)
  set G : B⟦X⟧ := PowerSeries.mk fun i => coeff (i + k) F
  have hF : Φ₁ F - Φ₂ F = Φ₁ X ^ k * (Φ₁ G - Φ₂ G) := by
    conv_lhs => rw [F.eq_X_pow_mul_shift_add_trunc k]
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, hp, ← hX]
    ring
  rw [hF]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hXJ k)

end HomExt

section RootEval

variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}

variable [IsAdicComplete I B] (hP : P.IsDistinguishedAt I)

def rootEval : B⟦X⟧ →ₐ[B] AdjoinRoot P :=
  (hP.algEquivQuotient.symm.toAlgHom : B⟦X⟧ ⧸ Ideal.span {(P : B⟦X⟧)} →ₐ[B] AdjoinRoot P).comp
    (Ideal.Quotient.mkₐ B _)

theorem rootEval_coe (p : Polynomial B) : rootEval hP (p : B⟦X⟧) = AdjoinRoot.mk P p := by
  apply hP.algEquivQuotient.injective
  change hP.algEquivQuotient (hP.algEquivQuotient.symm _) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

@[simp]
theorem rootEval_X : rootEval hP X = AdjoinRoot.root P := by
  rw [← Polynomial.coe_X, rootEval_coe]
  rfl

@[simp]
theorem rootEval_C (b : B) : rootEval hP (C b) = AdjoinRoot.of P b := by
  rw [← Polynomial.coe_C, rootEval_coe, AdjoinRoot.mk_C]

theorem rootEval_eq_zero_iff (F : B⟦X⟧) :
    rootEval hP F = 0 ↔ F ∈ Ideal.span {(P : B⟦X⟧)} := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change hP.algEquivQuotient.symm _ = 0 ↔ _
  rw [map_eq_zero_iff _ hP.algEquivQuotient.symm.injective]
  rfl

theorem rootEval_eq_rootEval_iff (F G : B⟦X⟧) :
    rootEval hP F = rootEval hP G ↔ F - G ∈ Ideal.span {(P : B⟦X⟧)} := by
  rw [← rootEval_eq_zero_iff hP, map_sub, sub_eq_zero]

theorem rootEval_self : rootEval hP (P : B⟦X⟧) = 0 := by
  rw [rootEval_coe, AdjoinRoot.mk_self]

theorem rootEval_subst_coe {G : B⟦X⟧} (hG : constantCoeff G = 0) (p : Polynomial B) :
    rootEval hP (subst G (p : B⟦X⟧)) = Polynomial.aeval (rootEval hP G) p := by
  rw [subst_coe (HasSubst.of_constantCoeff_zero' hG), Polynomial.aeval_algHom_apply]

theorem rootEval_mem_span_root {G : B⟦X⟧} (hG : constantCoeff G = 0) :
    rootEval hP G ∈ Ideal.span {AdjoinRoot.root P} := by
  obtain ⟨H, rfl⟩ := PowerSeries.X_dvd_iff.mpr hG
  rw [map_mul, rootEval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem isUnit_rootEval {G : B⟦X⟧} (hG : IsUnit (constantCoeff G)) :
    IsUnit (rootEval hP G) :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr hG).map _

end RootEval

section Hausdorff

variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}

theorem root_pow_mem_map (hP : P.IsDistinguishedAt I) :
    AdjoinRoot.root P ^ P.natDegree ∈ I.map (AdjoinRoot.of P) := by
  have h : Polynomial.eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P)
      (Polynomial.X ^ P.natDegree +
        ∑ i ∈ Finset.range P.natDegree, Polynomial.C (P.coeff i) * Polynomial.X ^ i) = 0 := by
    rw [← hP.monic.as_sum]
    exact AdjoinRoot.eval₂_root P
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at h
  rw [eq_neg_of_add_eq_zero_left h, neg_mem_iff]
  refine Ideal.sum_mem _ fun i hi => ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  exact Ideal.mul_mem_right _ _
    (Ideal.mem_map_of_mem _ (hP.mem (Finset.mem_range.mp hi)))

theorem repr_mem_of_mem_map (hP : P.Monic) (J : Ideal B) {z : AdjoinRoot P}
    (hz : z ∈ J.map (AdjoinRoot.of P)) (i : Fin (AdjoinRoot.powerBasis' hP).dim) :
    (AdjoinRoot.powerBasis' hP).basis.repr z i ∈ J := by
  have hz' : z ∈ J • (⊤ : Submodule B (AdjoinRoot P)) := by
    rw [Ideal.smul_top_eq_map]
    exact hz
  refine Submodule.smul_induction_on hz' (fun a ha m _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact J.mul_mem_right _ ha
  · rw [map_add, Finsupp.add_apply]
    exact J.add_mem hx hy

theorem eq_zero_of_forall_mem_span_root_pow [IsHausdorff I B] (hP : P.IsDistinguishedAt I)
    {z : AdjoinRoot P} (hz : ∀ k : ℕ, z ∈ Ideal.span {AdjoinRoot.root P} ^ k) : z = 0 := by
  set pb := AdjoinRoot.powerBasis' hP.monic
  have hmem : ∀ k : ℕ, z ∈ (I ^ k).map (AdjoinRoot.of P) := by
    intro k
    have h := hz (P.natDegree * k)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨w, hw⟩ := h
    rw [hw, pow_mul, Ideal.map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (root_pow_mem_map hP) k)
  apply pb.basis.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  refine IsHausdorff.haus' (I := I) _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact repr_mem_of_mem_map hP.monic _ (hmem k) i

theorem rootEval_ringHom_ext [IsHausdorff I B] (hP : P.IsDistinguishedAt I)
    {Φ₁ Φ₂ : B⟦X⟧ →+* AdjoinRoot P}
    (hC : ∀ b : B, Φ₁ (C b) = Φ₂ (C b)) (hX : Φ₁ X = Φ₂ X)
    (hXJ : Φ₁ X ∈ Ideal.span {AdjoinRoot.root P}) : Φ₁ = Φ₂ :=
  powerSeries_ringHom_ext (fun _ hz => eq_zero_of_forall_mem_span_root_pow hP hz) hC hX hXJ

end Hausdorff

section Coordinates

variable {B : Type*} [CommRing B] {P : Polynomial B}

theorem eq_zero_of_of_mul_eq_zero (hP : P.Monic) {b : B} (hb : ∀ c : B, b * c = 0 → c = 0)
    {z : AdjoinRoot P} (h : AdjoinRoot.of P b * z = 0) : z = 0 := by
  set pb := AdjoinRoot.powerBasis' hP
  have h' : b • z = 0 := by
    rw [Algebra.smul_def]
    exact h
  apply pb.basis.repr.injective
  ext i
  have := congrArg (fun w => pb.basis.repr w i) h'
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
  rw [map_zero, Finsupp.zero_apply]
  exact hb _ this

theorem eq_zero_of_mul_eq_zero_of_pow_eq (hP : P.Monic) {b : B}
    (hb : ∀ c : B, b * c = 0 → c = 0) {y : AdjoinRoot P} {k : ℕ} (hk : k ≠ 0)
    (hy : y ^ k = AdjoinRoot.of P b) {z : AdjoinRoot P} (h : y * z = 0) : z = 0 := by
  refine eq_zero_of_of_mul_eq_zero hP hb ?_
  rw [← hy]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [pow_succ, mul_assoc, h, mul_zero]

end Coordinates

end GroundTheory.LocalField
end
end

section
noncomputable section

open PowerSeries IsLocalRing ValuativeRel GroundTheory.LocalField.FormalGroup

namespace GroundTheory.LocalField

section Series

variable {R : Type*} [CommRing R]

theorem coe_comp_eq_subst (p q : Polynomial R) (hq : q.coeff 0 = 0) :
    ((p.comp q : Polynomial R) : R⟦X⟧) = subst (q : R⟦X⟧) (p : R⟦X⟧) := by
  rw [subst_coe (HasSubst.of_constantCoeff_zero' (by rw [Polynomial.constantCoeff_coe, hq])),
    Polynomial.comp_eq_aeval]
  have h := Polynomial.aeval_algHom_apply (Polynomial.coeToPowerSeries.algHom R) q p
  simp only [Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self, map_id] at h
  exact h.symm

theorem map_coe_polynomial {S : Type*} [CommRing S] (φ : R →+* S) (p : Polynomial R) :
    PowerSeries.map φ (p : R⟦X⟧) = ((p.map φ : Polynomial S) : S⟦X⟧) := by
  ext n
  simp

theorem constantCoeff_subst_of_constantCoeff_eq_zero {G : R⟦X⟧} (hG : constantCoeff G = 0)
    (F : R⟦X⟧) : constantCoeff (subst G F : R⟦X⟧) = constantCoeff F := by
  have hs := HasSubst.of_constantCoeff_zero' hG
  conv_lhs => rw [F.eq_X_mul_shift_add_const]
  rw [← coe_substAlgHom hs, map_add, map_mul, coe_substAlgHom hs, subst_X hs, subst_C]
  change constantCoeff (G * _ + PowerSeries.C _) = _
  rw [map_add, map_mul, hG, zero_mul, zero_add, constantCoeff_C]

theorem exists_subst_eq_mul {G W : R⟦X⟧} (hG : constantCoeff G = 0) (hW : constantCoeff W = 0) :
    ∃ V : R⟦X⟧, (subst G W : R⟦X⟧) = G * V ∧ constantCoeff V = coeff 1 W := by
  obtain ⟨W', rfl⟩ := PowerSeries.X_dvd_iff.mpr hW
  have hs := HasSubst.of_constantCoeff_zero' hG
  refine ⟨subst G W', ?_, ?_⟩
  · rw [← coe_substAlgHom hs, map_mul, coe_substAlgHom hs, subst_X hs]
  · rw [constantCoeff_subst_of_constantCoeff_eq_zero hG, ← coeff_zero_eq_constantCoeff_apply,
      ← coeff_succ_X_mul]

end Series

section Iterates

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

theorem ltPolyIter_succ_eq_mul (π : 𝒪[K]) (k : ℕ) :
    ltPolyIter π (k + 1) = ltPolyIter π k * ltEisenstein π k := by
  have hq := one_lt_card_residueField' K
  rw [ltPolyIter_succ, ltPoly, ltEisenstein, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.X_pow_comp, mul_add, ← pow_succ',
    Nat.sub_add_cancel hq.le]
  ring

variable (hπ : Irreducible π)

theorem coe_ltPolyIter (k : ℕ) :
    ((ltPolyIter π k : Polynomial 𝒪[K]) : 𝒪[K]⟦X⟧) =
      (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
        (π ^ k)).toPowerSeries := by
  induction k with
  | zero =>
    rw [pow_zero, lubinTateHom_self_one, Hom.toPowerSeries_id, ltPolyIter_zero, Polynomial.coe_X]
  | succ k ih =>
    rw [ltPolyIter_succ, coe_comp_eq_subst _ _ (coeff_zero_ltPolyIter π k), ih, pow_succ',
      lubinTateHom_mul hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
        (isLubinTateSeries_ltPoly π), Hom.toPowerSeries_comp, lubinTateHom_self_uniformizer]

variable (B : Type*) [CommRing B] [Algebra 𝒪[K] B]

def ltSeries (a : 𝒪[K]) : B⟦X⟧ :=
  PowerSeries.map (algebraMap 𝒪[K] B)
    (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) a).toPowerSeries

variable {B}

theorem constantCoeff_ltSeries (a : 𝒪[K]) : constantCoeff (ltSeries hπ B a) = 0 := by
  rw [ltSeries, powerSeries_constantCoeff_map, Hom.constantCoeff_eq_zero, map_zero]

theorem coeff_one_ltSeries (a : 𝒪[K]) : coeff 1 (ltSeries hπ B a) = algebraMap 𝒪[K] B a := by
  rw [ltSeries, coeff_map, coeff_one_lubinTateHom]

theorem subst_ltSeries (a b : 𝒪[K]) :
    (subst (ltSeries hπ B b) (ltSeries hπ B a) : B⟦X⟧) = ltSeries hπ B (a * b) := by
  rw [ltSeries, ltSeries, ltSeries, lubinTateHom_mul hπ (isLubinTateSeries_ltPoly π)
    (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π), Hom.toPowerSeries_comp]
  exact (map_subst (HasSubst.of_constantCoeff_zero' (Hom.constantCoeff_eq_zero _)) _).symm

theorem map_ltSeries (φ : B →ₐ[𝒪[K]] B) (a : 𝒪[K]) :
    PowerSeries.map (φ : B →+* B) (ltSeries hπ B a) = ltSeries hπ B a :=
  powerSeries_map_sigma_map_algebraMap φ _

theorem ltSeries_one : ltSeries hπ B 1 = X := by
  rw [ltSeries, lubinTateHom_self_one, Hom.toPowerSeries_id, map_X]

theorem ltSeries_uniformizer_pow (k : ℕ) :
    ltSeries hπ B (π ^ k) = (((ltPolyIter π k).map (algebraMap 𝒪[K] B) : Polynomial B) : B⟦X⟧) := by
  rw [ltSeries, ← coe_ltPolyIter hπ, map_coe_polynomial]

end Iterates

section Root

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π)
  {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
  (hunr : (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] B) = maximalIdeal B)

variable (π B) in

abbrev ltEisB (m : ℕ) : Polynomial B :=
  (ltEisenstein π m).map (algebraMap 𝒪[K] B)

variable (π B) in
omit [IsDomain B] [IsDiscreteValuationRing B] in
theorem monic_ltEisB (m : ℕ) : (ltEisB π B m).Monic :=
  (ltEisenstein_monic π m).1.map _

omit [IsDomain B] [IsDiscreteValuationRing B] in
theorem ltEisB_eq (m : ℕ) :
    ltEisB π B m = Polynomial.C (algebraMap 𝒪[K] B π) +
      ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) ^ (Nat.card 𝓀[K] - 1) := by
  rw [ltEisB, ltEisenstein, Polynomial.map_add, Polynomial.map_C, Polynomial.map_pow]

include hπ hunr in

theorem isDistinguishedAt_ltEisB (m : ℕ) : (ltEisB π B m).IsDistinguishedAt (maximalIdeal B) := by
  have hmon := (ltEisenstein_monic π m).1
  refine ⟨⟨fun {n} hn => ?_⟩, hmon.map _⟩
  rw [hmon.natDegree_map] at hn
  rw [Polynomial.coeff_map, ← hunr]
  exact Ideal.mem_map_of_mem _ ((isEisensteinAt_ltEisenstein hπ m).mem hn)

include hπ hunr in

theorem algebraMap_uniformizer_mul_eq_zero {c : B} (h : algebraMap 𝒪[K] B π * c = 0) : c = 0 := by
  have hπB := irreducible_algebraMap hunr hπ
  exact (mul_eq_zero.mp h).resolve_left hπB.ne_zero

end Root

section Coordinates

variable {B : Type*} [CommRing B] {P : Polynomial B}

theorem repr_ringHom_eq (T : AdjoinRoot P →+* AdjoinRoot P) (ψ : B → B)
    (hof : ∀ b : B, T (AdjoinRoot.of P b) = AdjoinRoot.of P (ψ b))
    (hroot : T (AdjoinRoot.root P) = AdjoinRoot.root P) (pb : PowerBasis B (AdjoinRoot P))
    (hgen : pb.gen = AdjoinRoot.root P) (z : AdjoinRoot P) (i : Fin pb.dim) :
    pb.basis.repr (T z) i = ψ (pb.basis.repr z i) := by
  have hTz : T z = ∑ j, ψ (pb.basis.repr z j) • pb.basis j := by
    conv_lhs => rw [← pb.basis.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, PowerBasis.coe_basis, map_pow, hgen,
      AdjoinRoot.algebraMap_eq, hof, hroot]
  rw [hTz, map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Coordinates

section Twist

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π)
  {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
  [IsAdicComplete (maximalIdeal B) B]
  (hunr : (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] B) = maximalIdeal B) (m : ℕ)

include hπ hunr

theorem rootEval_subst_ltSeries_uniformizer_pow_succ {F : B⟦X⟧} (hF : constantCoeff F = 0) :
    rootEval (isDistinguishedAt_ltEisB hπ hunr m) (subst (ltSeries hπ B (π ^ (m + 1))) F) = 0 := by
  obtain ⟨V, hV, -⟩ := exists_subst_eq_mul (constantCoeff_ltSeries hπ (π ^ (m + 1))) hF
  rw [hV, map_mul, ltSeries_uniformizer_pow, ltPolyIter_succ_eq_mul, Polynomial.map_mul,
    Polynomial.coe_mul, map_mul, rootEval_self, mul_zero, zero_mul]

omit hπ hunr [IsDomain B] [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] in

theorem aeval_root_ltPolyIter_pow :
    Polynomial.aeval (AdjoinRoot.root (ltEisB π B m)) ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) ^ (Nat.card 𝓀[K] - 1) =
      AdjoinRoot.of (ltEisB π B m) (-algebraMap 𝒪[K] B π) := by
  have h : Polynomial.aeval (AdjoinRoot.root (ltEisB π B m))
      (Polynomial.C (algebraMap 𝒪[K] B π) +
        ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) ^ (Nat.card 𝓀[K] - 1)) = 0 := by
    rw [← ltEisB_eq, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [map_add, Polynomial.aeval_C, map_pow] at h
  rw [map_neg, eq_neg_of_add_eq_zero_right h]
  rfl

omit [IsAdicComplete (maximalIdeal B) B] in

theorem eq_zero_of_aeval_root_ltPolyIter_mul {z : AdjoinRoot (ltEisB π B m)}
    (h : Polynomial.aeval (AdjoinRoot.root (ltEisB π B m)) ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) * z = 0) : z = 0 := by
  have hq := one_lt_card_residueField' K
  refine eq_zero_of_mul_eq_zero_of_pow_eq (monic_ltEisB π B m)
    (b := -algebraMap 𝒪[K] B π) (fun c hc => ?_) (by omega)
    (aeval_root_ltPolyIter_pow m) h
  rw [neg_mul, neg_eq_zero] at hc
  exact algebraMap_uniformizer_mul_eq_zero hπ hunr hc

theorem eq_zero_of_rootEval_subst_mul {W : B⟦X⟧} (hW : constantCoeff W = 0)
    (hW1 : IsUnit (coeff 1 W)) {z : AdjoinRoot (ltEisB π B m)}
    (h : rootEval (isDistinguishedAt_ltEisB hπ hunr m) (subst (ltSeries hπ B (π ^ m)) W) * z = 0) : z = 0 := by
  obtain ⟨V, hV, hV0⟩ := exists_subst_eq_mul (constantCoeff_ltSeries hπ (π ^ m)) hW
  rw [hV, map_mul, ltSeries_uniformizer_pow, rootEval_coe, ← AdjoinRoot.aeval_eq] at h
  have hu : IsUnit (rootEval (isDistinguishedAt_ltEisB hπ hunr m) V) := isUnit_rootEval _ (hV0 ▸ hW1)
  have h' := eq_zero_of_aeval_root_ltPolyIter_mul hπ hunr m (z := rootEval (isDistinguishedAt_ltEisB hπ hunr m) V * z) (by rw [← mul_assoc, h])
  exact (hu.mul_right_eq_zero).mp h'

theorem aeval_rootEval_ltSeries_eq_zero {a : 𝒪[K]} (ha : IsUnit a) :
    Polynomial.aeval (rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B a)) (ltEisB π B m) = 0 := by
  have hs := constantCoeff_ltSeries (B := B) hπ a
  have h1 : Polynomial.aeval (rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B a))
      ((ltPolyIter π (m + 1)).map (algebraMap 𝒪[K] B)) = 0 := by
    rw [← rootEval_subst_coe _ hs, ← ltSeries_uniformizer_pow hπ, subst_ltSeries, mul_comm,
      ← subst_ltSeries]
    exact rootEval_subst_ltSeries_uniformizer_pow_succ hπ hunr m hs
  have h2 : Polynomial.aeval (rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B a)) ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) =
      rootEval (isDistinguishedAt_ltEisB hπ hunr m) (subst (ltSeries hπ B (π ^ m)) (ltSeries hπ B a)) := by
    rw [← rootEval_subst_coe _ hs, ← ltSeries_uniformizer_pow hπ, subst_ltSeries, subst_ltSeries,
      mul_comm]
  rw [ltPolyIter_succ_eq_mul, Polynomial.map_mul, map_mul, h2] at h1
  exact eq_zero_of_rootEval_subst_mul hπ hunr m (constantCoeff_ltSeries hπ a)
    (by rw [coeff_one_ltSeries]; exact ha.map _) h1

omit hπ hunr [IsDomain B] [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] in

theorem map_map_ltEisB (φ : B →ₐ[𝒪[K]] B) :
    (ltEisB π B m).map (φ : B →+* B) = ltEisB π B m := by
  rw [ltEisB, Polynomial.map_map, AlgHom.comp_algebraMap_of_tower]

variable (φ : B →ₐ[𝒪[K]] B) (u : 𝒪[K]ˣ)

def twistFrob : AdjoinRoot (ltEisB π B m) →+* AdjoinRoot (ltEisB π B m) :=
  AdjoinRoot.lift ((AdjoinRoot.of (ltEisB π B m)).comp (φ : B →+* B)) (rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])))
    (by
      rw [← Polynomial.eval₂_map, map_map_ltEisB (K := K) (π := π) m φ]
      exact aeval_rootEval_ltSeries_eq_zero hπ hunr m (Units.isUnit _))

theorem twistFrob_of (b : B) :
    twistFrob hπ hunr m φ u (AdjoinRoot.of (ltEisB π B m) b) = AdjoinRoot.of (ltEisB π B m) (φ b) :=
  AdjoinRoot.lift_of _

theorem twistFrob_root :
    twistFrob hπ hunr m φ u (AdjoinRoot.root (ltEisB π B m)) = rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])) :=
  AdjoinRoot.lift_root _

theorem twistFrob_rootEval (F : B⟦X⟧) :
    twistFrob hπ hunr m φ u (rootEval (isDistinguishedAt_ltEisB hπ hunr m) F) =
      rootEval (isDistinguishedAt_ltEisB hπ hunr m) (subst (ltSeries hπ B ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])) (PowerSeries.map (φ : B →+* B) F)) := by
  have hs := HasSubst.of_constantCoeff_zero'
    (constantCoeff_ltSeries (B := B) hπ ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]))
  have key : (twistFrob hπ hunr m φ u).comp (rootEval (isDistinguishedAt_ltEisB hπ hunr m) : B⟦X⟧ →ₐ[B] AdjoinRoot (ltEisB π B m)).toRingHom =
      (rootEval (isDistinguishedAt_ltEisB hπ hunr m) : B⟦X⟧ →ₐ[B] AdjoinRoot (ltEisB π B m)).toRingHom.comp
        ((substAlgHom hs : B⟦X⟧ →ₐ[B] B⟦X⟧).toRingHom.comp (PowerSeries.map (φ : B →+* B))) := by
    refine rootEval_ringHom_ext (isDistinguishedAt_ltEisB hπ hunr m)
      (fun b => ?_) ?_ ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rootEval_C,
        twistFrob_of, map_C, coe_substAlgHom, subst_C]
      exact (rootEval_C _ (φ b)).symm
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rootEval_X,
        twistFrob_root, map_X, coe_substAlgHom, subst_X hs]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rootEval_X,
        twistFrob_root]
      exact rootEval_mem_span_root _ (constantCoeff_ltSeries hπ _)
  have := congrArg (fun Φ : B⟦X⟧ →+* AdjoinRoot (ltEisB π B m) => Φ F) key
  simpa [coe_substAlgHom] using this

theorem twistFrob_iterate_root (k : ℕ) :
    (twistFrob hπ hunr m φ u)^[k] (AdjoinRoot.root (ltEisB π B m)) = rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ k)) := by
  induction k with
  | zero => rw [Function.iterate_zero, id, pow_zero, ltSeries_one, rootEval_X]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, twistFrob_rootEval, map_ltSeries, subst_ltSeries,
      pow_succ]

theorem twistFrob_iterate_of (k : ℕ) (b : B) :
    (twistFrob hπ hunr m φ u)^[k] (AdjoinRoot.of (ltEisB π B m) b) = AdjoinRoot.of (ltEisB π B m) ((⇑φ)^[k] b) := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, twistFrob_of, ih, ← Function.iterate_succ_apply]

theorem repr_twistFrob_iterate {N : ℕ} (hN : (twistFrob hπ hunr m φ u)^[N] (AdjoinRoot.root (ltEisB π B m)) =
      AdjoinRoot.root (ltEisB π B m))
    (z : AdjoinRoot (ltEisB π B m)) (i : Fin (AdjoinRoot.powerBasis' (monic_ltEisB π B m)).dim) :
    (AdjoinRoot.powerBasis' (monic_ltEisB π B m)).basis.repr
        ((twistFrob hπ hunr m φ u)^[N] z) i =
      (⇑φ)^[N] ((AdjoinRoot.powerBasis' (monic_ltEisB π B m)).basis.repr z i) := by
  have hTc : ⇑(twistFrob hπ hunr m φ u ^ N) = (twistFrob hπ hunr m φ u)^[N] := RingHom.coe_pow _ N
  have h := repr_ringHom_eq (twistFrob hπ hunr m φ u ^ N) ((⇑φ)^[N])
    (fun b => by rw [hTc, twistFrob_iterate_of]) (by rw [hTc, hN])
    (AdjoinRoot.powerBasis' (monic_ltEisB π B m)) (AdjoinRoot.powerBasis'_gen _) z i
  rwa [hTc] at h

end Twist

section Theta

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π)
  {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
  [IsAdicComplete (maximalIdeal B) B] [IsAlgClosed (ResidueField B)]
  (hunr : (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] B) = maximalIdeal B) (m : ℕ)
  (φ : B →ₐ[𝒪[K]] B) (hφ : ∀ x : B, residue B (φ x) = residue B x ^ Nat.card 𝓀[K])
  (u : 𝒪[K]ˣ)

include hφ in

theorem exists_twistFrob_fixed_root :
    ∃ x : AdjoinRoot (ltEisB π B m), twistFrob hπ hunr m φ u x = x ∧
      Polynomial.aeval x (ltEisB ((u : 𝒪[K]) * π) B m) = 0 := by
  have hπ' : Irreducible ((u : 𝒪[K]) * π) := (irreducible_units_mul u).2 hπ
  obtain ⟨θ, hθ1, -, hθφ, hθcomm, -⟩ := exists_iso_lubinTateFormalGroup hunr φ hφ hπ u
    (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly ((u : 𝒪[K]) * π))
  set t := θ.hom.toPowerSeries with ht
  have ht0 : constantCoeff t = 0 := θ.hom.constantCoeff_eq_zero
  have hmap : PowerSeries.map (φ : B →+* B) t = subst (ltSeries hπ B (u : 𝒪[K])) t := hθφ
  have hcomm : ∀ a : 𝒪[K], (subst (ltSeries hπ B a) t : B⟦X⟧) = subst t (ltSeries hπ' B a) :=
    fun a => congrArg Hom.toPowerSeries (hθcomm a)
  have hs : ∀ a : 𝒪[K], HasSubst (ltSeries hπ B a) := fun a =>
    HasSubst.of_constantCoeff_zero' (constantCoeff_ltSeries hπ a)
  have hsub0 : ∀ a : 𝒪[K], constantCoeff (subst (ltSeries hπ B a) t : B⟦X⟧) = 0 := fun a => by
    rw [constantCoeff_subst_of_constantCoeff_eq_zero (constantCoeff_ltSeries hπ a), ht0]

  have hval : ∀ k : ℕ, Polynomial.aeval (rootEval (isDistinguishedAt_ltEisB hπ hunr m) t)
      ((ltPolyIter ((u : 𝒪[K]) * π) k).map (algebraMap 𝒪[K] B)) =
      rootEval (isDistinguishedAt_ltEisB hπ hunr m)
        (subst (ltSeries hπ B (π ^ k)) (subst (ltSeries hπ B ((u : 𝒪[K]) ^ k)) t)) := by
    intro k
    rw [← rootEval_subst_coe _ ht0, ← ltSeries_uniformizer_pow hπ', ← hcomm, mul_pow,
      ← subst_ltSeries, subst_comp_subst_apply (hs _) (hs _)]
  refine ⟨rootEval (isDistinguishedAt_ltEisB hπ hunr m) t, ?_, ?_⟩
  · rw [twistFrob_rootEval, hmap, subst_comp_subst_apply (hs _) (hs _), subst_ltSeries,
      Units.mul_inv, ltSeries_one, X_subst]
  · have h1 := hval (m + 1)
    rw [rootEval_subst_ltSeries_uniformizer_pow_succ hπ hunr m (hsub0 _), ltPolyIter_succ_eq_mul,
      Polynomial.map_mul, map_mul, hval m] at h1
    refine eq_zero_of_rootEval_subst_mul hπ hunr m (hsub0 _) ?_ h1
    rw [coeff_one_subst ht0 (constantCoeff_ltSeries hπ _), coeff_one_ltSeries]
    exact hθ1.mul ((u.isUnit.pow m).map _)

end Theta

end GroundTheory.LocalField
end
end

section
noncomputable section

open PowerSeries IsLocalRing ValuativeRel GroundTheory.LocalField.FormalGroup
open scoped Topology

namespace GroundTheory.LocalField

section PsEval

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem psEval_add' {σ : Type*} [Finite σ] (F G : MvPowerSeries σ 𝒪[K]) (x : σ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (F + G) x = psEval F x + psEval G x := by
  have := t2Space_of_isValuativeTopology Ω
  have h := (hasSum_psEval' F x hx).add (hasSum_psEval' G x hx)
  have e : (fun d => psTerm F x d + psTerm G x d) = psTerm (F + G) x := by
    funext d
    simp [psTerm, add_mul]
  rw [e] at h
  exact h.tsum_eq

theorem psEval_mul' {σ : Type*} [Finite σ] (F G : MvPowerSeries σ 𝒪[K]) (x : σ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (F * G) x = psEval F x * psEval G x := by
  let E := IntermediateField.adjoin K (Set.range x)
  have := finiteDimensional_adjoin_range (K := K) x
  let xE : σ → E := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  let a : σ → 𝒪[E] := fun i => ⟨xE i, ((valuation_coe_lt_one_iff E (xE i)).mp (hx i)).le⟩
  have ha : ∀ i, a i ∈ 𝓂[E] := fun i =>
    mem_maximalIdeal_integer_iff.mpr ((valuation_coe_lt_one_iff E (xE i)).mp (hx i))
  have h1 : psEval (F * G) x = _ := psEval_coe E (F * G) xE hx
  have h2 : psEval F x = _ := psEval_coe E F xE hx
  have h3 : psEval G x = _ := psEval_coe E G xE hx
  rw [h1, h2, h3]
  change ((psEval (F * G) fun i => (a i : E) : E) : Ω) =
    ((psEval F fun i => (a i : E) : E) : Ω) * ((psEval G fun i => (a i : E) : E) : Ω)
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have _ : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace 𝒪[K] := ⊥
  have _ : DiscreteUniformity 𝒪[K] := ⟨rfl⟩
  have hφ : Continuous[(⊥ : UniformSpace 𝒪[K]).toTopologicalSpace, _]
      (algebraMap 𝒪[K] 𝒪[E]) := by
    rw [UniformSpace.toTopologicalSpace_bot]
    exact continuous_bot
  rw [psEval_eq_eval₂ _ a ha, psEval_eq_eval₂ _ a ha, psEval_eq_eval₂ _ a ha,
    ← MvPowerSeries.coe_eval₂Hom hφ (hasEval_of_mem_maximalIdeal ha), map_mul]
  push_cast
  rfl

theorem psEval_eq_aeval_of_sub_mem {P h : Polynomial 𝒪[K]} {G : 𝒪[K]⟦X⟧}
    (hG : G - (h : 𝒪[K]⟦X⟧) ∈ Ideal.span {(P : 𝒪[K]⟦X⟧)}) {x : Ω} (hx : valuation Ω x < 1)
    (hP : Polynomial.aeval x (P.map (algebraMap 𝒪[K] K)) = 0) :
    psEval G (fun _ => x) = Polynomial.aeval x (h.map (algebraMap 𝒪[K] K)) := by
  have := t2Space_of_isValuativeTopology Ω
  obtain ⟨D, hD⟩ := Ideal.mem_span_singleton'.mp hG
  have hGe : G = (h : 𝒪[K]⟦X⟧) + D * (P : 𝒪[K]⟦X⟧) := by rw [hD]; ring
  rw [hGe, psEval_add' _ _ _ fun _ => hx, psEval_mul' _ _ _ fun _ => hx, psEval_polynomial,
    psEval_polynomial, hP, mul_zero, add_zero]

end PsEval

section Weierstrass

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π) (m : ℕ)

include hπ in

theorem isDistinguishedAt_ltEisenstein : (ltEisenstein π m).IsDistinguishedAt 𝓂[K] :=
  ⟨⟨fun hn => (isEisensteinAt_ltEisenstein hπ m).mem hn⟩, (ltEisenstein_monic π m).1⟩

include hπ in

theorem exists_sub_coe_mem_span_ltEisenstein (G : 𝒪[K]⟦X⟧) :
    ∃ h : Polynomial 𝒪[K], G - (h : 𝒪[K]⟦X⟧) ∈ Ideal.span {((ltEisenstein π m : Polynomial 𝒪[K]) :
      𝒪[K]⟦X⟧)} := by
  have := isAdicComplete_integer K
  have hP := isDistinguishedAt_ltEisenstein hπ m
  obtain ⟨h, hh⟩ := AdjoinRoot.mk_surjective (rootEval hP G)
  exact ⟨h, (rootEval_eq_rootEval_iff hP G h).mp (by rw [rootEval_coe, hh])⟩

variable {L : Type*} [Field L] [Algebra K L]

include hπ in

theorem ltEisenstein_dvd_of_aeval_eq_zero {x : L}
    (hx : Polynomial.aeval x ((ltEisenstein π m).map (algebraMap 𝒪[K] K)) = 0) {p : Polynomial 𝒪[K]}
    (hp : Polynomial.aeval x (p.map (algebraMap 𝒪[K] K)) = 0) : ltEisenstein π m ∣ p := by
  have hmon := (ltEisenstein_monic π m).1
  have hq := one_lt_card_residueField' K
  have hdeg : 0 < (ltEisenstein π m).natDegree := by
    rw [(ltEisenstein_monic π m).2]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) m)
  have hirr := irreducible_map_of_isEisensteinAt (isEisensteinAt_ltEisenstein hπ m) hdeg
  have hint : IsIntegral K x := ⟨_, hmon.map _, hx⟩
  have hmin : minpoly K x = (ltEisenstein π m).map (algebraMap 𝒪[K] K) :=
    (minpoly.eq_of_irreducible_of_monic hirr hx (hmon.map _)).symm
  have hdvd : (ltEisenstein π m).map (algebraMap 𝒪[K] K) ∣ p.map (algebraMap 𝒪[K] K) :=
    hmin ▸ minpoly.dvd K x hp
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hmon]
  apply Polynomial.map_injective (algebraMap 𝒪[K] K) (IsFractionRing.injective 𝒪[K] K)
  rw [Polynomial.map_modByMonic _ hmon, Polynomial.map_zero,
    Polynomial.modByMonic_eq_zero_iff_dvd (hmon.map _)]
  exact hdvd

end Weierstrass

section Iterate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π)

theorem pow_apply_eq_psEval (σ : Ω ≃ₐ[K] Ω) (a : 𝒪[K]) {x : Ω} (hx : valuation Ω x < 1)
    (hσ : σ x = psEval (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
      a).toPowerSeries fun _ => x) (k : ℕ) :
    (σ ^ k) x = psEval (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
      (a ^ k)).toPowerSeries fun _ => x := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, lubinTateHom_self_one, Hom.toPowerSeries_id, AlgEquiv.one_apply]
    exact (psEval_X (K := K) (fun _ : Unit => x) ()).symm
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, algEquiv_psEval σ _ _ fun _ => hx, hσ, pow_succ,
      lubinTateHom_mul hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
        (isLubinTateSeries_ltPoly π), Hom.toPowerSeries_comp, PowerSeries.subst_def,
      psEval_subst' (fun _ => Hom.constantCoeff_eq_zero' _) _ _ fun _ => hx]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in

theorem exists_pow_apply_eq_self (σ : Ω ≃ₐ[K] Ω) {p : Polynomial K} (hp : p ≠ 0) {x : Ω}
    (hx : Polynomial.aeval x p = 0) : ∃ N : ℕ, 0 < N ∧ (σ ^ N) x = x :=
  _root_.GroundTheory.Variant₂.N1.exists_pow_apply_eq_self_of_aeval_eq_zero σ hp hx

end Iterate

section Maps

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {B : Type*} [CommRing B] [Algebra 𝒪[K] B]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem map_sub_coe_mem_span {P h : Polynomial 𝒪[K]} {G : 𝒪[K]⟦X⟧}
    (hG : G - (h : 𝒪[K]⟦X⟧) ∈ Ideal.span {(P : 𝒪[K]⟦X⟧)}) :
    PowerSeries.map (algebraMap 𝒪[K] B) G - ((h.map (algebraMap 𝒪[K] B) : Polynomial B) : B⟦X⟧) ∈
      Ideal.span {((P.map (algebraMap 𝒪[K] B) : Polynomial B) : B⟦X⟧)} := by
  have := Ideal.mem_map_of_mem (PowerSeries.map (algebraMap 𝒪[K] B)) hG
  rwa [Ideal.map_span, Set.image_singleton, map_sub, map_coe_polynomial, map_coe_polynomial] at this

theorem adjoinRoot_ringHom_ext {R S : Type*} [CommRing R] [CommRing S] {p : Polynomial R}
    {f g : AdjoinRoot p →+* S} (hof : ∀ r : R, f (AdjoinRoot.of p r) = g (AdjoinRoot.of p r))
    (hroot : f (AdjoinRoot.root p) = g (AdjoinRoot.root p)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro r
    exact hof r
  · exact hroot

end Maps

section Unramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω]

theorem apply_coe_eq_frobenius (σ : Ω ≃ₐ[K] Ω) (hσ : unramifiedDegree K Ω σ = Multiplicative.ofAdd 1)
    {L : IntermediateField K Ω} (hL : IsUnramifiedSubextension L) (y : L) :
    letI := hL.1
    σ (y : Ω) = ((frobenius K L hL.ramificationIndex_eq_one y : L) : Ω) := by
  have := hL.1
  have hr := (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff σ).mpr hσ
  rw [← maximalUnramifiedExtensionFrobenius_inclusion hL y, ← hr]
  exact (AlgEquiv.restrictNormal_commutes σ (maximalUnramifiedExtension K Ω)
    (IntermediateField.inclusion hL.le_maximalUnramifiedExtension y)).symm

theorem completedFrobenius_iterate_integerToCompleted {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) (k : ℕ) (c : 𝒪[L]) :
    letI := hL.1
    (completedFrobenius K Ω)^[k] (integerToCompleted K Ω hL.le_maximalUnramifiedExtension c) =
      integerToCompleted K Ω hL.le_maximalUnramifiedExtension
        (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one ^ k) c) := by
  have := hL.1
  induction k with
  | zero => rw [Function.iterate_zero, id, pow_zero, map_one, AlgEquiv.one_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, completedFrobenius_integerToCompleted hL, pow_succ',
      map_mul, AlgEquiv.mul_apply]

theorem residue_completedFrobenius_iterate (k : ℕ) (x : CompletedUnramifiedIntegers K Ω) :
    residue _ ((completedFrobenius K Ω)^[k] x) = residue _ x ^ (Nat.card 𝓀[K] ^ k) := by
  induction k with
  | zero => rw [Function.iterate_zero, id, pow_zero, pow_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', residue_completedFrobenius, ih, ← pow_mul, ← pow_succ]

theorem exists_integerToCompleted_eq_of_iterate {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) {b : CompletedUnramifiedIntegers K Ω}
    (hb : (completedFrobenius K Ω)^[Module.finrank K L] b = b) :
    ∃ c : 𝒪[L], integerToCompleted K Ω hL.le_maximalUnramifiedExtension c = b := by
  have := hL.1
  have h := hL.ramificationIndex_eq_one
  have := isAdicComplete_integer L
  set ι := integerToCompleted K Ω hL.le_maximalUnramifiedExtension with hι
  let _ : Algebra 𝒪[L] (CompletedUnramifiedIntegers K Ω) := ι.toRingHom.toAlgebra
  have hιa : ∀ c : 𝒪[L], algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω) c = ι c := fun _ => rfl
  set N := Module.finrank K L with hN
  have hfrobN : frobenius K L h ^ N = 1 := by
    rw [hN, ← orderOf_frobenius K L h]
    exact pow_orderOf_eq_one _
  let T : CompletedUnramifiedIntegers K Ω →+* CompletedUnramifiedIntegers K Ω :=
    (completedFrobenius K Ω).toAlgHom.toRingHom ^ N
  have hT : ∀ x, T x = (completedFrobenius K Ω)^[N] x := fun x => by
    rw [RingHom.coe_pow]
    rfl
  have hTc : ∀ c : 𝒪[L], T (algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω) c) =
      algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω) c := fun c => by
    rw [hT, hιa, hι, completedFrobenius_iterate_integerToCompleted hL, hfrobN, map_one,
      AlgEquiv.one_apply]
  let σN : CompletedUnramifiedIntegers K Ω →ₐ[𝒪[L]] CompletedUnramifiedIntegers K Ω :=
    { toRingHom := T, commutes' := hTc }
  have hσN : ∀ x, σN x = (completedFrobenius K Ω)^[N] x := hT
  have hres : ∀ x, residue _ (σN x) = residue _ x ^ Nat.card (ResidueField 𝒪[L]) := fun x => by
    rw [hσN, residue_completedFrobenius_iterate, card_residueField_of_unramified K L h]
  have hunrL : (maximalIdeal 𝒪[L]).map (algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω)) =
      maximalIdeal (CompletedUnramifiedIntegers K Ω) := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) ?_
    · rw [Ideal.mem_comap, hιa, hι, integerToCompleted_apply, mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal x).mp hx (isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ hu))
    · rw [← map_maximalIdeal_completedUnramifiedIntegers K Ω]
      have hcomp : algebraMap 𝒪[K] (CompletedUnramifiedIntegers K Ω) =
          (algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω)).comp (algebraMap 𝒪[K] 𝒪[L]) :=
        (ι.comp_algebraMap).symm
      rw [hcomp, ← Ideal.map_map]
      exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr fun x hx =>
        map_nonunit (algebraMap 𝒪[K] 𝒪[L]) x hx)
  obtain ⟨c, hc⟩ := (mem_range_algebraMap_iff_fixed hunrL σN hres b).mpr (by rw [hσN]; exact hb)
  exact ⟨c, hc⟩

end Unramified

section Descent

variable {R : Type*} [CommRing R]

theorem eval₂_of_mk (f p q : Polynomial R) :
    Polynomial.eval₂ (AdjoinRoot.of f) (AdjoinRoot.mk f q) p = AdjoinRoot.mk f (p.comp q) :=
  (Polynomial.hom_eval₂ p Polynomial.C (AdjoinRoot.mk f) q).symm

theorem adjoinRoot_map_mk {S : Type*} [CommRing S] (ι : R →+* S) (p : Polynomial R) (q : Polynomial S)
    (h : q ∣ p.map ι) (g : Polynomial R) :
    AdjoinRoot.map ι p q h (AdjoinRoot.mk p g) = AdjoinRoot.mk q (g.map ι) := by
  have key : (AdjoinRoot.map ι p q h).comp (AdjoinRoot.mk p) =
      (AdjoinRoot.mk q).comp (Polynomial.mapRingHom ι) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp
    · simp
  exact congrArg (fun F : Polynomial R →+* AdjoinRoot q => F g) key

theorem adjoinRoot_map_injective {S : Type*} [CommRing S] {ι : R →+* S} (hι : Function.Injective ι)
    {p : Polynomial R} (hp : p.Monic) {q : Polynomial S} (hq : q ∣ p.map ι) (hpq : p.map ι = q) :
    Function.Injective (AdjoinRoot.map ι p q hq) := by
  subst hpq
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective w
  rw [adjoinRoot_map_mk, AdjoinRoot.mk_eq_zero, ← Polynomial.modByMonic_eq_zero_iff_dvd (hp.map ι),
    ← Polynomial.map_modByMonic ι hp] at hw
  rw [AdjoinRoot.mk_eq_zero, ← Polynomial.modByMonic_eq_zero_iff_dvd hp]
  exact Polynomial.map_injective ι hι (by rw [hw, Polynomial.map_zero])

theorem exists_adjoinRoot_twist (p : Polynomial R) (ψ : R →+* R) (hψ : p.map ψ = p) (g : Polynomial R)
    (hg : p ∣ p.comp g) :
    ∃ τ : AdjoinRoot p →+* AdjoinRoot p, (∀ c, τ (AdjoinRoot.of p c) = AdjoinRoot.of p (ψ c)) ∧
      τ (AdjoinRoot.root p) = AdjoinRoot.mk p g := by
  refine ⟨AdjoinRoot.lift ((AdjoinRoot.of p).comp ψ) (AdjoinRoot.mk p g) ?_,
    fun c => AdjoinRoot.lift_of _, AdjoinRoot.lift_root _⟩
  rw [← Polynomial.eval₂_map, hψ, eval₂_of_mk, AdjoinRoot.mk_eq_zero]
  exact hg

theorem exists_adjoinRoot_lift {S : Type*} [CommRing S] (p : Polynomial R) (jc : R →+* S) (x : S)
    (hx : p.eval₂ jc x = 0) :
    ∃ j : AdjoinRoot p →+* S, (∀ c, j (AdjoinRoot.of p c) = jc c) ∧ j (AdjoinRoot.root p) = x ∧
      ∀ g, j (AdjoinRoot.mk p g) = g.eval₂ jc x :=
  ⟨AdjoinRoot.lift jc x hx, fun _ => AdjoinRoot.lift_of _, AdjoinRoot.lift_root _,
    fun _ => AdjoinRoot.lift_mk _ _⟩

theorem exists_adjoinRoot_map_eq {S : Type*} [CommRing S] (ι : R →+* S) (p : Polynomial R)
    {q : Polynomial S} (hq : q ∣ p.map ι) (hqm : q.Monic) (z : AdjoinRoot q)
    (d : Fin (AdjoinRoot.powerBasis' hqm).dim → R)
    (hd : ∀ i, ι (d i) = (AdjoinRoot.powerBasis' hqm).basis.repr z i) :
    ∃ y : AdjoinRoot p, AdjoinRoot.map ι p q hq y = z := by
  refine ⟨∑ i, AdjoinRoot.of p (d i) * AdjoinRoot.root p ^ (i : ℕ), ?_⟩
  conv_rhs => rw [← (AdjoinRoot.powerBasis' hqm).basis.sum_repr z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, AdjoinRoot.map_of, AdjoinRoot.map_root, hd, Algebra.smul_def,
    PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen, AdjoinRoot.algebraMap_eq]

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) (u : 𝒪[K]ˣ) (m : ℕ)

set_option maxHeartbeats 1000000 in
include hπ in

theorem exists_fixed_root_ltEisenstein (σ : Ω ≃ₐ[K] Ω)
    (hσ : unramifiedDegree K Ω σ = Multiplicative.ofAdd 1) {l : Ω}
    (hl : Polynomial.aeval l ((ltEisenstein π m).map (algebraMap 𝒪[K] K)) = 0)
    (hσl : σ l = psEval (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
      ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])).toPowerSeries fun _ => l) :
    ∃ x : Ω, Polynomial.aeval x ((ltEisenstein ((u : 𝒪[K]) * π) m).map (algebraMap 𝒪[K] K)) = 0 ∧
      σ x = x ∧ ∀ τ : Ω ≃ₐ[K] Ω, (∀ y ∈ maximalUnramifiedExtension K Ω, τ y = y) → τ l = l →
        τ x = x := by
  classical
  have hPmon : (ltEisenstein π m).Monic := (ltEisenstein_monic π m).1

  have hlv : valuation Ω l < 1 := by
    refine valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ (m + 1) ?_
    rw [ltPolyIter_succ_eq_mul, Polynomial.map_mul, map_mul, hl, mul_zero]

  obtain ⟨h, hh⟩ := exists_sub_coe_mem_span_ltEisenstein hπ m
    (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])).toPowerSeries
  have hσl' : σ l = Polynomial.aeval l (h.map (algebraMap 𝒪[K] K)) :=
    hσl.trans (psEval_eq_aeval_of_sub_mem hh hlv hl)

  obtain ⟨N, hN0, hNl⟩ := exists_pow_apply_eq_self σ ((hPmon.map (algebraMap 𝒪[K] K)).ne_zero) hl
  obtain ⟨hN', hhN'⟩ := exists_sub_coe_mem_span_ltEisenstein hπ m
    (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ N)).toPowerSeries
  have haevalN : Polynomial.aeval l (hN'.map (algebraMap 𝒪[K] K)) = l := by
    rw [← psEval_eq_aeval_of_sub_mem hhN' hlv hl, ← pow_apply_eq_psEval hπ σ _ hlv hσl N, hNl]
  have hdvdN : (ltEisenstein π m) ∣ hN' - Polynomial.X := by
    refine ltEisenstein_dvd_of_aeval_eq_zero hπ m hl ?_
    rw [Polynomial.map_sub, Polynomial.map_X, map_sub, haevalN, Polynomial.aeval_X, sub_self]
  have hGN : (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ N)).toPowerSeries -
      ((Polynomial.X : Polynomial 𝒪[K]) : 𝒪[K]⟦X⟧) ∈ Ideal.span {((ltEisenstein π m) : 𝒪[K]⟦X⟧)} := by
    obtain ⟨q, hq⟩ := hdvdN
    have e : (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ N)).toPowerSeries -
        ((Polynomial.X : Polynomial 𝒪[K]) : 𝒪[K]⟦X⟧) =
        ((lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ N)).toPowerSeries - (hN' : 𝒪[K]⟦X⟧)) +
          ((ltEisenstein π m) : 𝒪[K]⟦X⟧) * (q : 𝒪[K]⟦X⟧) := by
      rw [← Polynomial.coe_mul, ← hq, Polynomial.coe_sub]
      ring
    rw [e]
    exact add_mem hhN' (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

  have hunr := map_maximalIdeal_completedUnramifiedIntegers K Ω
  obtain ⟨z, hzfix, hzroot⟩ := exists_twistFrob_fixed_root hπ hunr m
    (completedFrobenius K Ω).toAlgHom residue_completedFrobenius u
  set T := twistFrob hπ hunr m (completedFrobenius K Ω).toAlgHom u with hT
  have hP := isDistinguishedAt_ltEisB hπ hunr m
  have hTN : T^[N] (AdjoinRoot.root (ltEisB π (CompletedUnramifiedIntegers K Ω) m)) =
      AdjoinRoot.root (ltEisB π (CompletedUnramifiedIntegers K Ω) m) := by
    rw [hT, twistFrob_iterate_root, ← rootEval_X hP, rootEval_eq_rootEval_iff]
    have := map_sub_coe_mem_span (B := CompletedUnramifiedIntegers K Ω) hGN
    rwa [Polynomial.map_X, Polynomial.coe_X] at this

  have hzN : T^[N] z = z := Function.iterate_fixed hzfix N
  obtain ⟨L, ⟨hL, hLN⟩, -⟩ := existsUnique_isUnramifiedSubextension (K := K) (Ksep := Ω) hN0.ne'
  have := hL.1
  have hcoord : ∀ i, ∃ d : 𝒪[L], integerToCompleted K Ω hL.le_maximalUnramifiedExtension d =
      (AdjoinRoot.powerBasis' (monic_ltEisB π (CompletedUnramifiedIntegers K Ω) m)).basis.repr z i :=
      fun i => by
    refine exists_integerToCompleted_eq_of_iterate hL ?_
    rw [hLN]
    have := repr_twistFrob_iterate hπ hunr m (completedFrobenius K Ω).toAlgHom u hTN z i
    rw [← hT, hzN] at this
    exact this.symm
  choose d hd using hcoord

  have hPLmap : ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])).map
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* _) =
      ltEisB π (CompletedUnramifiedIntegers K Ω) m := by
    rw [Polynomial.map_map, AlgHom.comp_algebraMap]
  have hdvd : ltEisB π (CompletedUnramifiedIntegers K Ω) m ∣ ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])).map
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* _) := hPLmap ▸ dvd_rfl
  have hιinj : Function.Injective
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* CompletedUnramifiedIntegers K Ω) :=
    integerToCompleted_injective _
  have hinj := adjoinRoot_map_injective hιinj (hPmon.map (algebraMap 𝒪[K] 𝒪[L])) hdvd hPLmap
  obtain ⟨y, hy⟩ := exists_adjoinRoot_map_eq
    (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* CompletedUnramifiedIntegers K Ω)
    ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])) hdvd (monic_ltEisB π (CompletedUnramifiedIntegers K Ω) m) z d hd
  generalize hiM : AdjoinRoot.map
    (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* CompletedUnramifiedIntegers K Ω)
    ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])) (ltEisB π (CompletedUnramifiedIntegers K Ω) m) hdvd = iM at hinj hy
  have hiMof : ∀ c : 𝒪[L], iM (AdjoinRoot.of _ c) = AdjoinRoot.of _
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension c) := fun c => by
    rw [← hiM, AdjoinRoot.map_of]
    rfl
  have hiMroot : iM (AdjoinRoot.root _) = AdjoinRoot.root _ := by
    rw [← hiM, AdjoinRoot.map_root]
  have hiMmk : ∀ g : Polynomial 𝒪[L], iM (AdjoinRoot.mk _ g) = AdjoinRoot.mk _
      (g.map (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* _)) := fun g => by
    rw [← hiM, adjoinRoot_map_mk]

  have hPcomp : (ltEisenstein π m) ∣ (ltEisenstein π m).comp h := by
    refine ltEisenstein_dvd_of_aeval_eq_zero hπ m hl ?_
    rw [Polynomial.map_comp, Polynomial.aeval_comp, ← hσl']
    have e := Polynomial.aeval_algHom_apply (σ : Ω →ₐ[K] Ω) l ((ltEisenstein π m).map (algebraMap 𝒪[K] K))
    change Polynomial.aeval (σ l) _ = 0
    rw [show ((σ : Ω →ₐ[K] Ω) l) = σ l from rfl] at e
    rw [e, hl, map_zero]
  have hfrPL : ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])).map
      (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one)).toAlgHom.toRingHom =
      (ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun c => (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one)).commutes c
  have hPcompL : (ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]) ∣
      ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])).comp (h.map (algebraMap 𝒪[K] 𝒪[L])) := by
    rw [← Polynomial.map_comp (f := algebraMap 𝒪[K] 𝒪[L])]
    exact Polynomial.map_dvd _ hPcomp
  obtain ⟨σL, hσLof, hσLroot⟩ := exists_adjoinRoot_twist ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]))
    (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one)).toAlgHom.toRingHom hfrPL
    (h.map (algebraMap 𝒪[K] 𝒪[L])) hPcompL

  have hφι : ∀ c : 𝒪[L], (completedFrobenius K Ω).toAlgHom
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension c) =
      integerToCompleted K Ω hL.le_maximalUnramifiedExtension
        ((integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one)).toAlgHom.toRingHom c) :=
    fun c => completedFrobenius_integerToCompleted hL c
  have hsq1 : iM.comp σL = T.comp iM := by
    refine adjoinRoot_ringHom_ext (fun c => ?_) ?_
    · change iM (σL _) = T (iM _)
      rw [hσLof, hiMof, hiMof, hT, twistFrob_of, hφι]
    · change iM (σL _) = T (iM _)
      rw [hσLroot, hiMmk, hiMroot, hT, twistFrob_root,
        Polynomial.map_map, AlgHom.comp_algebraMap, ← rootEval_coe hP]
      exact ((rootEval_eq_rootEval_iff hP _ _).mpr (map_sub_coe_mem_span hh)).symm

  have hσLy : σL y = y := by
    apply hinj
    change (iM.comp σL) y = iM y
    rw [hsq1]
    change T (iM y) = iM y
    rw [hy, hzfix]

  have hiMofc : iM.comp (AdjoinRoot.of ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]))) =
      (AdjoinRoot.of (ltEisB π (CompletedUnramifiedIntegers K Ω) m)).comp
        (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* _) :=
    RingHom.ext hiMof
  have hy' : Polynomial.eval₂ (AdjoinRoot.of ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]))) y
      ((ltEisenstein ((u : 𝒪[K]) * π) m).map (algebraMap 𝒪[K] 𝒪[L])) = 0 := by
    apply hinj
    rw [map_zero, Polynomial.hom_eval₂, hiMofc, hy, ← Polynomial.eval₂_map, Polynomial.map_map,
      AlgHom.comp_algebraMap]
    exact hzroot

  have hjc : ((algebraMap L Ω).comp (algebraMap 𝒪[L] L)).comp (algebraMap 𝒪[K] 𝒪[L]) =
      (algebraMap K Ω).comp (algebraMap 𝒪[K] K) := by
    refine RingHom.ext fun c => ?_
    change algebraMap L Ω (algebraMap K L (c : K)) = algebraMap K Ω (c : K)
    exact (IsScalarTower.algebraMap_apply K L Ω (c : K)).symm
  obtain ⟨j, hjof, hjroot, hjmk⟩ := exists_adjoinRoot_lift
    ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])) ((algebraMap L Ω).comp (algebraMap 𝒪[L] L)) l
    (by rw [Polynomial.eval₂_map, hjc, ← Polynomial.eval₂_map]; exact hl)
  have hjc' : j.comp (AdjoinRoot.of ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]))) =
      (algebraMap L Ω).comp (algebraMap 𝒪[L] L) := RingHom.ext hjof

  have hsq2 : (σ : Ω →+* Ω).comp j = j.comp σL := by
    refine adjoinRoot_ringHom_ext (fun c => ?_) ?_
    · change σ (j _) = j (σL _)
      rw [hσLof, hjof, hjof]
      change σ ((c : L) : Ω) = (((integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one) c :
        𝒪[L]) : L) : Ω)
      rw [coe_integerAlgEquiv_apply]
      exact apply_coe_eq_frobenius σ hσ hL (c : L)
    · change σ (j _) = j (σL _)
      rw [hσLroot, hjmk, hjroot, hσl', Polynomial.eval₂_map, hjc, ← Polynomial.eval₂_map]
      rfl
  refine ⟨j y, ?_, ?_, ?_⟩
  · change Polynomial.eval₂ (algebraMap K Ω) (j y)
      ((ltEisenstein ((u : 𝒪[K]) * π) m).map (algebraMap 𝒪[K] K)) = 0
    rw [Polynomial.eval₂_map, ← hjc, ← Polynomial.eval₂_map, ← hjc', ← Polynomial.hom_eval₂, hy',
      map_zero]
  · change ((σ : Ω →+* Ω).comp j) y = j y
    rw [hsq2]
    change j (σL y) = j y
    rw [hσLy]
  · intro τ hτ hτl
    have hτj : (τ : Ω →+* Ω).comp j = j := by
      refine adjoinRoot_ringHom_ext (fun c => ?_) ?_
      · change τ (j _) = j _
        rw [hjof]
        exact hτ _ (hL.le_maximalUnramifiedExtension (c : L).2)
      · change τ (j _) = j _
        rw [hjroot]
        exact hτl
    change ((τ : Ω →+* Ω).comp j) y = j y
    rw [hτj]

end Descent

end GroundTheory.LocalField
end
end
