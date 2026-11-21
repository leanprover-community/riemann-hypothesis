import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleMultiHomog
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleMultiHomogGrad
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def toFn (P : Ideal (MRing ι)) : MRing ι →+* FnField P :=
  (algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ker_toFn (P : Ideal (MRing ι)) : RingHom.ker (toFn P) = P := by
  rw [toFn, RingHom.ker_comp_of_injective _ (IsFractionRing.injective _ _), Ideal.mk_ker]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem evalAt_genPt (P : Ideal (MRing ι)) (f : MRing ι) : evalAt (genPt P) f = toFn P f := by
  rw [evalAt, eval_map]
  have h : eval₂Hom (Int.castRingHom (FnField P)) (genPt P) = toFn P :=
    MvPolynomial.ringHom_ext (fun z => by simp) (fun p => by simp [genPt, toFn])
  exact RingHom.congr_fun h f

def genMap (P : Ideal (MRing ι)) {N1 : ℕ} {S : Type} [Fintype S] (v : S → Fin N1 → FnField P) :
    MRing (PBlk ι N1) →+* MvPolynomial S (FnField P) :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (genPt P ⟨k, i⟩)
    | ⟨.inr _, j⟩ => ∑ s, C (v s j) * X s

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ker_genMap_le (P : Ideal (MRing ι)) {N1 : ℕ} {S S' : Type} [Fintype S] [Fintype S']
    (v : S → Fin N1 → FnField P) (v' : S' → Fin N1 → FnField P)
    (h : ∀ s', v' s' ∈ Submodule.span (FnField P) (Set.range v)) :
    RingHom.ker (genMap P v) ≤ RingHom.ker (genMap P v') := by
  choose G hG using fun s' => (Submodule.mem_span_range_iff_exists_fun (FnField P)).mp (h s')
  let σ : MvPolynomial S (FnField P) →+* MvPolynomial S' (FnField P) :=
    (aeval fun s => ∑ s', C (G s' s) * X s' : MvPolynomial S (FnField P) →ₐ[FnField P] _).toRingHom
  have key : genMap P v' = σ.comp (genMap P v) := by
    refine MvPolynomial.ringHom_ext (fun z => by simp) ?_
    rintro ⟨k | u, i⟩
    · simp [genMap, σ]
    · change Fin N1 at i
      simp only [genMap, RingHom.coe_comp, Function.comp_apply, eval₂Hom_X', map_sum, map_mul, σ,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, aeval_X, algebraMap_eq]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s' _ => ?_
      have hGi := congrFun (hG s') i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hGi
      rw [← hGi, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_mul]
      ring
  intro f hf
  rw [RingHom.mem_ker] at hf ⊢
  rw [key, RingHom.comp_apply, hf, map_zero]

omit [∀ k, Fintype (ι k)] in

theorem exists_homog_span [DecidableEq K] (P : Ideal (MRing ι)) [P.IsPrime]
    (hP : ∀ f ∈ P, ∀ b, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f ∈ P)
    {t N1 n : ℕ} (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (hc : ∀ r j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (c r j) m)
    (B : Fin n → Fin N1 → FnField P)
    (hB : ∀ a, B a ∈ LinearMap.ker (Matrix.mulVecLin (Matrix.of fun r j => evalAt (genPt P) (c r j)))) :
    ∃ (S : Type) (_ : Fintype S) (V : S → Fin N1 → MRing ι) (γ : S → K → ℕ),
      (∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s)) ∧
      (∀ s, (fun j => toFn P (V s j)) ∈
        LinearMap.ker (Matrix.mulVecLin (Matrix.of fun r j => evalAt (genPt P) (c r j)))) ∧
      ∀ a, B a ∈ Submodule.span (FnField P) (Set.range fun s j => toFn P (V s j)) := by
  classical
  set w := NumbersDVR.blockWeight ι
  choose δ hδ using fun a => IsLocalization.exist_integer_multiples (nonZeroDivisors (MRing ι ⧸ P))
    (Finset.univ : Finset (Fin N1)) (B a)
  have hlift : ∀ a j, ∃ L : MRing ι, toFn P L = (δ a : MRing ι ⧸ P) • B a j := by
    intro a j
    obtain ⟨r, hr⟩ := hδ a j (Finset.mem_univ j)
    obtain ⟨L, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact ⟨L, hr⟩
  choose L hL using hlift
  have hL' : ∀ a j, toFn P (L a j) = algebraMap (MRing ι ⧸ P) (FnField P) (δ a) * B a j :=
    fun a j => by rw [hL a j]; exact Algebra.smul_def (δ a : MRing ι ⧸ P) (B a j)
  have hrow : ∀ a r, ∑ j, c r j * L a j ∈ P := by
    intro a r
    have h0 : ∑ j, evalAt (genPt P) (c r j) * B a j = 0 := by
      have := congrFun (LinearMap.mem_ker.mp (hB a)) r
      simpa [Matrix.mulVec, dotProduct] using this
    rw [← ker_toFn P, RingHom.mem_ker, map_sum]
    simp only [map_mul, hL', ← evalAt_genPt]
    rw [show ∑ j, evalAt (genPt P) (c r j) * (algebraMap (MRing ι ⧸ P) (FnField P) (δ a) * B a j) =
        algebraMap (MRing ι ⧸ P) (FnField P) (δ a) * ∑ j, evalAt (genPt P) (c r j) * B a j by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring]
    rw [h0, mul_zero]
  let D : Finset (K → ℕ) := Finset.univ.biUnion fun aj : Fin n × Fin N1 =>
    (L aj.1 aj.2).support.image (Finsupp.weight w)
  have hsum : ∀ a j, ∑ γ ∈ D, weightedHomogeneousComponent w γ (L a j) = L a j := by
    intro a j
    conv_rhs => rw [← sum_weightedHomogeneousComponent w (L a j)]
    refine (finsum_eq_sum_of_support_subset _ fun γ hγ => ?_).symm
    rw [Function.mem_support] at hγ
    by_contra hD
    refine hγ (weightedHomogeneousComponent_eq_zero' γ (L a j) fun d hd hdγ => hD ?_)
    exact Finset.mem_biUnion.mpr ⟨(a, j), Finset.mem_univ _, Finset.mem_image.mpr ⟨d, hd, hdγ⟩⟩
  refine ⟨Fin n × D, inferInstance, fun s j => weightedHomogeneousComponent w s.2 (L s.1 j), fun s => s.2,
    fun s j => weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_, ?_⟩
  · intro s
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext r
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, evalAt_genPt, ← map_mul,
      ← map_sum]
    rw [← RingHom.mem_ker, ker_toFn]
    rw [show ∑ j, c r j * weightedHomogeneousComponent w s.2 (L s.1 j) =
        weightedHomogeneousComponent w (s.2 + m) (∑ j, c r j * L s.1 j) by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => (weightedHomogeneousComponent_mul_of_left (hc r j) _ _).symm]
    exact hP _ (hrow s.1 r) _
  · intro a
    have hδ0 : algebraMap (MRing ι ⧸ P) (FnField P) (δ a) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (δ a).2
    have hBa : B a = (algebraMap (MRing ι ⧸ P) (FnField P) (δ a))⁻¹ •
        ∑ γ : D, fun j => toFn P (weightedHomogeneousComponent w γ (L a j)) := by
      funext j
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← map_sum]
      rw [Finset.sum_coe_sort D (fun γ => weightedHomogeneousComponent w γ (L a j)), hsum, hL',
        ← mul_assoc, inv_mul_cancel₀ hδ0, one_mul]
    rw [hBa]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun γ _ => Submodule.subset_span ⟨(a, γ), rfl⟩)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Weights

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def zDegInl : (K → ℕ) →+ (K ⊕ Unit → ℤ) :=
  AddMonoidHom.mk' (fun a x => Sum.elim (fun k => (a k : ℤ)) (fun _ => 0) x) (by
    intro a b
    funext x
    cases x <;> simp)

def zDeg : (K ⊕ Unit → ℕ) →+ (K ⊕ Unit → ℤ) := AddMonoidHom.compLeft (Nat.castAddMonoidHom ℤ) _

omit [Fintype K] [DecidableEq K] in
theorem zDeg_injective : Function.Injective (zDeg (K := K)) := fun a b h =>
  funext fun x => by
    have := congrFun h x
    simpa [zDeg] using this

variable (ι) {S : Type} [Fintype S] (γ : S → K → ℕ)

def genericWeight : S ⊕ (Σ k, ι k) → (K ⊕ Unit → ℤ)
  | .inl s => Pi.single (Sum.inr ()) 1 - zDegInl (γ s)
  | .inr p => zDegInl (NumbersDVR.blockWeight ι p)

variable {ι} {N1 : ℕ}

def genericSubstitution (V : S → Fin N1 → MRing ι) : (Σ x, PBlk ι N1 x) → MvPolynomial (S ⊕ (Σ k, ι k)) ℤ
  | ⟨.inl k, i⟩ => X (.inr ⟨k, i⟩)
  | ⟨.inr _, j⟩ => ∑ s, rename Sum.inr (V s j) * X (.inl s)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem genericSubstitution_isWeightedHomogeneous (V : S → Fin N1 → MRing ι)
    (hV : ∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s))
    (v : Σ x, PBlk ι N1 x) :
    IsWeightedHomogeneous (genericWeight ι γ) (genericSubstitution V v) (zDeg (NumbersDVR.blockWeight (PBlk ι N1) v)) := by
  rcases v with ⟨k | u, i⟩
  · convert isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inr ⟨k, i⟩) using 1
    · rfl
    · funext x
      cases x <;> simp [genericWeight, zDegInl, zDeg, NumbersDVR.blockWeight, Pi.single_apply]
  · have hdeg : zDeg (NumbersDVR.blockWeight (PBlk ι N1) ⟨Sum.inr u, i⟩) = Pi.single (Sum.inr ()) 1 := by
      funext x
      cases x <;> simp [zDeg, NumbersDVR.blockWeight]
    rw [hdeg]
    change Fin N1 at i
    refine IsWeightedHomogeneous.sum _ _ _ fun s _ => ?_
    have hren : IsWeightedHomogeneous (genericWeight ι γ) (rename Sum.inr (V s i) : MvPolynomial (S ⊕ _) ℤ)
        (zDegInl (γ s)) := by
      rw [rename_eq_aeval]
      refine isWeightedHomogeneous_aeval_of_weights (w := fun p => zDegInl (NumbersDVR.blockWeight ι p))
        (e := X ∘ Sum.inr)
        (fun p => isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inr p)) ?_
      intro d hd
      rw [NumbersDVR.weight_comp_addMonoidHom, hV s i hd]
    convert hren.mul (isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inl s)) using 1
    show _ = zDegInl (γ s) + (Pi.single (Sum.inr ()) 1 - zDegInl (γ s))
    abel

end Weights

section Kernel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [Fintype S]

def genericEvaluation (P : Ideal (MRing ι)) : MvPolynomial (S ⊕ (Σ k, ι k)) ℤ →+* MvPolynomial S (FnField P) :=
  (map (toFn P)).comp (sumAlgEquiv ℤ S (Σ k, ι k)).toAlgHom.toRingHom

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S] in
theorem sumAlgEquiv_rename_inr (f : MRing ι) :
    sumAlgEquiv ℤ S (Σ k, ι k) (rename Sum.inr f) = C f := by
  have := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr ℤ S (Σ k, ι k)) f
  simpa [algebraMap_eq] using this

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S] in
theorem genericEvaluation_rename_inr (P : Ideal (MRing ι)) (f : MRing ι) :
    genericEvaluation (S := S) P (rename Sum.inr f) = C (toFn P f) := by
  simp [genericEvaluation, sumAlgEquiv_rename_inr]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem genMap_eq_comp [DecidableEq K] (P : Ideal (MRing ι)) {N1 : ℕ} (V : S → Fin N1 → MRing ι) :
    genMap P (fun s j => toFn P (V s j)) = (genericEvaluation P).comp (aeval (genericSubstitution V)).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun z => by simp) ?_
  rintro ⟨k | u, i⟩
  · simp [genMap, genericSubstitution, genericEvaluation, genPt, toFn]
  · change Fin N1 at i
    simp only [genMap, genericSubstitution, RingHom.coe_comp, Function.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, aeval_X, map_sum, map_mul, genericEvaluation_rename_inr]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [genericEvaluation]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S] in

theorem ker_genericEvaluation_le (P : Ideal (MRing ι)) :
    RingHom.ker (genericEvaluation (S := S) P) ≤ Ideal.map (rename Sum.inr) P := by
  intro f hf
  set e := sumAlgEquiv ℤ S (Σ k, ι k)
  have hg : e f ∈ Ideal.map (C : MRing ι →+* MvPolynomial S (MRing ι)) P := by
    rw [← ker_toFn P, ← MvPolynomial.ker_map]
    exact hf
  have hre : ∀ x : MRing ι, e.symm (C x) = rename Sum.inr x := by
    intro x
    rw [AlgEquiv.symm_apply_eq]
    exact (sumAlgEquiv_rename_inr x).symm
  have h1 : Ideal.map e.symm (Ideal.map (C : MRing ι →+* MvPolynomial S (MRing ι)) P) ≤
      Ideal.map (rename Sum.inr) P := by
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, hre]
    exact Ideal.mem_map_of_mem _ hx
  simpa using h1 (Ideal.mem_map_of_mem e.symm hg)

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S] in

theorem map_le_ker_genericEvaluation (P : Ideal (MRing ι)) :
    Ideal.map (rename Sum.inr) P ≤ RingHom.ker (genericEvaluation (S := S) P) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, genericEvaluation_rename_inr]
  have h0 : toFn P x = 0 := by rw [← RingHom.mem_ker, ker_toFn]; exact hx
  rw [h0, map_zero]

theorem component_mem_ker_genMap [DecidableEq K] (P : Ideal (MRing ι)) (G : Set (MRing ι))
    (hG : ∀ f ∈ G, ∃ a, IsMultiHomog f a) (hPG : P = Ideal.span G) {N1 : ℕ}
    (V : S → Fin N1 → MRing ι) (γ : S → K → ℕ)
    (hV : ∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s))
    {f : MRing (PBlk ι N1)} (hf : f ∈ RingHom.ker (genMap P fun s j => toFn P (V s j)))
    (b : K ⊕ Unit → ℕ) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight (PBlk ι N1)) b f ∈
      RingHom.ker (genMap P fun s j => toFn P (V s j)) := by
  classical
  rw [genMap_eq_comp] at hf ⊢
  rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker] at hf ⊢
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf ⊢
  have hJ := ker_genericEvaluation_le P hf
  have hGw : ∀ g ∈ G, ∃ a, IsWeightedHomogeneous (fun p => zDegInl (NumbersDVR.blockWeight ι p)) g a := by
    intro g hg
    obtain ⟨a, ha⟩ := hG g hg
    refine ⟨zDegInl a, fun d hd => ?_⟩
    rw [NumbersDVR.weight_comp_addMonoidHom, ((Bridge.isMultiHomog_iff g a).mpr ha) hd]
  rw [hPG, rename_eq_aeval] at hJ
  have hc := weightedHomogeneousComponent_mem_map_aeval (ω := genericWeight ι γ) (e := X ∘ Sum.inr)
    (fun p => isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inr p)) G hGw hJ (zDeg b)
  rw [← rename_eq_aeval, ← hPG] at hc
  rw [← aeval_weightedHomogeneousComponent_of_weights
      (fun v => zDeg (NumbersDVR.blockWeight (PBlk ι N1) v)) (genericWeight ι γ) (genericSubstitution V)
      (genericSubstitution_isWeightedHomogeneous γ V hV), NumbersDVR.weightedHomogeneousComponent_comp_addMonoidHom zDeg zDeg_injective]
    at hc
  exact map_le_ker_genericEvaluation P hc

end Kernel

theorem ProjBundleMultiHomog.proof : ProjBundleMultiHomog.Statement := by
  intro K _ ι _ N1 t n P d c m B hP hQ hB
  classical
  obtain ⟨-, ⟨hPp, hPh, -⟩, -, -⟩ := hP
  have := hPp
  have hPc := (Bridge.isMultiHomogIdeal_iff P).mpr hPh
  obtain ⟨S, _, V, γ, hV, hVker, hBspan⟩ := exists_homog_span P hPc c m
    (fun r j => (Bridge.isMultiHomog_iff _ _).mpr (hQ.1 r j)) B
    (fun a => by rw [← hB.2]; exact Submodule.subset_span ⟨a, rfl⟩)
  have hker : projBundleIdeal P B = RingHom.ker (genMap P fun s j => toFn P (V s j)) :=
    le_antisymm (ker_genMap_le P B _ fun s => by rw [hB.2]; exact hVker s)
      (ker_genMap_le P _ B hBspan)
  rw [hker]
  obtain ⟨G, hG, hPG⟩ := hPh
  exact (Bridge.isMultiHomogIdeal_iff _).mp fun f hf b => component_mem_ker_genMap P G hG hPG V γ hV hf b

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end
