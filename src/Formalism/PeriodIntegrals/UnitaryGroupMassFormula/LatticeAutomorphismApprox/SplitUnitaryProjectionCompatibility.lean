import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocDefs
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.SplitGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB

open Matrix PI.UnitaryGroupMassFormula.AdIndexEq

def piHom {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K) : R →+* K × K :=
  RingHom.prod p1 (p1.comp σ)

theorem piHom_bijective {K R : Type} [Field K] [CommRing R] [Algebra K R] [FiniteDimensional K R]
    (hdim : Module.finrank K R = 2) (σ : R →+* R) (p1 : R →+* K)
    (hσK : ∀ c, σ (algebraMap K R c) = algebraMap K R c) (hσσ : ∀ r, σ (σ r) = r)
    (hp1K : ∀ c, p1 (algebraMap K R c) = c) (ε : R) (h1 : p1 ε = 1) (h0 : p1 (σ ε) = 0) :
    Function.Bijective (piHom σ p1) := by
  let L : R →ₗ[K] K × K :=
    { toFun := piHom σ p1
      map_add' := fun a b => map_add _ a b
      map_smul' := fun c r => by
        rw [Algebra.smul_def, map_mul]
        ext <;> simp [piHom, hp1K, hσK] }
  have hsurj : Function.Surjective L := by
    rintro ⟨a, b⟩
    refine ⟨algebraMap K R a * ε + algebraMap K R b * σ ε, ?_⟩
    ext <;> simp [L, piHom, hp1K, hσK, hσσ, h1, h0]
  have hfr : Module.finrank K R = Module.finrank K (K × K) := by
    rw [hdim, Module.finrank_prod, Module.finrank_self]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 hsurj, hsurj⟩

def piEquiv {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K)
    (hb : Function.Bijective (piHom σ p1)) : R ≃+* K × K :=
  RingEquiv.ofBijective (piHom σ p1) hb

theorem piEquiv_sig {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K)
    (hσσ : ∀ r, σ (σ r) = r) (hb : Function.Bijective (piHom σ p1)) (r : R) :
    piEquiv σ p1 hb (σ r) = (piEquiv σ p1 hb r).swap := by
  ext <;> simp [piEquiv, piHom, hσσ]



theorem proj_coe {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (σ : R →+* R) (π : R ≃+* k × k) (J : Matrix n n R) (y : Formalism.UG.UJ σ J) :
    ((SplitGL.proj σ π J y : GL n k) : Matrix n n k) = ((y : GL n R) : Matrix n n R).map (SplitGL.p1 π) := rfl

theorem isUnit_det_first_projection {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (π : R ≃+* k × k) (J : Matrix n n R) (hdet : IsUnit J.det) : IsUnit (J.map (SplitGL.p1 π)).det := by
  show IsUnit ((SplitGL.p1 π).mapMatrix J).det
  rw [← RingHom.map_det]
  exact hdet.map _

theorem second_projection_mulVec_eq {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap) (J : Matrix n n R)
    (hdet : IsUnit J.det) (y : Formalism.UG.UJ σ J) (β β' : n → k)
    (h : β' ᵥ* J.map (SplitGL.p1 π) =
      (β ᵥ* J.map (SplitGL.p1 π)) ᵥ* (((SplitGL.proj σ π J y)⁻¹ : GL n k) : Matrix n n k)) :
    ((y : GL n R) : Matrix n n R).map (SplitGL.p2 π) *ᵥ β = β' := by
  set P := J.map (SplitGL.p1 π) with hP
  set M2 := ((y : GL n R) : Matrix n n R).map (SplitGL.p2 π) with hM2
  set T := SplitGL.proj σ π J y with hT
  have hu : M2ᵀ * P * (T : Matrix n n k) = P := by
    rw [hT, proj_coe]
    exact ((SplitGL.unitary_iff σ π hπ J _).1 y.2).1
  have hTT : (T : Matrix n n k) * ((T⁻¹ : GL n k) : Matrix n n k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : M2ᵀ * P = P * ((T⁻¹ : GL n k) : Matrix n n k) := by
    calc M2ᵀ * P = M2ᵀ * P * ((T : Matrix n n k) * ((T⁻¹ : GL n k) : Matrix n n k)) := by
          rw [hTT, Matrix.mul_one]
      _ = P * ((T⁻¹ : GL n k) : Matrix n n k) := by rw [← Matrix.mul_assoc, hu]
  have h2 : (M2 *ᵥ β) ᵥ* P = β' ᵥ* P := by
    calc (M2 *ᵥ β) ᵥ* P = (β ᵥ* M2ᵀ) ᵥ* P := by rw [Matrix.vecMul_transpose]
      _ = β ᵥ* (M2ᵀ * P) := by rw [Matrix.vecMul_vecMul]
      _ = β ᵥ* (P * ((T⁻¹ : GL n k) : Matrix n n k)) := by rw [key]
      _ = (β ᵥ* P) ᵥ* ((T⁻¹ : GL n k) : Matrix n n k) := by rw [Matrix.vecMul_vecMul]
      _ = β' ᵥ* P := h.symm
  have hPu : IsUnit P.det := isUnit_det_first_projection π J hdet
  have h3 := congrArg (fun w => w ᵥ* P⁻¹) h2
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hPu, Matrix.vecMul_one] at h3
  exact h3

end PI.UnitaryGroupMassFormula.ScXuExists.BrB
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB

open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

abbrev LL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Submodule (OV I v) (Fin I.n → RV I v) :=
  Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))

theorem sigV_sigV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (r : RV I v) :
    sigV I v (sigV I v r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [show I.cm.sig (I.cm.sig e) = e from star_star e]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigV_alg (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : KV I v) :
    sigV I v (algebraMap (KV I v) (RV I v) c) = algebraMap (KV I v) (RV I v) c := by
  simp [sigV, Algebra.TensorProduct.algebraMap_apply]

def vecqL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (q : RV I v →+* KV I v)
    (hq : ∀ c, q (algebraMap (KV I v) (RV I v) c) = c) :
    (Fin I.n → RV I v) →ₗ[OV I v] (Fin I.n → KV I v) where
  toFun x i := q (x i)
  map_add' x y := by funext i; simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [PI.FinKW.LocTo.ov_smul_eq, map_mul]
    have e : ((c : KV I v) ⊗ₜ[I.F] (1 : I.E)) = algebraMap (KV I v) (RV I v) (c : KV I v) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    rw [e, hq]
    rfl

theorem exists_of_mem_span (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (q : RV I v →+* KV I v)
    (hq : ∀ c, q (algebraMap (KV I v) (RV I v) c) = c) (y : Fin I.n → KV I v)
    (hy : y ∈ Submodule.span (OV I v)
      ((fun x : Fin I.n → RV I v => fun i => q (x i)) '' (LL I v : Set (Fin I.n → RV I v)))) :
    ∃ x ∈ LL I v, (fun i => q (x i)) = y := by
  have hy' : y ∈ Submodule.span (OV I v) (⇑(vecqL I v q hq) '' (LL I v : Set (Fin I.n → RV I v))) := hy
  rw [← Submodule.map_coe, Submodule.span_eq] at hy'
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy'
  exact ⟨x, hx, hxy⟩

theorem mem_LL_iff (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) (hinj : Function.Injective (piHom (sigV I v) p1))
    (hε : ∀ w ∈ LL I v, ε • w ∈ LL I v) (x : Fin I.n → RV I v) :
    x ∈ LL I v ↔ vec1 p1 x ∈ Lam1 I v p1 ∧ vec2 p1 x ∈ Lam2 I v p1 := by
  obtain ⟨hp1, hpe, hpse, -⟩ := hp
  constructor
  · intro hx
    exact ⟨Submodule.subset_span (Set.mem_image_of_mem _ hx), Submodule.subset_span (Set.mem_image_of_mem _ hx)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨x1, hx1, e1⟩ := exists_of_mem_span I v p1 hp1 (vec1 p1 x) h1
    have hq2 : ∀ c, (p1.comp (sigV I v)) (algebraMap (KV I v) (RV I v) c) = c := by
      intro c
      rw [RingHom.comp_apply, sigV_alg, hp1]
    obtain ⟨x2, hx2, e2⟩ := exists_of_mem_span I v (p1.comp (sigV I v)) hq2 (vec2 p1 x) h2
    have hw : ε • x1 + (x2 - ε • x2) ∈ LL I v :=
      (LL I v).add_mem (hε x1 hx1) ((LL I v).sub_mem hx2 (hε x2 hx2))
    have hxw : x = ε • x1 + (x2 - ε • x2) := by
      funext i
      apply hinj
      have f1 : p1 (x1 i) = p1 (x i) := congrFun e1 i
      have f2 : p1 (sigV I v (x2 i)) = p1 (sigV I v (x i)) := congrFun e2 i
      simp only [piHom, RingHom.prod_apply, RingHom.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, map_add, map_sub, map_mul, hpe, hpse, f1, f2]
      refine Prod.ext ?_ ?_ <;> simp
    rw [hxw]
    exact hw

theorem first_coordinate_vector_sub {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v)
    (X X' : Fin I.n → RV I v) : vec1 p1 (X - X') = vec1 p1 X - vec1 p1 X' := by
  funext i
  simp [vec1]

theorem second_coordinate_vector_sub {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v)
    (X X' : Fin I.n → RV I v) : vec2 p1 (X - X') = vec2 p1 X - vec2 p1 X' := by
  funext i
  simp [vec2]

theorem first_coordinate_vector_nsmul {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v)
    (c : ℕ) (X : Fin I.n → RV I v) : vec1 p1 ((c : RV I v) • X) = (c : KV I v) • vec1 p1 X := by
  funext i
  simp [vec1]

theorem second_coordinate_vector_nsmul {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v)
    (c : ℕ) (X : Fin I.n → RV I v) : vec2 p1 ((c : RV I v) • X) = (c : KV I v) • vec2 p1 X := by
  funext i
  simp [vec2]

end PI.UnitaryGroupMassFormula.ScXuExists.BrB
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB

open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

set_option maxHeartbeats 1000000 in
theorem split_unitary_projection_compatibility : BridgeB := by
  intro I g r k e f z Rf _hH v _hv _hsum p1 hp1 T hT
  have hε : ∀ w ∈ LL I v, PI.FinKW.psiV I v Rf.ew • w ∈ LL I v := fun w hw =>
    PI.FinKW.LocTo.intAf_le_mulSet I v Rf.ew_int w hw
  have : Module.Finite I.F I.E := Module.finite_of_finrank_eq_succ I.cm.deg2
  have hdim : Module.finrank (KV I v) (RV I v) = 2 := by
    rw [Module.finrank_baseChange]; exact I.cm.deg2
  have hb := piHom_bijective hdim (sigV I v) p1 (sigV_alg I v) (sigV_sigV I v) hp1.1
    (PI.FinKW.psiV I v Rf.ew) hp1.2.1 hp1.2.2.1
  set π := piEquiv (sigV I v) p1 hb with hπdef
  have hπ : ∀ r, π (sigV I v r) = (π r).swap := piEquiv_sig _ _ (sigV_sigV I v) hb
  have hchar := mem_LL_iff I v _ p1 hp1 hb.1 hε
  obtain ⟨y, hy⟩ := (SplitGL.proj_bijective (sigV I v) π hπ _ (spl_herm_v I v) (spl_det_v I v)).2 T
  subst hy
  have hPm : (I.J.map (inclV I v)).map (SplitGL.p1 π) = Pm I v p1 := by ext i j; rfl

  have v1 : ∀ (y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) (X : Fin I.n → RV I v),
      vec1 p1 (((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X) =
        ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y' : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v)) *ᵥ
          vec1 p1 X := by
    intro y' X; funext i; exact RingHom.map_mulVec p1 _ _ i
  have v2 : ∀ (y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) (X : Fin I.n → RV I v),
      vec2 p1 (((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X) =
        ((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)).map (SplitGL.p2 π) *ᵥ
          vec2 p1 X := by
    intro y' X; funext i; exact RingHom.map_mulVec (p1.comp (sigV I v)) _ _ i
  have vp2 : ∀ (y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) (β β' : Fin I.n → KV I v),
      β' ᵥ* Pm I v p1 = (β ᵥ* Pm I v p1) ᵥ*
        (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y')⁻¹ : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v)) →
      ((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)).map (SplitGL.p2 π) *ᵥ β = β' := by
    intro y' β β' h
    rw [← hPm] at h
    exact second_projection_mulVec_eq (sigV I v) π hπ _ (spl_det_v I v) y' β β' h
  have extv : ∀ X X' : Fin I.n → RV I v, vec1 p1 X = vec1 p1 X' → vec2 p1 X = vec2 p1 X' → X = X' := by
    intro X X' h1 h2
    funext i
    apply hb.1
    exact Prod.ext (congrFun h1 i) (congrFun h2 i)

  have fwd : ∀ y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v)),
      (∀ x ∈ Lam1 I v p1, ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y' : GL (Fin I.n) (KV I v)) :
        Matrix (Fin I.n) (Fin I.n) (KV I v)) *ᵥ x ∈ Lam1 I v p1) →
      (∀ β ∈ Lam2 I v p1, ∃ β' ∈ Lam2 I v p1, β' ᵥ* Pm I v p1 = (β ᵥ* Pm I v p1) ᵥ*
        (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y')⁻¹ : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v))) →
      ∀ w ∈ LL I v, ((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ w ∈ LL I v := by
    intro y' h1 h2 w hw
    rw [hchar] at hw ⊢
    obtain ⟨hw1, hw2⟩ := hw
    refine ⟨?_, ?_⟩
    · rw [v1]; exact h1 _ hw1
    · rw [v2]
      obtain ⟨β', hβ', eβ⟩ := h2 _ hw2
      rw [vp2 y' _ β' eβ]
      exact hβ'
  have hinvproj : SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y⁻¹ = (SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y)⁻¹ := map_inv _ y
  have fwdY := fwd y (fun x hx => (hT.1 x hx).1) (fun β hβ => (hT.2.1 β hβ).2)
  have fwdYi := fwd y⁻¹ (fun x hx => by rw [hinvproj]; exact (hT.1 x hx).2)
    (fun β hβ => by rw [hinvproj, inv_inv]; exact (hT.2.1 β hβ).1)
  have hYiY : ∀ X : Fin I.n → RV I v,
      (((y⁻¹ : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) : GL (Fin I.n) (RV I v)) :
        Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ
        (((y : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X) = X := by
    intro X
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]
    have : ((y⁻¹ : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) : GL (Fin I.n) (RV I v)) *
        (y : GL (Fin I.n) (RV I v)) = 1 := by
      rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
    rw [this, Units.val_one, Matrix.one_mulVec]
  have fixv : ∀ X : Fin I.n → RV I v,
      ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v)) *ᵥ
        vec1 p1 X = vec1 p1 X →
      (vec2 p1 X ᵥ* Pm I v p1) ᵥ* ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y : GL (Fin I.n) (KV I v)) :
        Matrix (Fin I.n) (Fin I.n) (KV I v)) = vec2 p1 X ᵥ* Pm I v p1 →
      ((y : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X = X := by
    intro X h1 h2
    apply extv
    · rw [v1, h1]
    · rw [v2]
      apply vp2
      symm
      calc (vec2 p1 X ᵥ* Pm I v p1) ᵥ*
            (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y)⁻¹ : GL (Fin I.n) (KV I v)) :
              Matrix (Fin I.n) (Fin I.n) (KV I v))
          = ((vec2 p1 X ᵥ* Pm I v p1) ᵥ* ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y :
              GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v))) ᵥ*
            (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y)⁻¹ : GL (Fin I.n) (KV I v)) :
              Matrix (Fin I.n) (Fin I.n) (KV I v)) := by rw [h2]
        _ = vec2 p1 X ᵥ* Pm I v p1 := by
          rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  refine ⟨(y : GL (Fin I.n) (RV I v)), y.2, ?_, ?_, ?_⟩
  ·
    intro x
    refine ⟨fun hx => fwdY x hx, fun hx => ?_⟩
    have := fwdYi _ hx
    rwa [hYiY] at this
  ·
    intro a
    obtain ⟨h1, h2, h3, h4⟩ := hT.2.2.1 a
    exact ⟨fixv _ h1 h3, fixv _ h2 h4⟩
  ·
    obtain ⟨w1, hw1, hw1e⟩ := hT.2.2.2.1
    obtain ⟨β, hβ, hβe⟩ := hT.2.2.2.2
    set w : Fin I.n → RV I v := fun i => π.symm (w1 i, β i) with hwdef
    have hw1' : vec1 p1 w = w1 := by
      funext i
      show SplitGL.p1 π (π.symm (w1 i, β i)) = w1 i
      simp [SplitGL.p1]
    have hw2' : vec2 p1 w = β := by
      funext i
      show SplitGL.p2 π (π.symm (w1 i, β i)) = β i
      simp [SplitGL.p2]
    have hwL : w ∈ LL I v := (hchar w).2 ⟨hw1' ▸ hw1, hw2' ▸ hβ⟩
    refine ⟨w, hwL, ?_⟩
    have hyi : ((y : GL (Fin I.n) (RV I v))⁻¹ : GL (Fin I.n) (RV I v)) =
        ((y⁻¹ : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) : GL (Fin I.n) (RV I v)) := rfl
    rw [hyi]
    apply extv
    · rw [first_coordinate_vector_sub, v1, first_coordinate_vector_nsmul, hw1', hinvproj]
      exact hw1e
    · rw [second_coordinate_vector_sub, v2, second_coordinate_vector_nsmul, hw2']
      rw [vp2 y⁻¹ _ (vec2 p1 (PI.FinKW.vecV I v Rf.z0) + (g : KV I v) • β)]
      · abel
      · rw [hinvproj, inv_inv, Matrix.add_vecMul, Matrix.smul_vecMul, ← hβe]
        abel

end PI.UnitaryGroupMassFormula.ScXuExists.BrB
end
end
