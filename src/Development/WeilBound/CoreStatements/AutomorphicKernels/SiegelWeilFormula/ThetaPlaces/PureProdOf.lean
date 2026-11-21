import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.ProjInf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.RelReal

section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA

section Repr

variable {k : Type} [Field k] {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra k R] [Algebra k S]
  [Algebra k B]

theorem basis_repr_map' {J : Type} (b : Module.Basis J k B) (ρ : R →ₐ[k] S) (x : R ⊗[k] B) (i : J) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map ρ (AlgHom.id k B) x) i =
      ρ ((Algebra.TensorProduct.basis R b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [hx, hy]

end Repr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def phiV (v : HeightOneSpectrum (𝓞 F)) : HeckeCharacterZeroLocus.SiegelWeilU.AF F →ₐ[F] HeckeCharacterZeroLocus.SiegelWeilU.Fv F v :=
  (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)

def mapV (v : HeightOneSpectrum (𝓞 F)) :
    HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E →ₐ[F] HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map (phiV v) (AlgHom.id F E)

theorem mapV_eq (v : HeightOneSpectrum (𝓞 F)) (x : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    mapV v x = Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def IntV (bs : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (z : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) : Prop :=
  ∀ k, (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs).repr z k ∈ v.adicCompletionIntegers F

theorem ev_int_adele (a : HeckeCharacterZeroLocus.SiegelWeilU.AF F) :
    ∀ᶠ v in cofinite, phiV v a ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F := by
  filter_upwards [a.2.2] with v hv
  exact hv

theorem ev_int_F (f : F) :
    ∀ᶠ v in cofinite, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) f ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F := by
  filter_upwards [ev_int_adele (algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.AF F) f)] with v hv
  rwa [AlgHom.commutes] at hv

theorem intV_sum (bs : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (z : ι → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) (h : ∀ i ∈ s, IntV bs v (z i)) : IntV bs v (∑ i ∈ s, z i) := by
  intro k
  rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  exact sum_mem fun i hi => h i hi k

theorem ev_mul_int (bs : Module.Basis (Fin 2) F E) (c : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    ∀ᶠ v in cofinite, ∀ z, IntV bs v z → IntV bs v (mapV v c * z) := by
  set bA := Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) bs
  have h1 : ∀ᶠ v in cofinite, ∀ k, phiV v (bA.repr c k) ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => ev_int_adele _
  have h2 : ∀ᶠ v in cofinite, ∀ k j l, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (bs.repr (bs k * bs j) l) ∈
      (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun l => ev_int_F _
  filter_upwards [h1, h2] with v hv1 hv2
  intro z hz l
  set bV := Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs
  have hc : mapV v c = ∑ k, phiV v (bA.repr c k) • bV k := by
    conv_lhs => rw [← bV.sum_repr (mapV v c)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mapV, basis_repr_map']
  have hzz : z = ∑ j, bV.repr z j • bV j := (bV.sum_repr z).symm
  have hprod : bV.repr (mapV v c * z) l =
      ∑ k, ∑ j, (phiV v (bA.repr c k) * bV.repr z j) * algebraMap F _ (bs.repr (bs k * bs j) l) := by
    rw [hc]
    conv_lhs => rw [hzz]
    rw [Finset.sum_mul_sum]
    simp only [smul_mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, bV, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply, one_smul]
  rw [hprod]
  exact sum_mem fun k _ => sum_mem fun j _ => mul_mem (mul_mem (hv1 k) (hz j)) (hv2 k j l)

def IntM (bs : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) : Prop := ∀ i j, IntV bs v (M i j)

theorem ev_matmul_int (bs : Module.Basis (Fin 2) F E) {q : ℕ} (A : Matrix (Fin q) (Fin q) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    ∀ᶠ v in cofinite, ∀ (p : ℕ) (M : Matrix (Fin p) (Fin q) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)),
      IntM bs v M → IntM bs v (M * A.map (mapV v)) := by
  have h : ∀ᶠ v in cofinite, ∀ i j, ∀ z, IntV bs v z → IntV bs v (mapV v (A i j) * z) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_mul_int bs (A i j)
  filter_upwards [h] with v hv
  intro p M hM i j
  simp only [Matrix.mul_apply, Matrix.map_apply]
  refine intV_sum bs v _ _ fun l _ => ?_
  rw [mul_comm]
  exact hv l j _ (hM i l)

end PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA

end
end

section
noncomputable section

open scoped TensorProduct Matrix HeckeCharacterZeroLocus.SiegelWeilU
open NumberField IsDedekindDomain Filter

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR.PureC

open PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_mul_alg {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) {p q r : ℕ}
    (M : Matrix (Fin p) (Fin q) A) (N : Matrix (Fin q) (Fin r) A) : (M * N).map f = M.map f * N.map f :=
  Matrix.map_mul (f := f.toRingHom)

variable (bs : Module.Basis (Fin 2) F E) {m n : ℕ} (u : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E))
  (v : HeightOneSpectrum (𝓞 F))

def toMxV (Y : Fin n → Fin m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) : Matrix (Fin m) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
  Matrix.of fun a j => Y j a

abbrev Av : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
  (((u⁻¹ : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)).1)ᵀ).map (mapV v)

abbrev Bv : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) := ((u.1)ᵀ).map (mapV v)

theorem Av_mul_Bv : Av u v * Bv u v = 1 := by
  rw [Av, Bv, ← map_mul_alg, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem Bv_mul_Av : Bv u v * Av u v = 1 := by
  rw [Av, Bv, ← map_mul_alg, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

def crdV (N : Matrix (Fin m) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) : Fin m × Fin n × Fin 2 → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v :=
  fun k => (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs).repr (N k.1 k.2.1) k.2.2

def cmbV (c : Fin m × Fin n × Fin 2 → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) : Matrix (Fin m) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
  Matrix.of fun i j => ∑ kk, c (i, j, kk) • Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs kk

theorem cmbV_crdV (N : Matrix (Fin m) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) : cmbV bs v (crdV bs v N) = N := by
  ext i j
  exact (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs).sum_repr (N i j)

theorem crdV_cmbV (c : Fin m × Fin n × Fin 2 → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) : crdV bs v (cmbV bs v c) = c := by
  funext k
  simp only [crdV, cmbV, Matrix.of_apply]
  rw [(Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs).repr_sum_self]

def eL : (Fin n → Fin m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) ≃ₗ[HeckeCharacterZeroLocus.SiegelWeilU.Fv F v]
    (Fin m × Fin n × Fin 2 → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) where
  toFun Y := crdV bs v (toMxV v Y * Av u v)
  map_add' Y Y' := by
    funext k
    have : toMxV v (Y + Y') = toMxV v Y + toMxV v Y' := by ext; rfl
    simp only [this, Matrix.add_mul, crdV, Matrix.add_apply, map_add, Finsupp.add_apply, Pi.add_apply]
  map_smul' r Y := by
    funext k
    have : toMxV v (r • Y) = r • toMxV v Y := by ext; rfl
    simp only [this, Matrix.smul_mul, crdV, Matrix.smul_apply, map_smul, Finsupp.smul_apply, RingHom.id_apply,
      Pi.smul_apply]
  invFun c := fun j a => (cmbV bs v c * Bv u v) a j
  left_inv Y := by
    funext j a
    simp only [cmbV_crdV, Matrix.mul_assoc, Av_mul_Bv, Matrix.mul_one]
    rfl
  right_inv c := by
    have : toMxV v (fun j a => (cmbV bs v c * Bv u v) a j) = cmbV bs v c * Bv u v := by ext; rfl
    simp only [this, Matrix.mul_assoc, Bv_mul_Av, Matrix.mul_one, crdV_cmbV]

section Top

instance modTopV : IsModuleTopology (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) := ⟨rfl⟩

def eH : (Fin n → Fin m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) ≃ₜ (Fin m × Fin n × Fin 2 → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) := by
  haveI : ContinuousAdd (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) _
  haveI : ContinuousSMul (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
    IsModuleTopology.toContinuousSMul (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) _
  exact { toEquiv := (eL bs u v).toEquiv
          continuous_toFun := IsModuleTopology.continuous_of_linearMap (eL bs u v).toLinearMap
          continuous_invFun := IsModuleTopology.continuous_of_linearMap (eL bs u v).symm.toLinearMap }

theorem isSB_comp (φ : (Fin m × Fin n × Fin 2 → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) → ℂ)
    (hφ : IsLocallyConstant φ ∧ HasCompactSupport φ) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsSB (fun Y : Fin n → Fin m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E => φ (crdV bs v (toMxV v Y * Av u v))) :=
  ⟨hφ.1.comp_continuous (eH bs u v).continuous, hφ.2.comp_homeomorph (eH bs u v)⟩

end Top

theorem int_iff : ∀ᶠ v in cofinite, ∀ Y : Fin n → Fin m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E,
    (∀ k, crdV bs v (toMxV v Y * Av u v) k ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F) ↔
      Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v := by
  filter_upwards [ev_matmul_int bs ((u⁻¹ : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)).1)ᵀ,
    ev_matmul_int bs (u.1)ᵀ] with v h1 h2
  intro Y
  have e1 : (∀ k, crdV bs v (toMxV v Y * Av u v) k ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F) ↔
      IntM bs v (toMxV v Y * Av u v) := ⟨fun h i j kk => h (i, j, kk), fun h k => h k.1 k.2.1 k.2.2⟩
  have e2 : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v ↔ IntM bs v (toMxV v Y) := ⟨fun h i j kk => h j i kk, fun h a i kk => h i a kk⟩
  rw [e1, e2]
  constructor
  · intro h
    have := h2 _ _ h
    rwa [Matrix.mul_assoc, ← Bv, Av_mul_Bv, Matrix.mul_one] at this
  · intro h
    exact h1 _ _ h

end PositivityTheory.SiegelWeilFormula.ThetaDictR.PureC

end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA PositivityTheory.SiegelWeilFormula.ThetaDictR.PureC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pure_prod_of' {d : SD σ} (R : RD d) (Φ : d.Fn) (P : InfinitePlace F → PX d.m d.n)
    (gf : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ) (hP : IsPureBy R Φ P gf)
    (u : GL (Fin d.n) (AE F E)) (η : E)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star)
    (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1)
    (l : InfinitePlace F → ℝ) (hl : ∀ w, |l w| = 1) :
    ∃ (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ),
      HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧
      HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin (fun Y => d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ))
        (Gen.phiInf θ l fr g P) Φf := by
  obtain ⟨hloc, hcof, hT⟩ := hP
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ :=
    fun v Y => gf v (crdV d.bs v (toMxV v Y * Av u v))
  refine ⟨fun X => ∏ᶠ v, Φv v (HeckeCharacterZeroLocus.SiegelWeilU.projV v X), Φv,
    ⟨fun v => isSB_comp d.bs u v (gf v) (hloc v), ?_, fun X => rfl⟩, ?_⟩
  · filter_upwards [hcof, int_iff (m := d.m) d.bs u] with v hv hint
    funext Y
    show gf v _ = _
    rw [hv]
    by_cases h : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV d.bs v
    · rw [Set.indicator_of_mem h]
      refine (Set.indicator_of_mem ?_ _).trans rfl
      exact (hint Y).2 h
    · rw [Set.indicator_of_notMem h]
      refine Set.indicator_of_notMem ?_ _
      intro h'
      exact h ((hint Y).1 h')
  · intro X
    dsimp only
    rw [hT]
    dsimp only
    congr 1
    · unfold Gen.phiInf
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [PureB.crd_eq R u η θ th fr frc g gc w X, hl w, mul_one]
      rfl
    · refine finprod_congr fun v => ?_
      congr 1
      funext k
      have hZ : (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map (mapV v) =
          toMxV v (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X)) * Av u v := by
        rw [map_mul_alg]
        congr 1
        ext a j
        simp only [Matrix.map_apply, toMx, toMxV, Matrix.of_apply, HeckeCharacterZeroLocus.SiegelWeilU.projV, HeckeCharacterZeroLocus.SiegelWeilU.projFin,
          mapV_eq]
      have h1 : HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) k).2 =
          phiV v (d.crd (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) k) := rfl
      rw [h1, SD.crd, ← basis_repr_map']
      simp only [crdV]
      rw [← hZ]
      rfl

end PositivityTheory.SiegelWeilFormula.ThetaDictR

end
end
