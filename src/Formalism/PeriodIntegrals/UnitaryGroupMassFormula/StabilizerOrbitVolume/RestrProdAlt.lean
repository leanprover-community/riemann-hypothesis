import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProdSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoPolish

section
noncomputable section

namespace PI.VolStabSW.RestrProdA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem hasProd_compl_of_ne_zero {β : Type} {f : β → ℂ} {p : ℂ} (h : HasProd f p) (S : Finset β)
    (hS : ∀ b ∈ S, f b ≠ 0) :
    HasProd ({b | b ∉ S}.mulIndicator f) (p * ∏ b ∈ S, (f b)⁻¹) := by
  classical
  have h2 : HasProd (fun b => if b ∈ S then (f b)⁻¹ else 1)
      (∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1)) := hasProd_prod_of_ne_finset_one fun b hb => if_neg hb
  have e : ∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1) = ∏ b ∈ S, (f b)⁻¹ :=
    Finset.prod_congr rfl fun b hb => if_pos hb
  rw [e] at h2
  convert h.mul h2 using 1
  funext b
  by_cases hb : b ∈ S
  · simp [Set.mulIndicator, hb, hS b hb]
  · simp [Set.mulIndicator, hb]

theorem hasProd_ofReal_of_complex {β : Type} {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) {q : ℂ}
    (h : HasProd (fun b => (f b : ℂ)) q) :
    HasProd (fun b => ENNReal.ofReal (f b)) (ENNReal.ofReal q.re) := by
  unfold HasProd at h ⊢
  have h1 := ((ENNReal.continuous_ofReal.comp Complex.continuous_re).tendsto q).comp h
  refine h1.congr fun s => ?_
  simp only [Function.comp_apply, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact ENNReal.ofReal_prod_of_nonneg fun b _ => hf b

theorem rpTail_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E))
    (hSB : ∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ → Integrable Φ (m v))
    (hmult : ∀ (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv → Multipliable (fun v => ∫ X, Φv v X ∂(m v))) :
    (∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ → ∫ X, Φ X ∂(m v) = 0) ∨
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ENNReal, c ≠ ⊤ ∧
      HasProd (fun v : {v // v ∉ S} => m v.1 (latV b v.1)) c := by
  classical
  by_cases h0 : ∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ → ∫ X, Φ X ∂(m v) = 0
  · exact Or.inl h0
  refine Or.inr fun S => ?_
  push_neg at h0
  choose g hgSB hg0 using h0
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => if v ∈ S then g v else (latV b v).indicator 1
  have hpure : IsPureFin b (fun Y => ∏ᶠ v, Φv v (projV v Y)) Φv := by
    refine ⟨fun v => ?_, ?_, fun Y => rfl⟩
    · by_cases hv : v ∈ S
      · simp only [Φv, hv, if_true]; exact hgSB v
      · simp only [Φv, hv, if_false]; exact PositiveNearLattice.isSB_latV b v a M
    · refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
      by_contra h
      exact hv (if_neg h)
  have hP := (hmult _ Φv hpure).hasProd
  have hne : ∀ v ∈ S, ∫ X, Φv v X ∂(m v) ≠ 0 := fun v hv => by
    simp only [Φv, hv, if_true]; exact hg0 v
  have h1 := hasProd_compl_of_ne_zero hP S hne
  have hL : ∀ v, MeasurableSet (latV (M := M) (n := a) b v) := fun v =>
    (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet
  have hfin : ∀ v, m v (latV b v) ≠ ⊤ := fun v => by
    have h := hSB v _ (PositiveNearLattice.isSB_latV b v a M)
    rw [integrable_indicator_iff (hL v)] at h
    exact (((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne
  have e : {v | v ∉ S}.mulIndicator (fun v => ∫ X, Φv v X ∂(m v)) =
      fun v => (({v | v ∉ S}.mulIndicator (fun v => (m v (latV b v)).toReal) v : ℝ) : ℂ) := by
    funext v
    by_cases hv : v ∈ S
    · simp [Set.mulIndicator, hv]
    · simp only [Set.mulIndicator, Set.mem_setOf_eq, hv, not_false_eq_true, if_true, Φv, if_false]
      rw [integral_indicator (hL v)]
      simp [Measure.real]
  rw [e] at h1
  have h2 := hasProd_ofReal_of_complex (fun v => by
    by_cases hv : v ∈ S <;> simp [Set.mulIndicator, hv]) h1
  have e2 : (fun v => ENNReal.ofReal ({v | v ∉ S}.mulIndicator
      (fun v => (m v (latV b v)).toReal) v)) = {v | v ∉ S}.mulIndicator (fun v => m v (latV b v)) := by
    funext v
    by_cases hv : v ∈ S
    · simp [Set.mulIndicator, hv]
    · simp [Set.mulIndicator, hv, ENNReal.ofReal_toReal (hfin v)]
  rw [e2] at h2
  exact ⟨_, ENNReal.ofReal_ne_top, (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ S})).2 h2⟩

theorem repr_change {F E : Type} [Field F] [Field E] [Algebra F E] {d d' : ℕ}
    (R : Type) [CommRing R] [Algebra F R] (b : Module.Basis (Fin d) F E)
    (b' : Module.Basis (Fin d') F E) (y : R ⊗[F] E) (k' : Fin d') :
    (Algebra.TensorProduct.basis R b').repr y k' =
      ∑ k, (Algebra.TensorProduct.basis R b).repr y k * algebraMap F R (b'.repr (b k) k') := by
  have hE : ∀ e : E, b'.repr e k' = ∑ k, b.repr e k * b'.repr (b k) k' := fun e => by
    conv_lhs => rw [← b.sum_repr e]
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, hE,
      map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_mul, mul_assoc]
  | add x y hx hy =>
    rw [map_add, Finsupp.add_apply, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, Finsupp.add_apply, add_mul]

theorem latCofin_holds : LatCofin := by
  intro F E _ _ _ _ a M d d' b b'
  have key : ∀ x : F, ∀ᶠ v in Filter.cofinite,
      algebraMap F (Fv F v) x ∈ (v.adicCompletionIntegers F : Set (Fv F v)) := fun x =>
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2
  have h1 : ∀ᶠ v in Filter.cofinite, ∀ k k', algebraMap F (Fv F v) (b'.repr (b k) k') ∈
      (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun k' => key _
  have h2 : ∀ᶠ v in Filter.cofinite, ∀ k' k, algebraMap F (Fv F v) (b.repr (b' k') k) ∈
      (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Filter.eventually_all.2 fun k' => Filter.eventually_all.2 fun k => key _
  filter_upwards [h1, h2] with v hv1 hv2
  ext Y
  simp only [latV, Set.mem_setOf_eq]
  constructor
  · intro hY x i k'
    rw [repr_change (Fv F v) b b']
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hY x i k) (hv1 k k')
  · intro hY x i k
    rw [repr_change (Fv F v) b' b]
    exact Subring.sum_mem _ fun k' _ => Subring.mul_mem _ (hY x i k') (hv2 k' k)

theorem rpTail_holds : RPTail := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet fibV d b hSB hmult
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact rpTail_gen b (fun v => fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) hSB hmult

end PI.VolStabSW.RestrProdA
end
end

section
noncomputable section

namespace PI.VolStabSW.RestrProdG

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Maps

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S]

theorem map_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ z) =
      sigR S σ (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem map_inclR (f : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR, Algebra.TensorProduct.map_tmul]

theorem map_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (x y : Fin n) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (gramR R σ J X x y) =
      gramR S σ J (fun x i => Algebra.TensorProduct.map f (AlgHom.id F E) (X x i)) x y := by
  simp only [gramR, hR, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, map_sigR,
    map_inclR]

end Maps

theorem t2_tensor_product {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type)
    [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    T2Space (R ⊗[F] E) := by
  let b := Module.finBasis F E
  refine T2Space.of_injective_continuous
    (f := fun y : R ⊗[F] E => fun k => PositiveNearLattice.crd b R y k) ?_
    (continuous_pi fun k => PositiveNearLattice.continuous_crd b R k)
  intro y y' h
  have h' : ∀ k, PositiveNearLattice.crd b R y k = PositiveNearLattice.crd b R y' k := fun k => congrFun h k
  rw [PositiveNearLattice.eq_sum_crd b R y, PositiveNearLattice.eq_sum_crd b R y']
  simp only [h']

theorem rpGram_holds : RPGram := by
  intro F E _ _ _ _ _ σ M J a T
  let b := Module.finBasis F E
  refine ⟨?_, ?_, fun v => ?_, ?_⟩
  · have : T2Space (AF F ⊗[F] E) := t2_tensor_product (AF F)
    have : T2Space (Matrix (Fin a) (Fin a) (AF F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → AF F ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (AF F) σ J)).isOpen_compl.measurableSet
  · have : T2Space (Ainf F ⊗[F] E) := t2_tensor_product (Ainf F)
    have : T2Space (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Ainf F ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (Ainf F) σ J)).measurableSet
  · have : LocallyCompactSpace (Fv F v) := locallyCompact_Fv F v
    have : T2Space (Fv F v ⊗[F] E) := t2_tensor_product (Fv F v)
    have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (Fv F v) σ J)).measurableSet
  · intro X hI hV
    have key : ∀ w w' : AF F ⊗[F] E,
        Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) w =
          Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) w' →
        (∀ v, Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
            (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w) =
          Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
            (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w')) → w = w' := by
      intro w w' h1 h2
      rw [PositiveNearLattice.eq_sum_crd b (AF F) w, PositiveNearLattice.eq_sum_crd b (AF F) w']
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      have e1 := congrArg (fun u => PositiveNearLattice.crd b (Ainf F) u k) h1
      simp only [PositiveNearLattice.crd_map] at e1
      refine Prod.ext e1 (FiniteAdeleRing.ext (K := F) fun v => ?_)
      have e2 := congrArg (fun u => PositiveNearLattice.crd b (Fv F v) u k) (h2 v)
      simp only [PositiveNearLattice.crd_map] at e2
      exact e2
    funext x y
    refine key _ _ ?_ fun v => ?_
    · rw [map_gramR, Matrix.map_apply, map_inclR]
      exact congrFun (congrFun hI x) y
    · rw [map_gramR, map_gramR, Matrix.map_apply, map_inclR, map_inclR]
      exact congrFun (congrFun (hV v) x) y

end PI.VolStabSW.RestrProdG
end
end

section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct

namespace RestrictedProductFiber

theorem finite_on_compacts {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [OpensMeasurableSpace V] [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (U : Set V) (hU : IsOpen U)
    (ν : Measure X) (B : Set X) (fib : X → Measure V) (h : IsFibreFamily μ f ι U ν B fib)
    (b : X) (hb : b ∈ B) (hC : IsClosed (f ⁻¹' {ι b})) (hCU : f ⁻¹' {ι b} ⊆ U) :
    IsFiniteMeasureOnCompacts (fib b) := by
  refine ⟨fun K hK => ?_⟩
  have hK' : IsCompact (K ∩ f ⁻¹' {ι b}) := hK.inter_right hC
  obtain ⟨φ, h1, hφc, hφU, _h01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK' hU (Set.inter_subset_right.trans hCU)
  have hint : Integrable φ (fib b) :=
    (h.2.2 φ φ.continuous hφc hφU).1 b hb
  have hnull : fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0 := h.1 b
  have hM : fib b (K ∩ f ⁻¹' {ι b}) ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib b) := by
    have hm : AEMeasurable (fun x => ENNReal.ofReal (φ x)) (fib b) :=
      (ENNReal.continuous_ofReal.comp φ.continuous).measurable.aemeasurable
    calc fib b (K ∩ f ⁻¹' {ι b}) ≤ fib b {x | 1 ≤ ENNReal.ofReal (φ x)} := by
          refine measure_mono fun x hx => ?_
          simp only [Set.mem_ofPred_eq, h1 hx, Pi.one_apply, ENNReal.ofReal_one, le_refl]
      _ = 1 * fib b {x | 1 ≤ ENNReal.ofReal (φ x)} := (one_mul _).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib b) := mul_meas_ge_le_lintegral₀ hm 1
  calc fib b K ≤ fib b ((K ∩ f ⁻¹' {ι b}) ∪ (f ⁻¹' {ι b} ∩ U)ᶜ) := by
        refine measure_mono fun x hx => ?_
        by_cases hx2 : x ∈ f ⁻¹' {ι b} ∩ U
        · exact Or.inl ⟨hx, hx2.1⟩
        · exact Or.inr hx2
    _ ≤ fib b (K ∩ f ⁻¹' {ι b}) + fib b (f ⁻¹' {ι b} ∩ U)ᶜ := measure_union_le _ _
    _ = fib b (K ∩ f ⁻¹' {ι b}) := by rw [hnull, add_zero]
    _ < ⊤ := lt_of_le_of_lt hM hint.lintegral_lt_top

theorem fib_props {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (hTF : TensFacts F E σ M J a R)
    (T : Matrix (Fin a) (Fin a) E) (hT : ∀ i j, σ (T j i) = T i j) (hdet : T.det ≠ 0)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    (fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E))
    (h : IsFibreFamily μ (gramR R σ J) Subtype.val
      {X | LinearIndependent (R ⊗[F] E) X} ν Set.univ fib) :
    SigmaFinite (fib (hermOf R σ T hT)) ∧
    ∀ Φ : (Fin a → Fin M → R ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf R σ T hT)) := by
  obtain ⟨h1, h2, h3, _h4, h5, _h6, h7⟩ := hTF
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → R ⊗[F] E))
  have hC : IsClosed (gramR R σ J ⁻¹' {((hermOf R σ T hT : HermR R σ a) :
      Matrix (Fin a) (Fin a) (R ⊗[F] E))}) := isClosed_singleton.preimage h5
  have hCU : gramR R σ J ⁻¹' {((hermOf R σ T hT : HermR R σ a) :
      Matrix (Fin a) (Fin a) (R ⊗[F] E))} ⊆ {X | LinearIndependent (R ⊗[F] E) X} := by
    intro X hX
    have hX' : gramR R σ J X = ((hermOf R σ T hT : HermR R σ a) :
        Matrix (Fin a) (Fin a) (R ⊗[F] E)) := hX
    have hu := isUnit_det_hermOf R σ T hT hdet
    rw [← hX'] at hu
    exact linIndep_of_isUnit_det R σ J X hu
  have hfin := finite_on_compacts μ (gramR R σ J) Subtype.val _ h7 ν Set.univ fib h
    (hermOf R σ T hT) (Set.mem_univ _) hC hCU
  have : SigmaCompactSpace (Fin a → Fin M → R ⊗[F] E) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  exact ⟨inferInstance, fun Φ hc hs => hc.integrable_of_hasCompactSupport hs⟩

end RestrictedProductFiber

theorem rpFib_holds : RPFib := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hI, hV⟩ := tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  refine ⟨fun μ ν fib h => RestrictedProductFiber.fib_props σ J a (Ainf F) hI _ hT hdet μ ν fib h,
    fun v μ ν fib h => RestrictedProductFiber.fib_props σ J a (Fv F v) (hV v) _ hT hdet μ ν fib h⟩

end PI.VolStabSW
end
end

section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct RestrictedProduct

namespace RestrictedProductGluing

open PositiveNearLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {M a d : ℕ} (b : Module.Basis (Fin d) F E)

def good : Set ((Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) :=
  {p | ∀ᶠ v in cofinite, p.2 v ∈ latV b v}

def mkAf (x : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in cofinite, x v ∈ v.adicCompletionIntegers F) : Af F :=
  (⟨x, h⟩ : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

omit [FiniteDimensional F E] in
theorem evalV_mkAf (x : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in cofinite, x v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (mkAf x h) = x v := rfl

open Classical in

def finAd (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : Af F :=
  if h : p ∈ good b then
    mkAf (fun v => crd b (Fv F v) (p.2 v i j) k)
      ((show ∀ᶠ v in cofinite, p.2 v ∈ latV b v from h).mono fun _ hv => hv i j k)
  else 0

def crdA (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : AF F :=
  pairA F (crd b (Ainf F) (p.1 i j) k) (finAd b p i j k)

def glue (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) :
    Fin a → Fin M → AF F ⊗[F] E :=
  fun i j => (Algebra.TensorProduct.basis (AF F) b).equivFun.symm (fun k => crdA b p i j k)

theorem crd_glue (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : crd b (AF F) (glue b p i j) k = crdA b p i j k := by
  show (Algebra.TensorProduct.basis (AF F) b).repr
      ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm fun k => crdA b p i j k) k = _
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem measurableSet_good :
    MeasurableSet (good (F := F) (E := E) (M := M) (a := a) b) := by
  have e : good (F := F) (E := E) (M := M) (a := a) b = ⋃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ⋂ v, ⋂ (_ : v ∉ S), {p | p.2 v ∈ latV b v} := by
    ext p
    simp only [good, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, eventually_cofinite]
    constructor
    · intro h
      exact ⟨h.toFinset, fun v hv => by
        by_contra hc
        exact hv (h.mem_toFinset.2 hc)⟩
    · rintro ⟨S, hS⟩
      exact S.finite_toSet.subset fun v hv => by
        by_contra hc
        exact hv (hS v hc)
  rw [e]
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine MeasurableSet.iUnion fun S => MeasurableSet.iInter fun v =>
    MeasurableSet.iInter fun _ => ?_
  exact ((measurable_pi_apply v).comp measurable_snd)
    (isClopen_latV b v a M).isOpen.measurableSet

def coeA (x : Af F) : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v := fun v => evalV F v x

theorem measurableEmbedding_coeA : MeasurableEmbedding (coeA (F := F)) := by
  have : BorelSpace (Af F) := ⟨rfl⟩
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have : PolishSpace (Af F) := TopoPolish.polish_of_lcsc (Af F)
  refine Continuous.measurableEmbedding ?_ ?_
  · exact continuous_pi fun v => by exact RestrictedProduct.continuous_eval v
  · intro x y h
    exact Subtype.ext (funext fun v => congrFun h v)

theorem measurable_finAd (i : Fin a) (j : Fin M) (k : Fin d) :
    Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => finAd b p i j k) := by
  classical
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine (measurableEmbedding_coeA (F := F)).measurable_comp_iff.1 ?_
  have e : (coeA (F := F)) ∘ (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => finAd b p i j k) =
      (good b).piecewise (fun p v => crd b (Fv F v) (p.2 v i j) k) 0 := by
    funext p
    by_cases hp : p ∈ good b
    · funext v
      rw [Set.piecewise_eq_of_mem _ _ _ hp]
      simp only [Function.comp, coeA]
      rw [finAd, dif_pos hp, evalV_mkAf]
    · funext v
      rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      simp only [Function.comp, coeA, Pi.zero_apply]
      rw [finAd, dif_neg hp, map_zero]
  rw [e]
  refine Measurable.piecewise (measurableSet_good b) ?_ measurable_const
  exact measurable_pi_lambda _ fun v => (continuous_crd b (Fv F v) k).measurable.comp
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply v).comp measurable_snd)))

theorem measurable_crdA (i : Fin a) (j : Fin M) (k : Fin d) :
    Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => crdA b p i j k) := by
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : BorelSpace (Af F) := ⟨rfl⟩
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hc : Continuous (fun q : Ainf F × Af F => pairA F q.1 q.2) := continuous_id
  have hx : Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) =>
      crd b (Ainf F) (p.1 i j) k) :=
    (continuous_crd b (Ainf F) k).measurable.comp
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst))
  exact hc.measurable.comp (hx.prodMk (measurable_finAd b i j k))

theorem measurable_glue :
    Measurable (glue (F := F) (E := E) (M := M) (a := a) b) := by
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have hL : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap)
  exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    hL.measurable.comp (measurable_pi_lambda _ fun k => measurable_crdA b i j k)

theorem glue_spec (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (hp : p ∈ good b) :
    projInf (glue b p) = p.1 ∧ ∀ v, projV v (projFin (glue b p)) = p.2 v := by
  refine ⟨?_, fun v => ?_⟩
  · funext i j
    refine (Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_
    show crd b (Ainf F) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (glue b p i j)) k =
      crd b (Ainf F) (p.1 i j) k
    rw [crd_map, crd_glue]
    rfl
  · funext i j
    refine (Algebra.TensorProduct.basis (Fv F v) b).ext_elem fun k => ?_
    show crd b (Fv F v) (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (glue b p i j))) k =
      crd b (Fv F v) (p.2 v i j) k
    rw [crd_map, crd_map, crd_glue]
    show evalV F v (finAd b p i j k) = _
    rw [finAd, dif_pos hp, evalV_mkAf]

end RestrictedProductGluing

theorem rpGlue_holds : RPGlue := by
  intro F E _ _ _ _ _ M a d b
  exact ⟨RestrictedProductGluing.glue b, RestrictedProductGluing.measurable_glue b,
    fun p hp => RestrictedProductGluing.glue_spec b p hp⟩

end PI.VolStabSW
end
end

section
noncomputable section

namespace PI.VolStabSW.RPA

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable (m : ∀ i, Measure (W i)) (L : ∀ i, Set (W i))

def am (i : ι) : ℝ≥0 := (m i (L i)).toNNReal

def tl (S : Finset ι) : ℝ≥0 := ∏' i : {i // i ∉ S}, am m L i.1

def TailH : Prop :=
  ∀ S : Finset ι, ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ HasProd (fun i : {i // i ∉ S} => m i.1 (L i.1)) c

variable {m L}

lemma hasProd_tl (hT : TailH m L) (S : Finset ι) :
    HasProd (fun i : {i // i ∉ S} => am m L i.1) (tl m L S) := by

  obtain ⟨c, hc, h⟩ := hT S
  have h2 : HasProd (fun i : {i // i ∉ S} => am m L i.1) c.toNNReal := by
    have := (ENNReal.tendsto_toNNReal hc).comp h
    unfold HasProd at this ⊢
    convert this using 2 with s
    simp [Function.comp, ENNReal.toNNReal_prod, am]
  unfold tl
  rw [h2.tprod_eq]
  exact h2

lemma hasProd_ind (hT : TailH m L) (S : Finset ι) :
    HasProd (({i | i ∉ S} : Set ι).mulIndicator (am m L)) (tl m L S) := hasProd_subtype_iff_mulIndicator.mp (hasProd_tl hT S)

lemma tl_split [DecidableEq ι] (hT : TailH m L) {S T : Finset ι} (h : S ⊆ T) :
    tl m L S = (∏ i ∈ T \ S, am m L i) * tl m L T := by

  have h1 := hasProd_ind hT S
  have h2 := hasProd_ind hT T
  have h3 : HasProd ((↑(T \ S) : Set ι).mulIndicator (am m L)) (∏ i ∈ T \ S, am m L i) := by
    have : HasProd ((↑(T \ S) : Set ι).mulIndicator (am m L))
        (∏ b ∈ T \ S, (↑(T \ S) : Set ι).mulIndicator (am m L) b) :=
      hasProd_prod_of_ne_finset_one (s := T \ S) (f := (↑(T \ S) : Set ι).mulIndicator (am m L))
      (fun b hb => by rw [Set.mulIndicator_apply, if_neg (by simpa using hb)])
    rwa [Finset.prod_congr rfl (fun b hb => by rw [Set.mulIndicator_apply, if_pos (by simpa using hb)])] at this
  have h4 := h3.mul h2
  have e : ({i | i ∉ S} : Set ι).mulIndicator (am m L) =
      (↑(T \ S) : Set ι).mulIndicator (am m L) * ({i | i ∉ T} : Set ι).mulIndicator (am m L) := by
    funext i
    simp only [Pi.mul_apply, Set.mulIndicator_apply, Set.mem_setOf_eq, Finset.coe_sdiff, Set.mem_diff,
      Finset.mem_coe]
    by_cases hT' : i ∈ T <;> by_cases hS : i ∈ S <;> simp [hT', hS] <;> exact absurd (h hS) hT'
  rw [e] at h1
  exact h1.unique h4

lemma tl_zero [DecidableEq ι] (hT : TailH m L) {S : Finset ι} {i : ι} (hi : i ∉ S)
    (h0 : am m L i = 0) : tl m L S = 0 := by

  rw [tl_split hT (Finset.subset_insert i S), Finset.prod_eq_zero (i := i) (by simp [hi]) h0, zero_mul]

variable (m L)

def Pn (i : ι) : Measure (W i) := (m i (L i))⁻¹ • (m i).restrict (L i)

lemma Pn_prob {i : ι} (h : m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤) : IsProbabilityMeasure (Pn m L i) := by

  constructor
  simp only [Pn, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h.1 h.2

open Classical in

def Qm (S : Finset ι) : Measure (∀ i : {i // i ∉ S}, W i) :=
  if h : ∀ i, i ∉ S → m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤ then
    haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) := fun i => Pn_prob m L (h i.1 i.2)
    tl m L S • Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1)
  else 0

instance Qm_fin (S : Finset ι) : IsFiniteMeasure (Qm m L S) := by
  unfold Qm; split_ifs with h
  · haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) :=
      fun i => Pn_prob m L (h i.1 i.2)
    infer_instance
  · infer_instance

def Rm (S : Finset ι) : Measure (∀ i : {i // i ∈ S}, W i) :=
  Measure.pi (fun i : {i // i ∈ S} => (m i.1).restrict (L i.1)ᶜ)

open Classical in

def eS (S : Finset ι) : (∀ i, W i) ≃ᵐ (∀ i : {i // i ∈ S}, W i) × (∀ i : {i // i ∉ S}, W i) :=
  MeasurableEquiv.piEquivPiSubtypeProd W (fun i => i ∈ S)

def kap [∀ i, SigmaFinite (m i)] (S : Finset ι) : Measure (∀ i, W i) :=
  ((Rm m L S).prod (Qm m L S)).map (eS S).symm

open Classical in

def mu (S : Finset ι) (i : ι) : Measure (W i) :=
  if i ∈ S then (m i).restrict (L i)ᶜ else (m i).restrict (L i)

open Classical in
lemma eS_symm_apply (S : Finset ι) (p : (∀ i : {i // i ∈ S}, W i) × (∀ i : {i // i ∉ S}, W i))
    (i : ι) : (eS S).symm p i = if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩ := by

  first
    | rfl
    | simp [eS, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]

variable [∀ i, SigmaFinite (m i)]

instance kap_sfin (S : Finset ι) : SFinite (kap m L S) := by unfold kap Rm; infer_instance

variable {m L}

lemma kap_eval_null {S : Finset ι} {i : ι} {A : Set (W i)} (hA : MeasurableSet A)
    (h : mu m L S i A = 0) : kap m L S {x | x i ∈ A} = 0 := by

  classical
  have hs : MeasurableSet {x : ∀ i, W i | x i ∈ A} := measurable_pi_apply i hA
  unfold kap
  rw [Measure.map_apply (eS S).symm.measurable hs]
  by_cases hiS : i ∈ S
  · have e : (eS S).symm ⁻¹' {x | x i ∈ A} =
        (Function.eval (⟨i, hiS⟩ : {i // i ∈ S}) ⁻¹' A) ×ˢ Set.univ := by
      ext p; simp [eS_symm_apply, hiS]
    have h0 : ((m i).restrict (L i)ᶜ) A = 0 := by simpa [mu, hiS] using h
    have h1 : Rm m L S (Function.eval (⟨i, hiS⟩ : {i // i ∈ S}) ⁻¹' A) = 0 := by
      unfold Rm
      exact Measure.pi_eval_preimage_null _ h0
    rw [e, Measure.prod_prod, h1, zero_mul]
  · have e : (eS S).symm ⁻¹' {x | x i ∈ A} =
        Set.univ ×ˢ (Function.eval (⟨i, hiS⟩ : {i // i ∉ S}) ⁻¹' A) := by
      ext p; simp [eS_symm_apply, hiS]
    have h0 : ((m i).restrict (L i)) A = 0 := by simpa [mu, hiS] using h
    have h1 : Qm m L S (Function.eval (⟨i, hiS⟩ : {i // i ∉ S}) ⁻¹' A) = 0 := by
      unfold Qm
      split_ifs with hQ
      · haveI : ∀ j : {i // i ∉ S}, IsProbabilityMeasure (Pn m L j.1) := fun j => Pn_prob m L (hQ j.1 j.2)
        rw [Measure.smul_apply, ← Measure.map_apply (show Measurable (Function.eval (⟨i, hiS⟩ : {i // i ∉ S}) :
          (∀ j : {i // i ∉ S}, W j.1) → W i) from measurable_pi_apply _) hA,
          Measure.infinitePi_map_eval]
        simp [Pn, h0]
      · simp
    rw [e, Measure.prod_prod, h1, mul_zero]

lemma kap_ae [Countable ι] (hLm : ∀ i, MeasurableSet (L i)) (S : Finset ι) :
    ∀ᵐ x ∂kap m L S, ∀ i, (i ∈ S → x i ∉ L i) ∧ (i ∉ S → x i ∈ L i) := by

  rw [ae_all_iff]
  intro i
  by_cases hiS : i ∈ S
  · have h0 : kap m L S {x | x i ∈ L i} = 0 :=
      kap_eval_null (hLm i) (by simp [mu, hiS, Measure.restrict_apply (hLm i)])
    rw [ae_iff]
    simpa [hiS] using h0
  · have h0 : kap m L S {x | x i ∈ (L i)ᶜ} = 0 :=
      kap_eval_null (hLm i).compl (by simp [mu, hiS, Measure.restrict_apply (hLm i).compl])
    rw [ae_iff]
    simpa [hiS] using h0

end PI.VolStabSW.RPA
end
end

section
noncomputable section

namespace PI.VolStabSW.RPA

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable {m : ∀ i, Measure (W i)} {L : ∀ i, Set (W i)} [∀ i, SigmaFinite (m i)]

instance Rm_sf (S : Finset ι) : SigmaFinite (Rm m L S) := by unfold Rm; infer_instance

lemma Qm_integral [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun z => ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j)) (Qm m L S) ∧
    ∫ z, ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j) ∂Qm m L S =
      (∏ i ∈ T \ S, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by
  classical
  set T' : Finset {i // i ∉ S} := T.subtype (fun i => i ∉ S) with hT'
  unfold Qm
  split_ifs with hh
  · haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) :=
      fun i => Pn_prob m L (hh i.1 i.2)
    have hP : ∀ j : {i // i ∉ S}, Integrable (g j.1) (Pn m L j.1) := fun j =>
      ((hg j.1).restrict).smul_measure (ENNReal.inv_ne_top.2 (hh j.1 j.2).1)
    let F : (∀ j : T', W j.1.1) → ℂ := fun y => ∏ j : T', g j.1.1 (y j)
    have hpi : Integrable F (Measure.pi (fun j : T' => Pn m L j.1.1)) :=
      Integrable.fintype_prod_dep (fun j => hP j.1)
    have hre : (fun z : (∀ j : {i // i ∉ S}, W j.1) => ∏ j ∈ T', g j.1 (z j)) =
        fun z => F (T'.restrict z) := by
      funext z
      exact (Finset.prod_coe_sort T' (fun j => g j.1 (z j))).symm
    have hmap := Measure.infinitePi_map_restrict (μ := fun j : {i // i ∉ S} => Pn m L j.1) (I := T')
    have hpi' : Integrable F ((Measure.infinitePi fun j : {i // i ∉ S} => Pn m L j.1).map
        T'.restrict) := by rw [hmap]; exact hpi
    have hint : Integrable (fun z => F (T'.restrict z))
        (Measure.infinitePi fun j : {i // i ∉ S} => Pn m L j.1) :=
      (integrable_map_measure hpi'.aestronglyMeasurable
        (Finset.measurable_restrict _).aemeasurable).1 hpi'
    rw [hre]
    refine ⟨hint.smul_measure_nnreal, ?_⟩
    rw [integral_smul_nnreal_measure,
      integral_restrict_infinitePi (fun j : {i // i ∉ S} => Pn m L j.1) hpi.aestronglyMeasurable]
    simp only [F]
    rw [integral_fintype_prod_eq_prod]
    simp only [Pn, integral_smul_measure]
    rw [Finset.prod_coe_sort T' (fun j => ((m j.1 (L j.1))⁻¹.toReal • ∫ w, g j.1 w ∂(m j.1).restrict (L j.1))),
      hT', Finset.prod_subtype_eq_prod_filter (f := fun i => ((m i (L i))⁻¹.toReal • ∫ w, g i w ∂(m i).restrict (L i))),
      ← Finset.sdiff_eq_filter, tl_split hT hST]
    have hmu : ∀ i ∈ T \ S, ∫ w, g i w ∂(mu m L S i) = ∫ w, g i w ∂(m i).restrict (L i) := by
      intro i hi
      rw [mu, if_neg (Finset.mem_sdiff.1 hi).2]
    rw [Finset.prod_congr rfl hmu]
    have hone : (∏ i ∈ T \ S, ((am m L i : ℝ) : ℂ)) * (∏ i ∈ T \ S, (((m i (L i))⁻¹.toReal : ℝ) : ℂ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one (fun i hi => ?_)
      have h1 := hh i (Finset.mem_sdiff.1 hi).2
      rw [← Complex.ofReal_mul, am, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_inv,
        mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h1.1, h1.2⟩), Complex.ofReal_one]
    simp only [NNReal.smul_def, Complex.real_smul, NNReal.coe_mul, NNReal.coe_prod,
      Complex.ofReal_mul, Complex.ofReal_prod, Finset.prod_mul_distrib]
    linear_combination (((tl m L T : ℝ) : ℂ) * ∏ i ∈ T \ S, ∫ w, g i w ∂(m i).restrict (L i)) * hone
  · push_neg at hh
    obtain ⟨i, hiS, hi⟩ := hh
    have h0 : m i (L i) = 0 := by
      by_contra h; exact hfin i (hi h)
    refine ⟨integrable_zero_measure, ?_⟩
    rw [integral_zero_measure]
    by_cases hiT : i ∈ T
    · rw [Finset.prod_eq_zero (i := i) (Finset.mem_sdiff.2 ⟨hiT, hiS⟩), zero_mul]
      rw [mu, if_neg hiS, Measure.restrict_eq_zero.2 h0, integral_zero_measure]
    · rw [tl_zero hT hiT (by simp [am, h0])]
      simp

lemma kap_integral [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun x => ∏ i ∈ T, g i (x i)) (kap m L S) ∧
    ∫ x, ∏ i ∈ T, g i (x i) ∂kap m L S =
      (∏ i ∈ T, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by
  classical
  set T' : Finset {i // i ∉ S} := T.subtype (fun i => i ∉ S) with hT'
  have hfun : ∀ p, (fun x : (∀ i, W i) => ∏ i ∈ T, g i (x i)) ((eS S).symm p) =
      (∏ i : {i // i ∈ S}, g i.1 (p.1 i)) * (∏ j ∈ T', g j.1 (p.2 j)) := by
    intro p
    simp only
    rw [← Finset.prod_filter_mul_prod_filter_not T (fun i => i ∈ S)]
    congr 1
    · rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hST, ← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [eS_symm_apply, dif_pos i.2]
    · rw [← Finset.prod_subtype_eq_prod_filter]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [eS_symm_apply, dif_neg j.2]
  have hR : Integrable (fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i))
      (Rm m L S) := by
    unfold Rm; exact Integrable.fintype_prod_dep (fun i => (hg i.1).restrict)
  obtain ⟨hQi, hQ⟩ := Qm_integral hfin hT hST g hg
  rw [← hT'] at hQi hQ
  have hcomp : (fun x : (∀ i, W i) => ∏ i ∈ T, g i (x i)) ∘ (eS S).symm =
      fun p => (∏ i : {i // i ∈ S}, g i.1 (p.1 i)) * (∏ j ∈ T', g j.1 (p.2 j)) :=
    funext hfun
  refine ⟨?_, ?_⟩
  · unfold kap
    rw [integrable_map_equiv, hcomp]
    exact Integrable.mul_prod (μ := Rm m L S) (ν := Qm m L S)
      (f := fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i))
      (g := fun z => ∏ j ∈ T', g j.1 (z j)) hR hQi
  · unfold kap
    rw [integral_map_equiv]
    refine (integral_congr_ae (ae_of_all _ hfun)).trans ?_
    rw [integral_prod_mul (fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i))
      (fun z : (∀ i : {i // i ∉ S}, W i) => ∏ j ∈ T', g j.1 (z j)), hQ, Rm, integral_fintype_prod_eq_prod,
      ← Finset.prod_sdiff hST]
    have hS : ∏ i : {i // i ∈ S}, ∫ w, g i.1 w ∂(m i.1).restrict (L i.1)ᶜ =
        ∏ i ∈ S, ∫ w, g i w ∂(mu m L S i) := by
      rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [mu, if_pos i.2]
    rw [hS]
    ring

end PI.VolStabSW.RPA
end
end

section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Filter Finset PI.VolStabSW.RPA
open scoped NNReal ENNReal

theorem rpAbs_holds : RPAbs := by
  intro ι _ W _ m _ L hLm hfin hT
  classical
  have hT' : TailH m L := hT
  refine ⟨Measure.sum (kap m L), inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
    intro S
    have := kap_ae (m := m) (L := L) hLm S
    rw [ae_iff] at this
    refine measure_mono_null (fun x hx => ?_) this
    intro hgood
    apply hx
    rw [Filter.eventually_cofinite]
    refine (S.finite_toSet).subset (fun i hi => ?_)
    by_contra hiS
    exact hi ((hgood i).2 hiS)
  · intro i C hC hC0
    rw [Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
    intro S
    refine kap_eval_null (m := m) (L := L) (S := S) (A := Cᶜ) hC.compl ?_
    unfold mu
    split_ifs <;> exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hC0.le)
  · intro f hf hcof
    have hfin0 := Filter.eventually_cofinite.1 hcof
    set S0 := hfin0.toFinset with hS0def
    have hS0 : ∀ i, i ∉ S0 → f i = (L i).indicator 1 := fun i hi => by
      by_contra h; exact hi (hfin0.mem_toFinset.2 h)
    set G : (∀ i, W i) → ℂ := fun x => ∏ i ∈ S0, f i (x i) with hG
    have hae : ∀ S : Finset ι, (fun x => ∏ᶠ i, f i (x i)) =ᵐ[kap m L S]
        fun x => if S ⊆ S0 then G x else 0 := by
      intro S
      filter_upwards [kap_ae (m := m) (L := L) hLm S] with x hx
      have hsupp : Function.mulSupport (fun i => f i (x i)) ⊆ ↑(S ∪ S0) := by
        intro i hi
        by_contra hn
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
        apply hi
        simp only [hS0 i hn.2, Set.indicator_of_mem ((hx i).2 hn.1), Pi.one_apply]
      rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
      by_cases hsub : S ⊆ S0
      · rw [if_pos hsub, Finset.union_eq_right.2 hsub]
      · rw [if_neg hsub]
        obtain ⟨j, hjS, hj0⟩ := Finset.not_subset.1 hsub
        refine Finset.prod_eq_zero (Finset.mem_union_left _ hjS) ?_
        simp [hS0 j hj0, (hx j).1 hjS]
    have hK : ∀ S ⊆ S0, Integrable G (kap m L S) ∧
        ∫ x, G x ∂kap m L S = (∏ i ∈ S0, ∫ w, f i w ∂(mu m L S i)) * (tl m L S0 : ℂ) :=
      fun S hS => kap_integral hfin hT' hS f hf
    have hIntS : ∀ S, Integrable (fun x => ∏ᶠ i, f i (x i)) (kap m L S) := by
      intro S
      refine Integrable.congr ?_ (hae S).symm
      by_cases hs : S ⊆ S0
      · simp only [hs, if_true]; exact (hK S hs).1
      · simp only [hs, if_false]; exact integrable_zero _ _ _
    have hzero : ∀ S, S ∉ S0.powerset → ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S = 0 ∧
        ∫ x, ‖∏ᶠ i, f i (x i)‖ ∂kap m L S = 0 := by
      intro S hS
      have hs : ¬ S ⊆ S0 := fun h => hS (Finset.mem_powerset.2 h)
      refine ⟨?_, ?_⟩
      · rw [integral_congr_ae (hae S)]; simp [hs]
      · refine (integral_congr_ae ((hae S).fun_comp norm)).trans ?_
        simp [hs, Function.comp_def]
    have hint : Integrable (fun x => ∏ᶠ i, f i (x i)) (Measure.sum (kap m L)) :=
      integrable_sum_measure hIntS (summable_of_ne_finset_zero (s := S0.powerset)
        (fun S hS => (hzero S hS).2))
    refine ⟨hint, ?_⟩
    rw [integral_sum_measure hint, tsum_eq_sum (s := S0.powerset) (fun S hS => (hzero S hS).1)]
    have hsumS : ∑ S ∈ S0.powerset, ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S =
        ∑ S ∈ S0.powerset, (∏ i ∈ S0, ∫ w, f i w ∂(mu m L S i)) * (tl m L S0 : ℂ) := by
      refine Finset.sum_congr rfl (fun S hS => ?_)
      have hs := Finset.mem_powerset.1 hS
      rw [integral_congr_ae (hae S)]
      simp only [hs, if_true]
      exact (hK S hs).2
    rw [hsumS, ← Finset.sum_mul]
    have hsplit : ∀ i, ∫ w, f i w ∂(m i) =
        (∫ w, f i w ∂(m i).restrict (L i)ᶜ) + ∫ w, f i w ∂(m i).restrict (L i) := fun i => by
      rw [add_comm]; exact (integral_add_compl (hLm i) (hf i)).symm
    have hprodadd : ∑ S ∈ S0.powerset, ∏ i ∈ S0, ∫ w, f i w ∂(mu m L S i) =
        ∏ i ∈ S0, ∫ w, f i w ∂(m i) := by
      rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_add]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      have hs := Finset.mem_powerset.1 hS
      rw [← Finset.prod_sdiff hs, mul_comm]
      congr 1
      · refine Finset.prod_congr rfl (fun i hi => ?_); rw [mu, if_pos hi]
      · refine Finset.prod_congr rfl (fun i hi => ?_); rw [mu, if_neg (Finset.mem_sdiff.1 hi).2]
    rw [hprodadd]
    have h1 : HasProd (fun i => (((({i | i ∉ S0} : Set ι).mulIndicator (am m L) i : ℝ≥0) : ℝ) : ℂ))
        (((tl m L S0 : ℝ≥0) : ℝ) : ℂ) := by
      have := (hasProd_ind hT' S0).map
        (((Complex.ofRealHom : ℝ →+* ℂ).toMonoidHom).comp (NNReal.toRealHom.toMonoidHom))
        (Complex.continuous_ofReal.comp NNReal.continuous_coe)
      exact this
    have h2 : HasProd (fun i => if i ∈ S0 then ∫ w, f i w ∂(m i) else 1)
        (∏ i ∈ S0, ∫ w, f i w ∂(m i)) := by
      have : HasProd (fun i => if i ∈ S0 then ∫ w, f i w ∂(m i) else 1)
          (∏ i ∈ S0, (if i ∈ S0 then ∫ w, f i w ∂(m i) else 1)) :=
        hasProd_prod_of_ne_finset_one (fun b hb => if_neg hb)
      convert this using 1
      exact (Finset.prod_congr rfl (fun i hi => if_pos hi)).symm
    have h3 := h2.mul h1
    convert h3 using 1
    funext i
    by_cases hi : i ∈ S0
    · simp [hi]
    · have hmem : i ∈ ({i | i ∉ S0} : Set ι) := hi
      rw [if_neg hi, one_mul, Set.mulIndicator_of_mem hmem, hS0 i hi,
        integral_indicator (hLm i)]
      simp [am, Measure.real]
      exact (ENNReal.coe_toNNReal_eq_toReal _).symm

end PI.VolStabSW
end
end

section
namespace PI.VolStabSW

theorem restrProd_holds : RestrProd :=
  restrProd_of rpAbs_holds rpFib_holds rpGlue_holds RestrProdG.rpGram_holds
    RestrProdA.rpTail_holds RestrProdA.latCofin_holds

end PI.VolStabSW
end
