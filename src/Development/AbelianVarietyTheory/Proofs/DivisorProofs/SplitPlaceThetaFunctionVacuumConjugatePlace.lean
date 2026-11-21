import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.AdelicTraceNondeg

theorem trace_one_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R]
    [Algebra F R] (e : E) : Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem eq_zero_of_trace_mul {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [CommRing R]
    [Algebra F R] (m : R ⊗[F] E) (h : ∀ z : R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (m * z) = 0) : m = 0 := by
  let b := Module.finBasis F E
  let d := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b
  let bA := Algebra.TensorProduct.basis R b
  have key : ∀ j, bA.repr m j = 0 := by
    intro j
    have hj := h ((1 : R) ⊗ₜ[F] d j)
    rw [← bA.sum_repr m, Finset.sum_mul, map_sum] at hj
    rw [← hj, Finset.sum_eq_single j]
    · rw [Algebra.TensorProduct.basis_apply, smul_mul_assoc, map_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        trace_one_tmul, smul_eq_mul]
      have := (Algebra.traceForm F E).apply_dualBasis_left (traceForm_nondegenerate F E) b j j
      rw [Algebra.traceForm_apply, mul_comm] at this
      rw [this]; simp
    · intro i _ hij
      rw [Algebra.TensorProduct.basis_apply, smul_mul_assoc, map_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        trace_one_tmul, smul_eq_mul]
      have := (Algebra.traceForm F E).apply_dualBasis_left (traceForm_nondegenerate F E) b j i
      rw [Algebra.traceForm_apply, mul_comm] at this
      rw [this, if_neg hij, map_zero, mul_zero]
    · intro hj'; exact absurd (Finset.mem_univ j) hj'
  exact bA.repr.injective (by ext j; simp [key j])

theorem trace_pairing_nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ m : AEF F E, m ≠ 0 → ∃ z : AEF F E, ψ (Algebra.trace (AF F) (AEF F E) (m * z)) ≠ 1 := by
  intro F E _ _ _ _ _ ψ hψ m hm
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Algebra.IsSeparable F E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  by_contra hne
  push_neg at hne
  apply hm
  refine eq_zero_of_trace_mul m fun z => ?_
  refine GlobalTheory.DiagNonvan.eq_zero_of_psi_mul hψ _ fun y => ?_
  have e1 : Algebra.trace (AF F) (AEF F E) (m * z) * y = Algebra.trace (AF F) (AEF F E) (m * (y • z)) := by
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rw [e1]
  exact hne _

example : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ m : AEF F E, m ≠ 0 → ∃ z : AEF F E, ψ (Algebra.trace (AF F) (AEF F E) (m * z)) ≠ 1 :=
  trace_pairing_nondeg

end GlobalTheory.AdelicTraceNondeg
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitPairNondegF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}

variable (σ JS JT) in

def pairMat (y : WOF F E nS nT) : Matrix (Fin nS) (Fin nT) (AEF F E) :=
  (JS⁻¹).map (incAF F E) * (y.map (cAF σ))ᵀ * JT.map (incAF F E)

theorem pairMat_apply (y : WOF F E nS nT) (a : Fin nS) (d : Fin nT) :
    pairMat σ JS JT y a d = ∑ b, ∑ c, incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) := by
  simp only [pairMat, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem hOF_single (y : WOF F E nS nT) (d₀ : Fin nT) (a₀ : Fin nS) (t : AEF F E) :
    hOF σ JS JT (Matrix.single d₀ a₀ t) y = pairMat σ JS JT y a₀ d₀ * t := by
  rw [pairMat_apply, Finset.sum_mul, hOF, Finset.sum_eq_single a₀]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single d₀]
    · rw [Matrix.single_apply_same]
    · intro d _ hd
      rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hd h.1.symm), mul_zero]
    · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => ha h.2.symm), mul_zero]
  · simp

theorem pairMat_ne_zero (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) {y : WOF F E nS nT}
    (hy : y ≠ 0) : pairMat σ JS JT y ≠ 0 := by
  intro h0
  apply hy
  have huS : IsUnit JS.det := isUnit_iff_ne_zero.mpr hS.2
  have huT : IsUnit JT.det := isUnit_iff_ne_zero.mpr hT.2
  have hL : JS.map (incAF F E) * (JS⁻¹).map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ huS, Matrix.map_one _ (map_zero _) (map_one _)]
  have hR : JT.map (incAF F E) * (JT⁻¹).map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ huT, Matrix.map_one _ (map_zero _) (map_one _)]
  have hY : (y.map (cAF σ))ᵀ = 0 := by
    calc (y.map (cAF σ))ᵀ = JS.map (incAF F E) * pairMat σ JS JT y * (JT⁻¹).map (incAF F E) := by
          rw [pairMat, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.mul_assoc, hR,
            Matrix.mul_one]
      _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]
  ext i j
  have := congrFun (congrFun hY j) i
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.zero_apply] at this
  rw [Matrix.zero_apply, ← GlobalTheory.HeisLineF.cAF_cAF σ hσ (y i j), this, map_zero]

theorem exists_detect (hσ : ∀ x, σ (σ x) = x) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (hS : IsHermND σ JS)
    (hT : IsHermND σ JT) {ξ₀ : E} (hξ0 : ξ₀ ≠ 0) (hξ : σ ξ₀ = -ξ₀) {e : AEF F E} (he : IsSplitIdemF σ e)
    {y : WOF F E nS nT} (hyY : ∀ i j, cAF σ e * y i j = y i j) (hy : y ≠ 0) :
    ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧
      ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) ≠ 1 := by
  have hM := pairMat_ne_zero hσ hS hT hy
  obtain ⟨a₀, d₀, had⟩ : ∃ a d, pairMat σ JS JT y a d ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hM (Matrix.ext hc)
  have hcc : cAF σ (cAF σ e) = e := GlobalTheory.HeisLineF.cAF_cAF σ hσ e
  have hMe : pairMat σ JS JT y a₀ d₀ * e = pairMat σ JS JT y a₀ d₀ := by
    rw [pairMat_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e1 : cAF σ (y c b) = e * cAF σ (y c b) := by
      conv_lhs => rw [← hyY c b]
      rw [map_mul, hcc]
    linear_combination (-(incAF F E (JS⁻¹ a₀ b) * incAF F E (JT c d₀))) * e1
  have hunit : incAF F E ξ₀⁻¹ * incAF F E ξ₀ = 1 := by rw [← map_mul, inv_mul_cancel₀ hξ0, map_one]
  have hm0 : incAF F E ξ₀ * pairMat σ JS JT y a₀ d₀ ≠ 0 := by
    intro h0
    apply had
    calc pairMat σ JS JT y a₀ d₀ = incAF F E ξ₀⁻¹ * (incAF F E ξ₀ * pairMat σ JS JT y a₀ d₀) := by
          rw [← mul_assoc, hunit, one_mul]
      _ = 0 := by rw [h0, mul_zero]
  obtain ⟨z, hz⟩ := GlobalTheory.AdelicTraceNondeg.trace_pairing_nondeg F E ψ hψ _ hm0
  refine ⟨Matrix.single d₀ a₀ (e * z), fun i j => ?_, ?_⟩
  · by_cases hij : d₀ = i ∧ a₀ = j
    · obtain ⟨rfl, rfl⟩ := hij
      rw [Matrix.single_apply_same, ← mul_assoc, he.1]
    · rw [Matrix.single_apply_of_ne _ _ _ _ _ hij, mul_zero]
  · rw [GlobalTheory.FinLatF.symplOHF_skew σ JS JT hσ hS hT ξ₀ hξ y, sub_neg_eq_add, GlobalTheory.FinLatF.symplOHF_add_self, symplOF,
      hOF_single, ← mul_assoc (pairMat σ JS JT y a₀ d₀) e z, hMe, ← mul_assoc]
    exact hz

theorem detect_conj_half : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ e, IsSplitIdemF σ e →
      ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) → y ≠ 0 →
        ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧
          ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) ≠ 1 := by
  intro F E _ _ _ _ _ σ hσ ψ hψ nS nT JS JT hS hT ξ₀ hξ0 hξ e he y hyY hy
  exact exists_detect hσ hψ hS hT hξ0 hξ he hyY hy

theorem sigma_sigma_of_cm (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

end GlobalTheory.SplitPairNondegF

end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.PlaceCoordsF

variable {F : Type} [Field F] [NumberField F]

def placeAt (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : AF F := pairA F 0 (GlobalTheory.AdelicU.singleFin v x)

theorem placeAt_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    placeAt v (x + y) = placeAt v x + placeAt v y := by
  unfold placeAt pairA
  rw [map_add]
  exact Prod.ext (add_zero 0).symm rfl

theorem placeAt_injective (v : HeightOneSpectrum (𝓞 F)) : Function.Injective (placeAt v) := by
  intro x y h
  have h2 := congrArg (fun c : AF F => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c.2) h
  simpa only [placeAt, pairA, GlobalTheory.AdelicU.evalV_singleFin_self] using h2

theorem continuous_placeAt (v : HeightOneSpectrum (𝓞 F)) : Continuous (placeAt v) := by
  unfold placeAt pairA
  exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

theorem eq_placeAt_of_mul {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (hα1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α = 1)
    (hα0 : ∀ v', v' ≠ v → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v' α = 0) {c : AF F} (hc : pairA F 0 α * c = c) :
    c = placeAt v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c.2) := by
  have h1 : c.1 = 0 := by
    have := congrArg Prod.fst hc
    rw [← this]
    exact zero_mul _
  have h2 : α * c.2 = c.2 := congrArg Prod.snd hc
  refine Prod.ext h1 ?_
  show c.2 = GlobalTheory.AdelicU.singleFin v _
  refine GlobalTheory.AdelicU.af_ext fun u => ?_
  by_cases hu : u = v
  · subst hu
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hu, ← h2, map_mul, hα0 u hu, zero_mul]

end GlobalTheory.PlaceCoordsF

namespace GlobalTheory.PlaceCoordsF

theorem coords_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlaceIdemF F v ε → ∀ nS nT : ℕ,
      ∃ (N : ℕ) (Φ : (Fin N → v.adicCompletion F) →+ WOF F E nS nT), Continuous Φ ∧ Function.Injective Φ ∧
        ∀ y : WOF F E nS nT, (∀ i j, algebraMap (AF F) (AEF F E) ε * y i j = y i j) → y ∈ Set.range Φ := by
  intro F E _ _ _ _ _ v ε hε nS nT
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AEF F E) :=
    Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  let e := Fintype.equivFin (Fin nT × Fin nS × Fin (Module.finrank F E))
  let f : (Fin (Fintype.card (Fin nT × Fin nS × Fin (Module.finrank F E))) → v.adicCompletion F) → WOF F E nS nT :=
    fun t i j => B.equivFun.symm (fun l => placeAt v (t (e (i, j, l))))
  have hadd : ∀ s t, f (s + t) = f s + f t := by
    intro s t
    funext i j
    show B.equivFun.symm _ = B.equivFun.symm _ + B.equivFun.symm _
    rw [← map_add]
    congr 1
    funext l
    exact placeAt_add v _ _
  let Φ := AddMonoidHom.mk' f hadd
  refine ⟨_, Φ, ?_, ?_, ?_⟩
  · have hB : Continuous B.equivFun.symm := IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap
    exact continuous_pi fun i => continuous_pi fun j =>
      hB.comp (continuous_pi fun l => (continuous_placeAt v).comp (continuous_apply _))
  · intro s t hst
    have key : ∀ i j l, s (e (i, j, l)) = t (e (i, j, l)) := by
      intro i j l
      have h1 : f s i j = f t i j := congrFun (congrFun hst i) j
      have h2 := congrFun (B.equivFun.symm.injective h1) l
      exact placeAt_injective v h2
    funext k
    have := key (e.symm k).1 (e.symm k).2.1 (e.symm k).2.2
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using this
  · intro y hy
    have hc : ∀ i j l, B.equivFun (y i j) l =
        placeAt v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (B.equivFun (y i j) l).2) := by
      intro i j l
      refine eq_placeAt_of_mul hα1 hα0 ?_
      have h1 : pairA F 0 α • y i j = y i j := by rw [Algebra.smul_def]; exact hy i j
      have h2 := congrFun (congrArg B.equivFun h1) l
      rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
      exact h2
    refine ⟨fun k => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (B.equivFun (y (e.symm k).1 (e.symm k).2.1) (e.symm k).2.2).2, ?_⟩
    funext i j
    show B.equivFun.symm _ = y i j
    simp only [Equiv.symm_apply_apply]
    rw [← B.equivFun.symm_apply_apply (y i j)]
    congr 1
    funext l
    rw [B.equivFun.symm_apply_apply]
    exact (hc i j l).symm

end GlobalTheory.PlaceCoordsF
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

namespace GlobalTheory.NonarchShell

theorem exists_compact_shell_nsmul : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (V : Set (Fin N → v.adicCompletion F)), V ∈ nhds 0 →
      ∃ K : Set (Fin N → v.adicCompletion F), IsCompact K ∧ (0 : Fin N → v.adicCompletion F) ∉ K ∧
        ∀ t, t ∉ V → ∃ n : ℕ, n • t ∈ K := by
  intro F _ _ v N V hV
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  set q : ℕ := Ideal.absNorm v.asIdeal with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hq1 : ‖(q : v.adicCompletion F)‖ < 1 := by
    have := (NumberField.FinitePlace.norm_lt_one_iff_mem F v ((q : 𝓞 F))).2 (Ideal.absNorm_mem _)
    rwa [map_natCast, map_natCast] at this
  have hqne : (q : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F)) q]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hq0)
  have hqpos : 0 < ‖(q : v.adicCompletion F)‖ := norm_pos_iff.2 hqne
  have hsm : ∀ (m : ℕ) (t : Fin N → v.adicCompletion F), ‖m • t‖ = ‖(m : v.adicCompletion F)‖ * ‖t‖ := by
    intro m t
    rw [← Nat.cast_smul_eq_nsmul (v.adicCompletion F), norm_smul]
  refine ⟨{t | r * ‖(q : v.adicCompletion F)‖ ≤ ‖t‖ ∧ ‖t‖ ≤ r}, ?_, ?_, ?_⟩
  · refine (isCompact_closedBall (0 : Fin N → v.adicCompletion F) r).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro t ht
      simpa [mem_closedBall_zero_iff] using ht.2
  · intro h
    have h1 := h.1
    rw [norm_zero] at h1
    exact absurd h1 (not_le.2 (mul_pos hr hqpos))
  · intro t ht
    have htr : r ≤ ‖t‖ := by
      by_contra hlt
      exact ht (hrV (mem_ball_zero_iff.2 (not_le.1 hlt)))
    have htpos : 0 < ‖t‖ := lt_of_lt_of_le hr htr
    have hex : ∃ k : ℕ, ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hr htpos) hq1
      exact ⟨k, (lt_div_iff₀ htpos).1 hk⟩
    classical
    set k := Nat.find hex with hkdef
    have hk : ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul] at hk
      exact absurd htr (not_le.2 hk)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hjmin : ¬ ‖(q : v.adicCompletion F)‖ ^ j * ‖t‖ < r :=
      Nat.find_min hex (by omega)
    have hnorm : ‖(q ^ k) • t‖ = ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ := by
      rw [hsm, Nat.cast_pow, norm_pow]
    refine ⟨q ^ k, ?_, ?_⟩
    · show r * ‖(q : v.adicCompletion F)‖ ≤ ‖(q ^ k) • t‖
      rw [hnorm, hj, pow_succ]
      have := not_lt.1 hjmin
      nlinarith
    · show ‖(q ^ k) • t‖ ≤ r
      rw [hnorm]; exact hk.le

end GlobalTheory.NonarchShell
end

section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitAnnF

theorem exists_finset_ann_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) →
        ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, ∀ i j, e * g i j = g i j) ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            (∀ g ∈ G, B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) = 1) → y ∈ U := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he U hU
  classical
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AEF F E) := eh.isEmbedding.t2Space
  have hψ : Continuous B.ψ := hB.std.1
  obtain ⟨he1, he2, v, ε, hpl, hsum⟩ := id he
  obtain ⟨N, Φ, hΦc, hΦi, hΦr⟩ := GlobalTheory.PlaceCoordsF.coords_at_place F E v ε hpl nS nT
  have hV : (Φ ⁻¹' (U : Set (WOF F E nS nT))) ∈ nhds (0 : Fin N → v.adicCompletion F) :=
    (hU.preimage hΦc).mem_nhds (by rw [Set.mem_preimage, map_zero]; exact U.zero_mem)
  obtain ⟨K, hK, hK0, hKn⟩ := GlobalTheory.NonarchShell.exists_compact_shell_nsmul F v N _ hV
  let Y : Set (WOF F E nS nT) := {y | ∀ i j, cAF σ e * y i j = y i j}
  have hYc : IsClosed Y := by
    simp only [Y, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
        ((continuous_apply j).comp (continuous_apply i))
  have hcc : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he1]
  have hYε : ∀ y ∈ Y, ∀ i j, algebraMap (AF F) (AEF F E) ε * y i j = y i j := by
    intro y hy i j
    rw [← hsum, ← hy i j]
    linear_combination (y i j) * he2 + (y i j) * hcc
  have hYn : ∀ y ∈ Y, ∀ n : ℕ, n • y ∈ Y := by
    intro y hy n i j
    show cAF σ e * (n • y i j) = n • y i j
    rw [mul_smul_comm, hy i j]
  let χ : WOF F E nS nT → WOF F E nS nT → ℂ := fun g y =>
    B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g)
  have hχc : ∀ g, Continuous (χ g) := fun g =>
    hψ.comp ((GlobalTheory.HeisThetaF.continuous_symplOHF_right g).sub (GlobalTheory.HeisThetaF.continuous_symplOHF_left g))
  have hχn : ∀ g y (n : ℕ), χ g (n • y) = χ g y ^ n := by
    intro g y n
    induction n with
    | zero =>
      simp only [χ, zero_smul, GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero,
        AddChar.map_zero_eq_one, pow_zero]
    | succ n ih =>
      rw [succ_nsmul, pow_succ, ← ih]
      simp only [χ]
      rw [GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right, ← AddChar.map_add_eq_mul]
      congr 1
      ring
  let S : Set (WOF F E nS nT) := Φ '' K ∩ Y
  have hSc : IsCompact S := (hK.image hΦc).inter_right hYc
  have hSdet : ∀ s ∈ S, ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧ χ g s ≠ 1 := by
    rintro s ⟨⟨k, hk, rfl⟩, hsY⟩
    refine GlobalTheory.SplitPairNondegF.detect_conj_half F E σ (GlobalTheory.SplitPairNondegF.sigma_sigma_of_cm hB.cm) B.ψ hB.std nS nT JS JT hS hT ξ₀ hξ hσξ e he _ hsY ?_
    intro h0
    apply hK0
    rw [← map_zero Φ] at h0
    rwa [hΦi h0] at hk
  choose! gs hgsX hgsχ using hSdet
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun s : S => {y | χ (gs s.1) y ≠ 1})
    (fun s => isOpen_ne_fun (hχc _) continuous_const) (fun s hs => Set.mem_iUnion.2 ⟨⟨s, hs⟩, hgsχ s hs⟩)
  refine ⟨t.image (fun s : S => gs s.1), ?_, ?_⟩
  · intro g hg
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hg
    exact hgsX s.1 s.2
  · intro y hy hG
    by_contra hyU
    obtain ⟨t0, rfl⟩ := hΦr _ (hYε _ hy)
    obtain ⟨n, hn⟩ := hKn t0 hyU
    have hmem : Φ (n • t0) ∈ S := ⟨⟨_, hn, rfl⟩, by rw [map_nsmul]; exact hYn _ hy n⟩
    obtain ⟨s, hs, hsy⟩ := Set.mem_iUnion₂.1 (ht hmem)
    apply hsy
    show χ (gs s.1) (Φ (n • t0)) = 1
    rw [map_nsmul, hχn]
    have := hG (gs s.1) (Finset.mem_image_of_mem (fun s : S => gs s.1) hs)
    simp only [χ] at this ⊢
    rw [this, one_pow]

end GlobalTheory.SplitAnnF

end
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

theorem _root_.GlobalTheory.T.exists_finset_pairing_trivial_imp_mem_open_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) →
        ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, ∀ i j, e * g i j = g i j) ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            (∀ g ∈ G, B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) = 1) → y ∈ U := by
  atlas_forward_decl GlobalTheory.SplitAnnF.exists_finset_ann_le
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitVacF

theorem exists_eigen_of_sep {Y V : Type} [AddCommGroup Y] [AddCommGroup V] [Module ℂ V]
    (ρ : Y → V →ₗ[ℂ] V) (hρ : ∀ a b w, ρ (a + b) w = ρ a (ρ b w))
    (Q : AddSubgroup Y) [Finite (Y ⧸ Q)] (v : V) (hv : v ≠ 0) (hQ : ∀ q ∈ Q, ρ q v = v)
    (X : Set (Y → ℂ)) (hmul : ∀ χ ∈ X, ∀ a b, χ (a + b) = χ a * χ b) (hQχ : ∀ χ ∈ X, ∀ q ∈ Q, χ q = 1)
    (hclos : ∀ χ ∈ X, ∀ χ' ∈ X, χ * χ' ∈ X) (hone : (1 : Y → ℂ) ∈ X)
    (hsep : ∀ y, y ∉ Q → ∃ χ ∈ X, χ y ≠ 1) :
    ∃ χ ∈ X, ∃ w ∈ Submodule.span ℂ (Set.range fun y => ρ y v), w ≠ 0 ∧ ∀ y, χ y • ρ y w = w := by
  classical
  haveI : Fintype (Y ⧸ Q) := Fintype.ofFinite _
  let wf : (Y → ℂ) → V := fun χ => ∑ a : Y ⧸ Q, χ (Quotient.out a) • ρ (Quotient.out a) v
  have hout : ∀ a : Y ⧸ Q, ((Quotient.out a : Y) : Y ⧸ Q) = a := fun a => QuotientAddGroup.out_eq' a

  have heig : ∀ χ ∈ X, ∀ y, χ y • ρ y (wf χ) = wf χ := by
    intro χ hχ y
    have h0 : χ 0 = 1 := hQχ χ hχ 0 Q.zero_mem
    have hterm : ∀ a : Y ⧸ Q, χ (Quotient.out a) • ρ y (ρ (Quotient.out a) v) =
        χ (-y) • (χ (Quotient.out ((y : Y ⧸ Q) + a)) • ρ (Quotient.out ((y : Y ⧸ Q) + a)) v) := by
      intro a
      set b := (y : Y ⧸ Q) + a
      have hq : -(Quotient.out b) + (y + Quotient.out a) ∈ Q := by
        rw [← QuotientAddGroup.eq, hout, QuotientAddGroup.mk_add, hout]
      set q := -(Quotient.out b) + (y + Quotient.out a) with hqdef
      have e1 : y + Quotient.out a = Quotient.out b + q := by rw [hqdef]; abel
      have e2 : Quotient.out a = -y + (Quotient.out b + q) := by rw [← e1]; abel
      rw [← hρ, e1, hρ, hQ q hq, smul_smul, e2, hmul χ hχ, hmul χ hχ, hQχ χ hχ q hq, mul_one]
    calc χ y • ρ y (wf χ) = χ y • ∑ a : Y ⧸ Q, χ (Quotient.out a) • ρ y (ρ (Quotient.out a) v) := by
          simp only [wf, map_sum, map_smul]
      _ = χ y • ∑ a : Y ⧸ Q, χ (-y) • (χ (Quotient.out ((y : Y ⧸ Q) + a)) • ρ (Quotient.out ((y : Y ⧸ Q) + a)) v) := by
          simp only [hterm]
      _ = (χ y * χ (-y)) • ∑ a : Y ⧸ Q, χ (Quotient.out ((y : Y ⧸ Q) + a)) • ρ (Quotient.out ((y : Y ⧸ Q) + a)) v := by
          rw [← Finset.smul_sum, smul_smul]
      _ = wf χ := by
          rw [← hmul χ hχ, add_neg_cancel, h0, one_smul]
          exact Fintype.sum_equiv (Equiv.addLeft (y : Y ⧸ Q)) _ _ (fun _ => rfl)

  have hne : ∃ χ ∈ X, wf χ ≠ 0 := by
    by_contra hc
    push_neg at hc
    let Φ : (Y → ℂ) →ₗ[ℂ] V := ∑ a : Y ⧸ Q, (LinearMap.proj (Quotient.out a) : (Y → ℂ) →ₗ[ℂ] ℂ).smulRight (ρ (Quotient.out a) v)
    have hΦ : ∀ h, Φ h = wf h := fun h => by simp [Φ, wf]
    let M := Submodule.span ℂ X
    have hker : M ≤ LinearMap.ker Φ := Submodule.span_le.2 fun χ hχ => by
      show Φ χ = 0
      rw [hΦ]; exact hc χ hχ
    have hMM : ∀ f ∈ M, ∀ g ∈ M, f * g ∈ M := by
      intro f hf g hg
      have h1 : f * g ∈ M * M := Submodule.mul_mem_mul hf hg
      rw [Submodule.span_mul_span] at h1
      refine Submodule.span_mono ?_ h1
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hclos a ha b hb
    have hsep' : ∀ a : Y ⧸ Q, a ≠ 0 → ∃ χ ∈ X, χ (Quotient.out a) ≠ 1 := by
      intro a ha
      refine hsep _ fun hm => ha ?_
      rw [← hout a]
      exact (QuotientAddGroup.eq_zero_iff _).2 hm
    choose! χa hχa hχne using hsep'
    let fac : Y ⧸ Q → (Y → ℂ) := fun a =>
      (1 - χa a (Quotient.out a))⁻¹ • (χa a - χa a (Quotient.out a) • (1 : Y → ℂ))
    let p : Y → ℂ := ∏ a ∈ Finset.univ.filter (fun a : Y ⧸ Q => a ≠ 0), fac a
    have hpM : p ∈ M := by
      refine Finset.prod_induction _ (· ∈ M) (fun f g hf hg => hMM f hf g hg) (Submodule.subset_span hone) ?_
      intro a ha
      have ha' := (Finset.mem_filter.1 ha).2
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span (hχa a ha'))
        (Submodule.smul_mem _ _ (Submodule.subset_span hone)))
    have hp0 : ∀ a : Y ⧸ Q, a ≠ 0 → p (Quotient.out a) = 0 := by
      intro a ha
      simp only [p, Finset.prod_apply]
      refine Finset.prod_eq_zero (i := a) (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩) ?_
      simp [fac]
    have hp1 : p (Quotient.out (0 : Y ⧸ Q)) = 1 := by
      have hq0 : Quotient.out (0 : Y ⧸ Q) ∈ Q := (QuotientAddGroup.eq_zero_iff _).1 (hout 0)
      simp only [p, Finset.prod_apply]
      refine Finset.prod_eq_one fun a ha => ?_
      have ha' := (Finset.mem_filter.1 ha).2
      have h1 : 1 - χa a (Quotient.out a) ≠ 0 := sub_ne_zero.2 (Ne.symm (hχne a ha'))
      simp only [fac, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one, hQχ _ (hχa a ha') _ hq0]
      exact inv_mul_cancel₀ h1
    have hΦp : Φ p = v := by
      rw [hΦ]
      simp only [wf]
      rw [Finset.sum_eq_single (0 : Y ⧸ Q) (fun a _ ha => by rw [hp0 a ha, zero_smul]) (fun h => absurd (Finset.mem_univ _) h),
        hp1, one_smul]
      exact hQ _ ((QuotientAddGroup.eq_zero_iff _).1 (hout 0))
    exact hv (by rw [← hΦp]; exact hker hpM)
  obtain ⟨χ, hχ, hw⟩ := hne
  refine ⟨χ, hχ, wf χ, Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩), hw,
    heig χ hχ⟩

end GlobalTheory.SplitVacF

end

noncomputable section

namespace GlobalTheory.SplitVacF

open GlobalTheory.SplitInvFormF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}

theorem isSplitIdemF_conj {e : AEF F E} (he : IsSplitIdemF σ e) : IsSplitIdemF σ (cAF σ e) := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hpl, ?_⟩
  · rw [cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, mul_comm, h2]
  · rw [cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, add_comm, hsum]

theorem mem_conjHalf_conj {e : AEF F E} (he : IsSplitIdemF σ e) {x : WOF F E nS nT} (hx : ∀ i j, e * x i j = x i j) :
    x ∈ conjHalf σ (cAF σ e) nS nT := fun i j => by rw [cAF_cAF he]; exact hx i j

theorem fin_of_mem {e : AEF F E} (he : IsSplitIdemF σ e) {u : WOF F E nS nT} (hu : u ∈ conjHalf σ e nS nT) :
    u.map (infPartF F E) = 0 := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  have hs := congrArg (infPartF F E) hsum
  rw [map_add, GlobalTheory.WeilPartsF.infPartF_placeIdem hpl] at hs
  have hc : infPartF F E (cAF σ e) = 0 := by
    have a1 : infPartF F E (cAF σ e) * infPartF F E (cAF σ e) = infPartF F E (cAF σ e) := by
      rw [← map_mul, ← map_mul, h1]
    have a2 : infPartF F E (cAF σ e) * infPartF F E e = 0 := by rw [← map_mul, mul_comm, h2, map_zero]
    linear_combination -a1 - a2 + infPartF F E (cAF σ e) * hs
  ext i j
  show infPartF F E (u i j) = 0
  rw [← hu i j, map_mul, hc, zero_mul]

theorem commF_add_left (u u' y : WOF F E nS nT) :
    commF σ JS JT xi0 ψ (u + u') y = commF σ JS JT xi0 ψ u y * commF σ JS JT xi0 ψ u' y := by
  unfold commF
  rw [← AddChar.map_add_eq_mul, GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right]
  congr 1; ring

theorem commF_add_right (u y y' : WOF F E nS nT) :
    commF σ JS JT xi0 ψ u (y + y') = commF σ JS JT xi0 ψ u y * commF σ JS JT xi0 ψ u y' := by
  unfold commF
  rw [← AddChar.map_add_eq_mul, GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right]
  congr 1; ring

theorem commF_zero_left (y : WOF F E nS nT) : commF σ JS JT xi0 ψ 0 y = 1 := by
  unfold commF
  rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one]

theorem commF_zero_right (u : WOF F E nS nT) : commF σ JS JT xi0 ψ u 0 = 1 := by
  unfold commF
  rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one]

theorem commF_neg_right (u y : WOF F E nS nT) : commF σ JS JT xi0 ψ u (-y) * commF σ JS JT xi0 ψ u y = 1 := by
  rw [← commF_add_right, neg_add_cancel, commF_zero_right]

theorem commF_swap (u y : WOF F E nS nT) : commF σ JS JT xi0 ψ y (-u) = commF σ JS JT xi0 ψ u y := by
  unfold commF
  have h1 := GlobalTheory.HeisThetaF.symplOHF_add_right (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) y (-u) u
  have h2 := GlobalTheory.HeisThetaF.symplOHF_add_left (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) (-u) u y
  rw [neg_add_cancel, GlobalTheory.HeisThetaF.symplOHF_zero_right] at h1
  rw [neg_add_cancel, GlobalTheory.HeisThetaF.symplOHF_zero_left] at h2
  congr 1
  linear_combination -h1 + h2

theorem commF_nsmul_left (u y : WOF F E nS nT) (n : ℕ) :
    commF σ JS JT xi0 ψ (n • u) y = commF σ JS JT xi0 ψ u y ^ n := by
  induction n with
  | zero => rw [zero_smul, commF_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, commF_add_left, ih, pow_succ]

theorem commF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : commF σ JS JT xi0 ψ x y = 1 := by
  unfold commF
  rw [symplOHF_half he hx hy, symplOHF_half he hy hx, sub_zero, AddChar.map_zero_eq_one]

theorem heisOF_add_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ (x + y) f = heisOF σ JS JT xi0 ψ x (heisOF σ JS JT xi0 ψ y f) := by
  rw [heisOF_heisOF, symplOHF_half he hx hy, AddChar.map_zero_eq_one, one_smul]

theorem heisOF_nsmul_fix {e : AEF F E} (he : IsSplitIdemF σ e) {x : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    {f : WOF F E nS nT → ℂ} (hf : heisOF σ JS JT xi0 ψ x f = f) (n : ℕ) : heisOF σ JS JT xi0 ψ (n • x) f = f := by
  induction n with
  | zero => rw [zero_smul, heisOF_zero]
  | succ n ih => rw [succ_nsmul, heisOF_add_half he (nsmul_mem hx n) hx, hf, ih]

end GlobalTheory.SplitVacF

end

noncomputable section

namespace GlobalTheory.SplitVacF

open GlobalTheory.SplitInvFormF

theorem exists_vac_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ φ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ φ ∧ φ ≠ 0 ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            heisOF σ JS JT ξ₀ B.ψ y φ = φ ∨
            ∃ u : WOF F E nS nT, heisOF σ JS JT ξ₀ B.ψ u φ = φ ∧
              B.ψ (symplOHF σ JS JT ξ₀ u y - symplOHF σ JS JT ξ₀ y u) ≠ 1 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  classical
  have he' := isSplitIdemF_conj he
  let Y := conjHalf σ e nS nT
  let X := conjHalf σ (cAF σ e) nS nT
  obtain ⟨U, hU, hUf⟩ := hf₀.level
  obtain ⟨G, hGX, hGU⟩ := GlobalTheory.T.exists_finset_pairing_trivial_imp_mem_open_subgroup F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he U hU
  have hGX' : ∀ g ∈ G, g ∈ X := fun g hg => mem_conjHalf_conj he (hGX g hg)

  let YK : AddSubgroup (WOF F E nS nT) :=
    { carrier := {y | y ∈ Y ∧ ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → commF σ JS JT ξ₀ B.ψ k y = 1}
      add_mem' := fun {a b} ha hb => ⟨Y.add_mem ha.1 hb.1, fun k hk hkf => by
        rw [commF_add_right, ha.2 k hk hkf, hb.2 k hk hkf, one_mul]⟩
      zero_mem' := ⟨Y.zero_mem, fun k _ _ => commF_zero_right k⟩
      neg_mem' := fun {a} ha => ⟨Y.neg_mem ha.1, fun k hk hkf => by
        have := commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) k a
        rwa [ha.2 k hk hkf, mul_one] at this⟩ }
  let Q : AddSubgroup YK :=
    { carrier := {y | ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1}
      add_mem' := fun {a b} ha hb g hg => by
        rw [AddSubgroup.coe_add, commF_add_right, ha g hg, hb g hg, one_mul]
      zero_mem' := fun g _ => commF_zero_right g
      neg_mem' := fun {a} ha g hg => by
        have := commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) g (a : WOF F E nS nT)
        rwa [ha g hg, mul_one] at this }
  have hQfix : ∀ q ∈ Q, heisOF σ JS JT ξ₀ B.ψ (q : WOF F E nS nT) f₀ = f₀ := fun q hq =>
    hUf _ (hGU _ q.2.1 hq) (fin_of_mem he q.2.1)

  have hN : ∀ g ∈ G, ∃ k : ℕ, 0 < k ∧ heisOF σ JS JT ξ₀ B.ψ (k • g) f₀ = f₀ := fun g hg => exists_nsmul_fix he' (hGX' g hg) hf₀
  choose! Ng hNg0 hNg using hN
  set N := ∏ g ∈ G, Ng g with hNdef
  have hN0 : 0 < N := Finset.prod_pos fun g hg => hNg0 g hg
  have hpowN : ∀ g ∈ G, ∀ y : YK, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) ^ N = 1 := by
    intro g hg y
    obtain ⟨m, hm⟩ : Ng g ∣ N := Finset.dvd_prod_of_mem _ hg
    rw [← commF_nsmul_left]
    refine y.2.2 _ (nsmul_mem (hGX' g hg) N) ?_
    rw [hm, mul_nsmul]
    exact heisOF_nsmul_fix he' (nsmul_mem (hGX' g hg) _) (hNg g hg) m

  haveI : Finite (YK ⧸ Q) := by
    let S := (Polynomial.nthRoots N (1 : ℂ)).toFinset
    refine Finite.of_injective (β := G → S) (fun a g => ⟨commF σ JS JT ξ₀ B.ψ g (Quotient.out a : YK), ?_⟩) ?_
    · rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hN0]
      exact hpowN g g.2 _
    · intro a b hab
      rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq]
      intro g hg
      have h1 := congrArg Subtype.val (congrFun hab ⟨g, hg⟩)
      simp only at h1
      show commF σ JS JT ξ₀ B.ψ g ((-Quotient.out a + Quotient.out b : YK) : WOF F E nS nT) = 1
      rw [AddSubgroup.coe_add, commF_add_right, ← h1, AddSubgroup.coe_neg, commF_neg_right]

  let Ch : Set (YK → ℂ) := {χ | ∃ x ∈ X, (∀ q ∈ Q, commF σ JS JT ξ₀ B.ψ x (q : WOF F E nS nT) = 1) ∧ χ = fun y : YK => commF σ JS JT ξ₀ B.ψ x (y : WOF F E nS nT)}
  obtain ⟨χ, ⟨x, hxX, -, rfl⟩, w, hwspan, hw0, hweig⟩ := exists_eigen_of_sep
    (fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT))
    (fun a b f => heisOF_add_half he a.2.1 b.2.1 f) Q f₀ hf₀0 hQfix Ch
    (by rintro _ ⟨x, -, -, rfl⟩ a b; exact commF_add_right x a b)
    (by rintro _ ⟨x, -, hx, rfl⟩ q hq; exact hx q hq)
    (by
      rintro _ ⟨x, hx, hxQ, rfl⟩ _ ⟨x', hx', hxQ', rfl⟩
      refine ⟨x + x', X.add_mem hx hx', fun q hq => by rw [commF_add_left, hxQ q hq, hxQ' q hq, one_mul], ?_⟩
      funext y
      simp only [Pi.mul_apply, commF_add_left])
    ⟨0, X.zero_mem, fun q _ => commF_zero_left _, by funext y; simp only [Pi.one_apply, commF_zero_left]⟩
    (fun y hy => by
      have hy' : ¬ ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1 := hy
      push_neg at hy'
      obtain ⟨g, hg, hne⟩ := hy'
      exact ⟨_, ⟨g, hGX' g hg, fun q hq => hq g hg, rfl⟩, hne⟩)

  have hspan_theta : Submodule.span ℂ (Set.range fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) ≤
      GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ := Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    exact GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS nT JS JT ξ₀ _ _ hf₀)
  have hspan_fix : ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → Submodule.span ℂ (Set.range fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) ≤
      LinearMap.eqLocus (heisL σ JS JT ξ₀ B.ψ k) LinearMap.id := fun k hk hkf => Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    show heisOF σ JS JT ξ₀ B.ψ k (heisOF σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) = heisOF σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀
    rw [heisOF_comm, y.2.2 k hk hkf, one_smul, hkf])
  have hwθ : IsThetaFunOF σ JS JT ξ₀ B.ψ w := hspan_theta hwspan
  refine ⟨heisOF σ JS JT ξ₀ B.ψ (-x) w, GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS nT JS JT ξ₀ _ _ hwθ, ?_, ?_⟩
  · intro h0
    apply hw0
    have := heisOF_add_half (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) he' hxX (X.neg_mem hxX) w
    rw [add_neg_cancel, heisOF_zero] at this
    rw [this, show heisOF σ JS JT ξ₀ B.ψ (-x) w = 0 from h0]
    exact map_zero (heisL σ JS JT ξ₀ B.ψ x)
  · intro y hy
    by_cases hyK : ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → commF σ JS JT ξ₀ B.ψ k y = 1
    · left
      have hyy : y ∈ YK := ⟨hy, hyK⟩
      have h1 := hweig ⟨y, hyy⟩
      change commF σ JS JT ξ₀ B.ψ x y • heisOF σ JS JT ξ₀ B.ψ y w = w at h1
      rw [heisOF_comm, commF_swap]
      conv_rhs => rw [← h1]
      exact (GlobalTheory.WeilPartsF.heisOF_smul _ _ _).symm
    · right
      push_neg at hyK
      obtain ⟨k, hk, hkf, hne⟩ := hyK
      refine ⟨k, ?_, hne⟩
      rw [heisOF_comm, commF_half he' hk (X.neg_mem hxX), one_smul]
      congr 1
      exact hspan_fix k hk hkf hwspan

end GlobalTheory.SplitVacF

end
end
