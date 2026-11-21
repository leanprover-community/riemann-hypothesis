import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormL2Bound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTransportArchimedeanSliceSobolevBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFiniteDimensionalFinitePartsWeilTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationL2Isometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxCoordinates

section
section
noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.WeilL2Words.StdArch

theorem supportedAtArchimedean_adeleOfMixedSpaceComponent (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (GlobalTheory.WeilL2Words.arch1 F z) := by
  intro u hu
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · exact mul_zero u.2

theorem evI_arch1 (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (GlobalTheory.WeilL2Words.arch1 F z) = z :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply z

theorem isStdInf_of_isStd : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → GlobalTheory.WeilL2Words.IsStdInf F ψ := by
  intro F _ _ ψ hψ
  refine ⟨-(Algebra.trace ℝ (mixedEmbedding.mixedSpace F)), fun z hz => ?_, fun z => ?_⟩
  · by_contra h
    push_neg at h
    exact hz (GlobalTheory.ArchUniq.Coord.eq_zero_of_trace z fun b => by
      have := h b
      rw [LinearMap.neg_apply, neg_eq_zero] at this
      exact this)
  · rw [hψ.2.2 _ (supportedAtArchimedean_adeleOfMixedSpaceComponent F z), evI_arch1]
    simp only [LinearMap.neg_apply, Complex.ofReal_neg]
    ring_nf

end GlobalTheory.WeilL2Words.StdArch

end
end

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardArchimedeanAddChar_of_isStandardTraceAdelic : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → GlobalTheory.WeilL2Words.IsStdInf F ψ := by
  atlas_forward_decl GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_l2_isometry : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {G : Type} [Group G]
    (om : G →* Module.End ℂ ((κ → AF F) → ℂ)), (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) → IsUnitaryOn (adeleClass F) om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A F μ Φ := by
  first | exact @GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn | exact GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn | (intros; apply GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn <;> assumption)
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_darboux_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (m n : ℕ) (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
    (om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ p w, ∀ φ ∈ schA F κ, om p (co.rho ψ w φ) = co.rho ψ (actAB (cA σ) p w) (om p φ)) →
    ∃ M : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ p h, ∀ φ ∈ schA F κ,
        om p (schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) ∧
      ∀ h, Continuous fun p => M p h := by
  first | exact @GlobalTheory.ArchTransportDir.archDir_transport | exact GlobalTheory.ArchTransportDir.archDir_transport | (intros; apply GlobalTheory.ArchTransportDir.archDir_transport <;> assumption)
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

theorem GlobalTheory.WeilContF.slice_bounds : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ (y : κ → FiniteAdeleRing (𝓞 F) F) p0 (k n : ℕ), ∃ C : ℝ,
      ∀ᶠ p in nhds p0, ∀ x : κ → mixedEmbedding.mixedSpace F,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ ≤ C := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ _ co hco om htr Φ hΦ y p0 k n
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have hI := GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hU := GlobalTheory.T.isUnitaryOn_weilDatum_transport_adelicSchwartz F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
  obtain ⟨M, himpl, hM⟩ := GlobalTheory.T.weil_representation_darboux_coordinates F E σ B.ψ nT nS JA JB ξ κ co om hI.2
  obtain ⟨μ, hμ, hiso⟩ := GlobalTheory.T.weil_representation_l2_isometry F κ om hI.1 hU
  have hfin := GlobalTheory.T.exists_local_finiteDimensional_finite_parts_weil_transport F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr Φ hΦ p0
  obtain ⟨N, C, hC, hsob⟩ := GlobalTheory.T.schwartz_seminorm_l2_bound (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)) k n
  choose Bd hBd using fun i j => GlobalTheory.WeilL2Words.slice_l2_of (GlobalTheory.T.isStandardArchimedeanAddChar_of_isStandardTraceAdelic F B.ψ hB.std) om hI.1 M himpl hM μ hμ hiso hΦ p0 hfin y i j
  have hev : ∀ᶠ p in nhds p0, ∀ i ∈ Finset.range (N + 1), ∀ j ∈ Finset.range (N + 1),
      ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2 ≤ Bd i j :=
    (Filter.eventually_all_finset _).2 fun i _ => (Filter.eventually_all_finset _).2 fun j _ => hBd i j
  refine ⟨C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), Bd i j), ?_⟩
  filter_upwards [hev] with p hp x
  obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F (hI.1 p Φ hΦ) y
  have hfs : (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) = ⇑s := funext fun x => (hs x).symm
  rw [hfs] at hp ⊢
  refine (hsob s x).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC)
  exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hp i hi j hj
end
