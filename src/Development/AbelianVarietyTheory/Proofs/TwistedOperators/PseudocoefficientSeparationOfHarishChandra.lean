import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConsequencesOfDsClass
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IrreducibleKStableFiniteSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteOrthogonalComplement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothIntertwinerExtensionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedKFiniteRestriction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitesimalCharacterDifference
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefExtendsHolomorphically
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothCycOfKFinSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlRelationsOnKFiniteVectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveInducedModuleShift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspaceStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

open GlobalTheory.HCChar GlobalTheory.Orb GlobalTheory.FlagLeviGroup

namespace GlobalTheory.IndTraceZero

variable {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : GlobalTheory.RealInd.Flag n a}

theorem IsSplit.commute (hW : IsIsoFlag ε j W) {x : Fin a → ℝ} {t g : UJ ε} (ht : IsSplit ε W x t)
    (hg : g ∈ flagM ε W) : g * t = t * g := by
  have hgi : g⁻¹ ∈ flagM ε W := (leviSub ε W).inv_mem hg
  have hgg : uMat g * uMat g⁻¹ = 1 := by
    rw [← show uMat (g * g⁻¹) = uMat g * uMat g⁻¹ from rfl, mul_inv_cancel]; rfl
  have hJ : Jm ε * uMat g⁻¹ = (uMat g)ᴴ * Jm ε := by
    have := conjTranspose_inv_mul_Jm (ε := ε) g⁻¹
    rw [inv_inv] at this
    exact this.symm
  have hm : uMat (g * t * g⁻¹) = uMat g * uMat t * uMat g⁻¹ := rfl
  have h' : IsSplit ε W x (g * t * g⁻¹) := by
    refine ⟨(leviSub ε W).mul_mem ((leviSub ε W).mul_mem hg ht.1) hgi, fun i y hy => ?_, fun y hy => ?_⟩
    · have hy' : uMat g⁻¹ *ᵥ y ∈ W i.succ := (hgi _ y hy).1
      have h1 := (hg _ _ (ht.2.1 i _ hy')).1
      have e : uMat g *ᵥ (uMat t *ᵥ (uMat g⁻¹ *ᵥ y) - (Real.exp (x i) : ℂ) • (uMat g⁻¹ *ᵥ y)) =
          uMat (g * t * g⁻¹) *ᵥ y - (Real.exp (x i) : ℂ) • y := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          hgg, Matrix.one_mulVec, hm]
      rwa [e] at h1
    · have hy' : ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ (uMat g⁻¹ *ᵥ y)) = 0 := fun z hz => by
        rw [Matrix.mulVec_mulVec, hJ, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
        exact hy _ (hg _ z hz).1
      have h1 := (hg _ _ (ht.2.2 _ hy')).1
      have e : uMat g *ᵥ (uMat t *ᵥ (uMat g⁻¹ *ᵥ y) - uMat g⁻¹ *ᵥ y) = uMat (g * t * g⁻¹) *ᵥ y - y := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgg,
          Matrix.one_mulVec, hm]
      rwa [e] at h1
  have e := (existsUnique_isSplit hW x).unique h' ht
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [e]

theorem not_isSplit_subset_compact (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) (ha : a ≠ 0) {K : Set (UJ ε)}
    (hK : IsCompact K) (h : ∀ r : ℝ, ∃ t ∈ K, IsSplit ε W (fun _ => r) t) : False := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  let i₀ : Fin (a' + 1) := 0
  have hr : Module.finrank ℂ (W i₀.succ) = j i₀ := by
    rw [hW.2.2.1 i₀, show i₀.castSucc = 0 from rfl, hW.1, finrank_bot, zero_add]
  have hne : W i₀.succ ≠ ⊥ := fun e => by
    have := hj i₀
    rw [e, finrank_bot] at hr
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hc : Continuous fun g : UJ ε => uMat g *ᵥ y :=
    (continuous_ujMat (ε := ε)).matrix_mulVec continuous_const
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  obtain ⟨t, htK, ht⟩ := h (C / ‖y‖)
  have h1 := ht.2.1 i₀ y hy
  rw [show i₀.castSucc = 0 from rfl, hW.1, Submodule.mem_bot, sub_eq_zero] at h1
  have h2 := hC t htK
  rw [h1, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h2
  have h3 := Real.add_one_le_exp (C / ‖y‖)
  have h4 : (C / ‖y‖ + 1) * ‖y‖ ≤ C := (mul_le_mul_of_nonneg_right h3 hyn.le).trans h2
  rw [add_mul, div_mul_cancel₀ _ hyn.ne', one_mul] at h4
  linarith

theorem not_conj_mem_flagM (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) (ha : a ≠ 0) {s : UJ ε}
    (hK : IsCompact (cent s : Set (UJ ε))) (x : UJ ε) : x * s * x⁻¹ ∉ flagM ε W := by
  intro hx
  refine not_isSplit_subset_compact hW hj ha (hK.image (f := fun g => x * g * x⁻¹)
    ((continuous_const.mul continuous_id).mul continuous_const)) fun r => ?_
  obtain ⟨t, ht, -⟩ := exists_isSplit hW (fun _ => r)
  have hc := IsSplit.commute hW ht hx
  refine ⟨t, ⟨x⁻¹ * t * x, mem_cent.2 ?_, by group⟩, ht⟩
  calc x⁻¹ * t * x * s = x⁻¹ * (t * (x * s * x⁻¹)) * x := by group
    _ = x⁻¹ * ((x * s * x⁻¹) * t) * x := by rw [hc]
    _ = s * (x⁻¹ * t * x) := by group

end GlobalTheory.IndTraceZero

namespace GlobalTheory.IndTraceZero

open GlobalTheory.HCChar GlobalTheory.Published

theorem hasTrace_indModule_eq_zero : GlobalTheory.Published.HarishChandraCharacters → ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : UJ ε →* (X →L[ℂ] X)) (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ δ f → ∀ I : IndModule ε, I.a ≠ 0 → HasTrace (repOp I.rep μ f) 0 := by
  intro hHC n ε μ _ X _ _ _ δ f hf I ha
  obtain ⟨Θ, hΘ, hvan⟩ := hHC.2.2.2.indModule μ I ha
  have htr := hΘ.1.2.2 f hf.mem
  convert htr using 1
  symm
  refine hHC.2.2.1.integral_mul_eq_zero μ (continuous_of_mem_ccSmooth isInducing_matCoord.continuous hf.mem)
    hf.mem.1 hΘ.1.1 (fun s x hs => (hΘ.2 s hs).2 x) fun s hs => ?_
  by_cases hK : IsCompact (cent s : Set (UJ ε))
  · exact Or.inl (hvan s hs fun x => not_conj_mem_flagM I.flag I.pos ha hK x)
  · exact Or.inr fun ds _ _ => hf.orb_noncompact s hs hK ds

end GlobalTheory.IndTraceZero
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudocoefficient_trace_vanishes : GlobalTheory.Published.HarishChandraCharacters → ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : UJ ε →* (X →L[ℂ] X)) (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ δ f → ∀ I : IndModule ε, I.a ≠ 0 → HasTrace (repOp I.rep μ f) 0 := by
  atlas_forward_decl GlobalTheory.IndTraceZero.hasTrace_indModule_eq_zero
end

section
section
noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep IsUnitEquiv)
open scoped InnerProductSpace

namespace GlobalTheory.TraceInfChar

theorem ujMat_onto {n : ℕ} {ε : Fin n → Bool} : ∀ x ∈ UJset ε, ∃ g, ujMat ε g = x := fun x hx => by
  obtain ⟨g, hg, -⟩ := GlobalTheory.RealIwasawa.exists_uMat x hx
  exact ⟨g, hg⟩

theorem isIrredOn_of_isom {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H H' : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (U : H ≃ₗᵢ[ℂ] H') (hU : ∀ g ∈ G, ∀ v, U (ρ g v) = σ g (U v)) (h : IsIrredOn G σ) : IsIrredOn G ρ := by
  intro S hS hst
  let e := U.toLinearEquiv
  have hS' : IsClosed ((S.map (e : H →ₗ[ℂ] H') : Submodule ℂ H') : Set H') := by
    rw [Submodule.map_coe]
    exact U.toHomeomorph.isClosedMap _ hS
  rcases h _ hS' (fun g hg w hw => by
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨ρ g v, hst g hg v hv, hU g hg v⟩) with h0 | h1
  · left
    rw [eq_bot_iff]
    intro v hv
    have : e v ∈ S.map (e : H →ₗ[ℂ] H') := ⟨v, hv, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    simpa using this
  · right
    rw [eq_top_iff]
    intro v _
    have : e v ∈ S.map (e : H →ₗ[ℂ] H') := h1 ▸ Submodule.mem_top
    obtain ⟨w, hw, hwe⟩ := this
    rwa [e.injective hwe] at hw

theorem isTempered_of_unitEquiv {G V W : Type} [Group G] [MeasurableSpace G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {μ : Measure G}
    {π : G →* (V →L[ℂ] V)} {π' : G →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') (ht : GlobalTheory.Orb.IsTempered μ π) :
    GlobalTheory.Orb.IsTempered μ π' := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨v, hv, hi⟩ := ht
  refine ⟨A v, by simpa using hv, fun r hr => ?_⟩
  simpa [← hA, LinearIsometryEquiv.inner_map_map] using hi r hr

theorem hasInfChar_of_trace_ne_zero : GlobalTheory.Published.LanglandsClassification → GlobalTheory.Published.HarishChandraCharacters →
    ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
      [CompleteSpace X] (δ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (hδ : IsURepOn (UJset ε) δ),
      HasInfChar ε χ δ → ∀ (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (f : UJ ε → ℂ),
      IsPseudoCoeff (ujMat ε) μ (ujRep hδ) f → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hπ : IsIrrAdm ε π) (c : ℂ),
      HasTrace (repOp (groupRep ε hπ.2.1.1) μ f) c → c ≠ 0 → HasInfChar ε χ π := by
  intro hL hC n ε χ X _ _ _ δ hδ hχ μ _ f hf V _ _ _ π hπ c hc hc0
  obtain ⟨b, W₀, hW₀⟩ := exists_isMinimalFlag ε
  obtain ⟨N, I, m, hstd, -, -, -, hinf, htr⟩ := hL.2.2.2.2.1 n ε b W₀ hW₀ V π hπ
  obtain ⟨-, hsum⟩ := htr μ f hf.mem
  have hcs : c = ∑ i, (m i : ℂ) * trace (repOp (I i).rep μ f) := hc.2.symm.trans hsum.2
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hcs ▸ hc0)
  have htr0 : trace (repOp (I i).rep μ f) ≠ 0 := right_ne_zero_of_mul hi
  refine (hinf i χ).1 ?_
  by_cases ha : (I i).a = 0
  · obtain ⟨hM, U, hUρ⟩ := GlobalTheory.Published.Langlands.equiv_of_zero (I i) ha
    have ht := (I i).temp
    rw [show leviOne ε (I i).W = ⊤ from hM] at ht
    obtain ⟨hσn, hσi, hσU, hσt⟩ := (isIrrTempered_top_iff μ).1 ht
    haveI := hσn
    have hAdm := (hL.1 n ε (I i)).1
    haveI hρn : Nontrivial (I i).H := U.toLinearEquiv.toEquiv.nontrivial
    have hρU : IsURepOn (UJset ε) (I i).ρ := ⟨(I i).isCRepOn, fun g hg v => by
      rw [← U.norm_map, hUρ g hg v, hσU.2.1 g hg, U.norm_map], hAdm.2.1⟩
    have hρi : IsIrredOn (UJset ε) (I i).ρ := isIrredOn_of_isom U hUρ hσi
    have hσρ : IsUnitEquiv (ujRep hσU) (ujRep hρU) :=
      ⟨U.symm, fun g v => by
        have hg : ujMat ε g ∈ UJset ε := g.2
        change U.symm ((I i).σ (ujMat ε g) v) = (I i).ρ (ujMat ε g) (U.symm v)
        apply U.injective
        rw [LinearIsometryEquiv.apply_symm_apply, hUρ _ hg, LinearIsometryEquiv.apply_symm_apply]⟩
    have hρt : GlobalTheory.Orb.IsTempered μ (ujRep hρU) := isTempered_of_unitEquiv hσρ hσt
    have hrep : (I i).rep = ujRep hρU := rfl
    have hρδ : IsUnitEquiv (ujRep hρU) (ujRep hδ) := by
      by_contra hne
      have h0 := hf.trace_other (I i).H (ujRep hρU)
        (GlobalTheory.Orb.isUnitaryRep_repVia hρU (fun g => g.2) GlobalTheory.HCChar.continuous_ujMat)
        (GlobalTheory.Orb.isTopIrreducible_repVia hρU (fun g => g.2) ujMat_onto hρi) hρt hne
      exact htr0 (hrep ▸ h0.2)
    obtain ⟨A, hA⟩ := hρδ
    refine GlobalTheory.ClassificationConsequences.hasInfChar_of_uEquiv ⟨A, fun g hg v => ?_⟩ hχ
    obtain ⟨g', rfl⟩ := ujMat_onto g hg
    exact hA g' v
  · exact absurd (GlobalTheory.T.pseudocoefficient_trace_vanishes hC n ε μ X (ujRep hδ) f hf (I i) ha).2 htr0

end GlobalTheory.TraceInfChar

end
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudocoefficient_trace_infinitesimal : GlobalTheory.Published.LanglandsClassification → GlobalTheory.Published.HarishChandraCharacters → ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (hδ : IsURepOn (UJset ε) δ), HasInfChar ε χ δ → ∀ (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ (ujRep hδ) f → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hπ : IsIrrAdm ε π) (c : ℂ), HasTrace (repOp (groupRep ε hπ.2.1.1) μ f) c → c ≠ 0 → HasInfChar ε χ π := by
  atlas_forward_decl GlobalTheory.TraceInfChar.hasInfChar_of_trace_ne_zero
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_finite_orthogonal_complement : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → ∀ Z : Submodule ℂ H, Z ≤ kFinVec ε ρ → IsKStableOn ε ρ Z → Z ≠ kFinVec ε ρ → ∃ a : H, a ≠ 0 ∧ IsKFin ε ρ a ∧ ∀ z ∈ Z, ⟪a, z⟫_ℂ = 0 := by
  first | exact @GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec | exact GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec | (intros; apply GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec <;> assumption)
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.IntertwiningDense
variable {n : ℕ} {ε : Fin n → Bool}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem inG_of_exp_mem {X : Matrix (Fin n) (Fin n) ℂ} (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ UJset ε) :
    inG ε X := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ (0 : ℝ)
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * Jm ε * NormedSpace.exp (t • X)) _ 0 :=
    (h1.mul_const (Jm ε)).mul h2
  have hc : (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * Jm ε * NormedSpace.exp (t • X)) = fun _ => Jm ε := by
    funext t
    have := h t
    rw [show t • Xᴴ = (t • X)ᴴ by rw [conjTranspose_smul, star_trivial], Matrix.exp_conjTranspose]
    exact this
  rw [hc] at h3
  have := h3.unique (hasDerivAt_const (0 : ℝ) (Jm ε))
  simpa [inG] using this
end

section Finite

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def transl (f : UJ ε → V) : Submodule ℂ (UJ ε → V) :=
  Submodule.span ℂ {φ | ∃ k ∈ KG ε, φ = fun g => f (g * k)}

theorem transl_mem (f : UJ ε → V) {k : UJ ε} (hk : k ∈ KG ε) : (fun g => f (g * k)) ∈ transl f :=
  Submodule.subset_span ⟨k, hk, rfl⟩

theorem isKFinFun_of_mem {f : UJ ε → V} (U : Submodule ℂ (UJ ε → V)) [FiniteDimensional ℂ U]
    (h : ∀ k ∈ KG ε, (fun g => f (g * k)) ∈ U) : IsKFinFun f :=
  Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by rintro φ ⟨k, hk, rfl⟩; exact h k hk))

theorem isKFinFun_add {f f' : UJ ε → V} (h : IsKFinFun f) (h' : IsKFinFun f') : IsKFinFun (f + f') := by
  haveI : FiniteDimensional ℂ (transl f) := h
  haveI : FiniteDimensional ℂ (transl f') := h'
  exact isKFinFun_of_mem (transl f ⊔ transl f') fun k hk =>
    Submodule.add_mem_sup (transl_mem f hk) (transl_mem f' hk)

theorem isKFinFun_smul {f : UJ ε → V} (h : IsKFinFun f) (c : ℂ) : IsKFinFun (c • f) := by
  haveI : FiniteDimensional ℂ (transl f) := h
  exact isKFinFun_of_mem (transl f) fun k hk => (transl f).smul_mem c (transl_mem f hk)

theorem isKFinFun_transl {f : UJ ε → V} (h : IsKFinFun f) {k₀ : UJ ε} (hk₀ : k₀ ∈ KG ε) :
    IsKFinFun fun g => f (g * k₀) := by
  haveI : FiniteDimensional ℂ (transl f) := h
  exact isKFinFun_of_mem (transl f) fun k hk => by
    simpa only [mul_assoc] using transl_mem f ((KG ε).mul_mem hk hk₀)

end Finite

section Integral

variable (D : Datum ε) (ν : Measure (UJ ε))

theorem isIntegral_zero : D.IsIntegral ν 0 0 := fun x v _ => by simp

variable {D ν}

theorem IsIntegral.add {f h f' h' : UJ ε → D.V} (a : D.IsIntegral ν f h) (b : D.IsIntegral ν f' h') :
    D.IsIntegral ν (f + f') (h + h') := fun x v hv => by
  obtain ⟨i1, e1⟩ := a x v hv
  obtain ⟨i2, e2⟩ := b x v hv
  refine ⟨by simp only [Pi.add_apply, inner_add_right]; exact i1.add i2, ?_⟩
  simp only [Pi.add_apply, inner_add_right, e1, e2]
  exact (integral_add i1 i2).symm

theorem IsIntegral.smul {f h : UJ ε → D.V} (a : D.IsIntegral ν f h) (c : ℂ) :
    D.IsIntegral ν (c • f) (c • h) := fun x v hv => by
  obtain ⟨i1, e1⟩ := a x v hv
  refine ⟨by simpa only [Pi.smul_apply, inner_smul_right] using i1.const_mul c, ?_⟩
  simp only [Pi.smul_apply, inner_smul_right, e1]
  exact (integral_const_mul c _).symm

theorem IsIntegral.transl {f h : UJ ε → D.V} (a : D.IsIntegral ν f h) (k : UJ ε) :
    D.IsIntegral ν (fun g => f (g * k)) (fun g => h (g * k)) := fun x v hv => by
  simpa only [mul_assoc] using a (x * k) v hv

end Integral

def oppDatum (D : Datum ε) : Datum ε where
  a := D.a
  j := D.j
  W := opp ε D.W
  flag := isIsoFlag_opp D.flag
  pos := D.pos
  V := D.V
  σ := D.σ
  temp := by rw [leviOne_opp]; exact D.temp
  s := -D.s

theorem oppDatum_M (D : Datum ε) : (oppDatum D).M = D.M := leviOne_opp

theorem isKFinIn_one {D : Datum ε} {h : UJ ε → D.V} (hh : h ∈ D.oppFns) (hk : IsKFinFun h) :
    IsKFinIn D.M D.σ (h 1) := by
  have := (GlobalTheory.T.induced_k_finite_restriction n ε (oppDatum D) h hh hk).2.1
  rwa [oppDatum_M] at this

theorem exists_ne_zero_K {D : Datum ε} {h : UJ ε → D.V} (hh : h ∈ D.oppFns) (hk : IsKFinFun h) (h0 : h ≠ 0) :
    ∃ k ∈ KG ε, h k ≠ 0 :=
  (GlobalTheory.T.induced_k_finite_restriction n ε (oppDatum D) h hh hk).2.2 h0

theorem eq_zero_of_K {D : Datum ε} {φ : UJ ε → D.V} (hφ : φ ∈ D.fns) (h : ∀ k ∈ KG ε, φ k = 0) : φ = 0 := by
  funext g
  obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact D.flag g
  obtain ⟨u, hu, m, hm, x, t, ht, e⟩ := exists_langlands_decomp D.flag D.pos hp
  have hkK : k ∈ KG ε := by rw [← SetLike.mem_coe, KG_eq]; exact hk
  have : g = u * m * t * k := by rw [← e]; group
  rw [this, (mem_indFun_top.1 hφ).2 u hu m hm x t ht k, h k hkK, map_zero, smul_zero]
  rfl

theorem ι_injective (I : IndModule ε) : Function.Injective I.ι := by
  haveI : IsProbabilityMeasure (muK ε) := ⟨Measure.haarMeasure_self⟩
  intro a b hab
  have h0 : I.ι (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hn := I.model.norm_sq (a - b)
  rw [h0, norm_zero] at hn
  have hc : Continuous fun k : KG ε => ‖(a - b).1 k‖ ^ 2 :=
    (((mem_indFun_top.1 (a - b).2).1.comp continuous_subtype_val).norm.pow 2)
  have hK : ∀ k ∈ KG ε, (a - b).1 k = 0 := fun k hk => by
    by_contra hne
    have := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := muK ε) (x := ⟨k, hk⟩)
      (isClosed_tsupport _).isCompact (fun _ => by positivity) (by simpa using hne)
    linarith
  have := eq_zero_of_K (D := I.toDatum) (a - b).2 hK
  exact sub_eq_zero.1 (Subtype.ext this)

def valSpace (I : IndModule ε) (ν : Measure (UJ ε)) : Submodule ℂ I.V where
  carrier := {w | ∃ f ∈ I.fns, IsKFinFun f ∧ ∃ h ∈ I.oppFns, IsKFinFun h ∧ I.IsIntegral ν f h ∧ h 1 = w}
  zero_mem' := ⟨0, zero_mem _, isKFinFun_of_mem ⊥ fun _ _ => (Submodule.mem_bot ℂ).2 (funext fun _ => rfl),
    0, zero_mem _, isKFinFun_of_mem ⊥ fun _ _ => (Submodule.mem_bot ℂ).2 (funext fun _ => rfl),
    isIntegral_zero _ _, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, hfk, h, hh, hhk, hi, rfl⟩ ⟨f', hf', hfk', h', hh', hhk', hi', rfl⟩
    exact ⟨f + f', add_mem hf hf', isKFinFun_add hfk hfk', h + h', add_mem hh hh', isKFinFun_add hhk hhk',
      IsIntegral.add hi hi', rfl⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, hfk, h, hh, hhk, hi, rfl⟩
    exact ⟨c • f, Submodule.smul_mem _ c hf, isKFinFun_smul hfk c, c • h, Submodule.smul_mem _ c hh,
      isKFinFun_smul hhk c, IsIntegral.smul hi c, rfl⟩

theorem one_mem_flagN {a : ℕ} (W : Flag n a) : (1 : UJ ε) ∈ flagN ε W :=
  have h1 : uMat (1 : UJ ε) = 1 := rfl
  ⟨fun i y _ => by simp [h1], fun y _ => by simp [h1]⟩

theorem intertwining_values_dense : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.LanglandsClassification →
    ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), I.Positive → ∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν →
      ∀ v : I.V, v ≠ 0 → ∃ f ∈ I.fns, IsKFinFun f ∧ ∃ h ∈ I.oppFns, I.IsIntegral ν f h ∧ ⟪v, h 1⟫_ℂ ≠ 0 := by
  intro hHC hLC n ε I hpos ν hν v hv
  obtain ⟨hInd, hQuot, -⟩ := hLC
  obtain ⟨-, -, hgk, hiff, hder, -⟩ := hInd n ε I
  obtain ⟨hex, hrd, Z, hZ, hZgk, hZne, -, -⟩ := hQuot n ε I hpos ν hν
  have hS0 : valSpace I ν ≠ ⊥ := by
    obtain ⟨w, hw, hwZ⟩ : ∃ w ∈ kFinVec ε I.ρ, w ∉ Z := by
      by_contra hcon
      push_neg at hcon
      exact hZne (le_antisymm (fun w hw => hZgk.kFin w hw) hcon)
    obtain ⟨f, hfk, rfl⟩ := (hiff w).1 hw
    obtain ⟨h, hh, hhk, hi⟩ := hex f.1 f.2 hfk
    have hne : h ≠ 0 := by
      rintro rfl
      apply hwZ
      have : I.ι f ∈ (Z : Set I.H) := by rw [hZ]; exact ⟨f, hfk, rfl, hi⟩
      exact this
    obtain ⟨k, hk, hhk0⟩ := exists_ne_zero_K hh hhk hne
    intro hbot
    have hmem : h k ∈ valSpace I ν := ⟨fun g => f.1 (g * k), indFun_mul_right f.2 trivial,
      isKFinFun_transl hfk hk, fun g => h (g * k), indFun_mul_right hh trivial, isKFinFun_transl hhk hk,
      IsIntegral.transl hi k, by simp⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hhk0 hmem
  have hlie : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε I.W)) →
      ∀ w ∈ valSpace I ν, ∃ w' ∈ valSpace I ν,
        HasDerivAt (fun t : ℝ => I.σ (NormedSpace.exp (t • X)) w) w' 0 := by
    rintro X hX _ ⟨f, hf, hfk, h, hh, hhk, hi, rfl⟩
    have hXg : X ∈ lieSet ε := inG_of_exp_mem fun t => by
      obtain ⟨y, -, hy⟩ := hX t
      rw [← hy]
      exact y.2
    obtain ⟨f', hrf, hdf⟩ := hder ⟨f, hf⟩ hfk X hXg
    have hf'k : IsKFinFun f'.1 := by
      have h1 : IsKFin ε I.ρ (I.ι ⟨f, hf⟩) := (hiff _).2 ⟨⟨f, hf⟩, hfk, rfl⟩
      have h2 : IsKFin ε I.ρ (I.ι f') := by rw [← hdf]; exact hgk.lieStable X hXg _ h1
      obtain ⟨f'', hk'', he⟩ := (hiff _).1 h2
      rwa [ι_injective I he] at hk''
    obtain ⟨h', hh', hh'k, hi'⟩ := hex f'.1 f'.2 hf'k
    have hrh := hrd f hf hfk X hXg f'.1 h h' hrf hi hi'
    refine ⟨h' 1, ⟨f'.1, f'.2, hf'k, h', hh', hh'k, hi', rfl⟩, ?_⟩
    have e : (fun t : ℝ => h (1 * expG ε X t)) = fun t : ℝ => I.σ (NormedSpace.exp (t • X)) (h 1) := by
      funext t
      obtain ⟨y, hy, hyX⟩ := hX t
      have hyt : expG ε X t = y := by
        apply Subtype.ext
        apply Units.ext
        have := toM_expG ε X t hXg
        rw [Complex.coe_smul] at this
        exact this.trans hyX.symm
      rw [one_mul, hyt, ← hyX]
      have hy' : y ∈ leviOne ε (opp ε I.W) := by rw [leviOne_opp]; exact hy
      have := (mem_indFun_top.1 hh).2 1 (one_mem_flagN _) y hy' 0 1 isSplit_one 1
      simpa [pairing] using this
    have := hrh 1
    rwa [e] at this
  have hd := hHC.2 n ε I.a I.j I.W I.flag I.pos I.V I.σ I.temp.2.2.1 I.temp.2.1 (valSpace I ν) hS0
    (fun w ⟨f, hf, hfk, h, hh, hhk, hi, hw⟩ => hw ▸ isKFinIn_one hh hhk) hlie
  by_contra hcon
  push_neg at hcon
  have hz : ((valSpace I ν : Submodule ℂ I.V) : Set I.V) ⊆ {w | ⟪v, w⟫_ℂ = 0} :=
    fun w ⟨f, hf, hfk, h, hh, hhk, hi, hw⟩ => hw ▸ hcon f hf hfk h hh hi
  have hcl : IsClosed {w : I.V | ⟪v, w⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have : ⟪v, v⟫_ℂ = 0 := closure_minimal hz hcl (hd v)
  exact hv (inner_self_eq_zero.1 this)

end GlobalTheory.IntertwiningDense

end
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_intertwining_integral_nonzero : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), I.Positive → ∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν → ∀ v : I.V, v ≠ 0 → ∃ f ∈ I.fns, IsKFinFun f ∧ ∃ h ∈ I.oppFns, I.IsIntegral ν f h ∧ ⟪v, h 1⟫_ℂ ≠ 0 := by
  atlas_forward_decl GlobalTheory.IntertwiningDense.intertwining_values_dense
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section
open Filter Topology

namespace GlobalTheory.UnitaryBound

theorem re_le_of_chamber {n a : ℕ} (j : Fin a → ℕ) (hj : ∀ i, 1 ≤ j i) (s : Fin a → ℂ) (h : 0 < a)
    (hx : ∀ x : Fin a → ℝ, InChamber x → 0 ≤ (pairing j (rho n j - s) x).re) :
    (s ⟨0, h⟩).re ≤ (n : ℝ) - 1 := by
  set i0 : Fin a := ⟨0, h⟩ with hi0
  have hre : ∀ x : Fin a → ℝ, (pairing j (rho n j - s) x).re =
      ∑ i, (j i : ℝ) * ((rho n j i).re - (s i).re) * x i := by
    intro x; simp [pairing, Complex.re_sum, Complex.mul_re]
  have hI : Finset.Iio i0 = ∅ :=
    Finset.eq_empty_of_forall_notMem fun l hl => by simp [hi0, Fin.lt_def] at hl
  have hrho : (rho n j i0).re = n - j i0 := by simp [rho, hI]
  set A := (j i0 : ℝ) * ((rho n j i0).re - (s i0).re) with hA
  set B := ∑ i, (j i : ℝ) * ((rho n j i).re - (s i).re) * ((a : ℝ) - ((i : ℕ) : ℝ)) with hB
  have key : ∀ δ : ℝ, 0 < δ → 0 ≤ A + δ * B := by
    intro δ hδ
    have hc : InChamber (fun i : Fin a => (if i = i0 then (1 : ℝ) else 0) + δ * ((a : ℝ) - ((i : ℕ) : ℝ))) := by
      refine ⟨fun i l hil => ?_, fun i => ?_⟩
      · have hl : l ≠ i0 := fun e => by
          have : (i : ℕ) < l := hil
          rw [e] at this; simp [hi0] at this
        have hil' : ((i : ℕ) : ℝ) < ((l : ℕ) : ℝ) := by exact_mod_cast hil
        simp only [hl, if_false]
        have : (0 : ℝ) ≤ if i = i0 then 1 else 0 := by split_ifs <;> norm_num
        nlinarith
      · have : ((i : ℕ) : ℝ) < a := by exact_mod_cast i.2
        have : (0 : ℝ) ≤ if i = i0 then 1 else 0 := by split_ifs <;> norm_num
        nlinarith
    have := hx _ hc
    rw [hre] at this
    convert this using 1
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, hA, hB, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  have hA0 : 0 ≤ A := by
    have ht : Tendsto (fun δ : ℝ => A + δ * B) (𝓝[>] 0) (𝓝 (A + 0 * B)) :=
      ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0).mono_left nhdsWithin_le_nhds
    have := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)
    simpa using this
  have hj0 : (1 : ℝ) ≤ j i0 := by exact_mod_cast hj i0
  rw [hA, hrho] at hA0
  have : 0 ≤ (n : ℝ) - j i0 - (s i0).re := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  linarith

theorem re_nonneg_of_tendsto {p L : ℂ} {F : ℝ → ℂ} {B : ℝ} (hB : ∀ r, ‖F r‖ ≤ B) (hL : L ≠ 0)
    (hF : Tendsto (fun r : ℝ => Complex.exp (r * p) * F r) atTop (𝓝 L)) : 0 ≤ p.re := by
  by_contra hp
  push_neg at hp
  have h0 : Tendsto (fun r : ℝ => Complex.exp (r * p) * F r) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun r : ℝ => Real.exp (r * p.re) * B) (fun r => ?_) ?_
    · rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
      exact mul_le_mul_of_nonneg_left (hB r) (Real.exp_pos _).le
    · have : Tendsto (fun r : ℝ => r * p.re) atTop atBot := tendsto_id.atTop_mul_const_of_neg hp
      simpa using (Real.tendsto_exp_atBot.comp this).mul_const B
  exact hL (tendsto_nhds_unique hF h0)

theorem inner_ι {n : ℕ} {ε : Fin n → Bool} (I : IndModule ε) (f g : I.fns) :
    ⟪I.ι g, I.ι f⟫_ℂ = ∫ k : KG ε, ⟪g.1 k, f.1 k⟫_ℂ ∂muK ε := by
  have hcont : ∀ u : I.fns, Continuous fun k : KG ε => u.1 k := fun u =>
    (mem_indFun_top.1 u.2).1.comp continuous_subtype_val
  have int : ∀ u : I.fns, Integrable (fun k : KG ε => ((‖u.1 k‖ : ℂ)) ^ 2) (muK ε) := fun u =>
    ((Complex.continuous_ofReal.comp (hcont u).norm).pow 2).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have key : ∀ u : I.fns, ((‖I.ι u‖ : ℂ)) ^ 2 = ∫ k : KG ε, ((‖u.1 k‖ : ℂ)) ^ 2 ∂muK ε := fun u => by
    have := I.model.norm_sq u
    rw [← Complex.ofReal_pow, this, ← integral_complex_ofReal]
    push_cast; rfl
  have key' : ∀ u : I.fns, (RCLike.ofReal ‖I.ι u‖ : ℂ) ^ 2 = ∫ k : KG ε, ((‖u.1 k‖ : ℂ)) ^ 2 ∂muK ε := key
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ), ← map_add, ← map_sub, ← map_smul, ← map_sub, ← map_add,
    key', key', key', key']
  have e : (fun k : KG ε => ⟪g.1 k, f.1 k⟫_ℂ) = fun k : KG ε =>
      (((‖(g + f).1 k‖ : ℂ)) ^ 2 - ((‖(g - f).1 k‖ : ℂ)) ^ 2 +
        (((‖(g - (RCLike.I : ℂ) • f).1 k‖ : ℂ)) ^ 2 - ((‖(g + (RCLike.I : ℂ) • f).1 k‖ : ℂ)) ^ 2) * RCLike.I) / 4 := by
    funext k
    rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ)]
    rfl
  rw [e, integral_div]
  congr 1
  have i12 : Integrable (fun k : KG ε => ((‖(g + f).1 k‖ : ℂ)) ^ 2 - ((‖(g - f).1 k‖ : ℂ)) ^ 2) (muK ε) :=
    (int _).sub (int _)
  have i34 : Integrable (fun k : KG ε => (((‖(g - (RCLike.I : ℂ) • f).1 k‖ : ℂ)) ^ 2 -
      ((‖(g + (RCLike.I : ℂ) • f).1 k‖ : ℂ)) ^ 2) * RCLike.I) (muK ε) := ((int _).sub (int _)).mul_const _
  rw [integral_add i12 i34, integral_sub (int _) (int _), integral_mul_const, integral_sub (int _) (int _)]

theorem isKFinFun_mul {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {φ : UJ ε → V} (hφ : IsKFinFun φ) {k : UJ ε} (hk : k ∈ KG ε) : IsKFinFun fun g => φ (g * k) := by
  unfold IsKFinFun at *
  have hle : Submodule.span ℂ {ψ : UJ ε → V | ∃ k' ∈ KG ε, ψ = fun g => (fun g => φ (g * k)) (g * k')} ≤
      Submodule.span ℂ {ψ : UJ ε → V | ∃ k' ∈ KG ε, ψ = fun g => φ (g * k')} := by
    refine Submodule.span_mono ?_
    rintro ψ ⟨k', hk', rfl⟩
    exact ⟨k' * k, mul_mem hk' hk, by funext g; simp [mul_assoc]⟩
  exact Submodule.finiteDimensional_of_le hle

theorem unitary_bound : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε π → IsURepOn (UJset ε) π → ∀ I : IndModule ε, I.Positive → ∀ Z, IsFactor ε I.ρ Z (kFinVec ε I.ρ) π → (∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν → (Z : Set I.H) = I.intKer ν) → ∀ h : 0 < I.a, (I.s ⟨0, h⟩).re ≤ (n : ℝ) - 1 := by
  intro hHC hL n ε V _ _ _ π hπ hπu I hI Z hZ hZker h0
  have hL' := hL
  obtain ⟨hInd, hQuot, -, hLim, -⟩ := hL'
  obtain ⟨hadm, -, hgk, hkfin, -, -⟩ := hInd n ε I
  obtain ⟨ν, hν⟩ := GlobalTheory.Published.Langlands.exists_isHaarSub_nbar I.toDatum
  obtain ⟨hZgk, -, -, T, hTY, hTker, hTK, hTX⟩ := hZ
  have hZne : Z ≠ kFinVec ε I.ρ := by
    obtain ⟨-, -, Z', hZ', -, hne, -⟩ := hQuot n ε I hI ν hν
    have : Z = Z' := SetLike.coe_injective ((hZker ν hν).trans hZ'.symm)
    rw [this]; exact hne
  obtain ⟨a₀, ha₀, ha₀K, ha₀Z⟩ := GlobalTheory.T.k_finite_orthogonal_complement n ε I.H I.ρ hadm Z (fun v hv => hZgk.kFin v hv)
    hZgk.kStable hZne
  obtain ⟨φ₀, hφ₀K, rfl⟩ := (hkfin a₀).1 ha₀K
  have hφ₀ : φ₀.1 ≠ 0 := fun e => ha₀ (by rw [show φ₀ = 0 from Subtype.ext e, map_zero])
  obtain ⟨k, hk, hφk⟩ := (GlobalTheory.T.induced_k_finite_restriction n ε I.toDatum φ₀.1 φ₀.2 hφ₀K).2.2 hφ₀
  set φ : I.fns := ⟨fun g => φ₀.1 (g * k), indFun_mul_right φ₀.2 trivial⟩ with hφdef
  have hφK : IsKFinFun φ.1 := isKFinFun_mul hφ₀K hk
  have hφ1 : φ.1 1 ≠ 0 := by simpa [hφdef] using hφk
  have haρ : I.ι φ = I.ρ (uMat k) (I.ι φ₀) := (I.model.transl k trivial φ₀ φ fun g => rfl).symm
  have haK : IsKFin ε I.ρ (I.ι φ) := (hkfin _).2 ⟨φ, hφK, rfl⟩

  have hiso : ∀ v w : I.H, ⟪I.ρ (uMat k) v, I.ρ (uMat k) w⟫_ℂ = ⟪v, w⟫_ℂ := fun v w =>
    (⟨(I.ρ (uMat k)).toLinearMap, fun v => hadm.2.2.1 _ hk v⟩ : I.H →ₗᵢ[ℂ] I.H).inner_map_map v w
  have hinv : ∀ z, I.ρ (uMat k) (I.ρ (uMat k⁻¹) z) = z := fun z => by
    rw [← ContinuousLinearMap.comp_apply, ← hadm.1.2 _ k.2 _ k⁻¹.2, RealIwasawa.uMat_mul_inv, hadm.1.1]; rfl
  have haZ : ∀ z ∈ Z, ⟪I.ι φ, z⟫_ℂ = 0 := fun z hz => by
    rw [haρ, ← hinv z, hiso]
    exact ha₀Z _ (hZgk.kStable _ (inv_mem hk) z hz)

  obtain ⟨w, hwK, hw⟩ := (GlobalTheory.T.intertwiner_of_k_finite_vectors n ε I.H I.ρ V π hadm hπ.2.1 T hTY (fun k hk y hy => hTK k hk y hy)).1
    (I.ι φ) haK fun y hy hTy => haZ y ((hTker y hy).1 hTy)
  have hTfin : ∀ y, IsKFin ε I.ρ y → IsKFin ε π (T y) := fun y hy => by
    have : T y ∈ (kFinVec ε I.ρ).map T := Submodule.mem_map_of_mem hy
    rw [hTY] at this; exact this
  have hcoef := GlobalTheory.T.smooth_intertwiner_extension hHC n ε I.H I.ρ V π hadm hπ.2.1 hgk
    (fun v hv => (GlobalTheory.T.irreducible_K_stable_finite_subspace n ε V π hπu hπ.2.2).2 v hv) T hTfin (fun k hk y hy => hTK k hk y hy)
    (fun X hX y hy => hTX X hX y hy) (I.ι φ) w haK hwK hw

  obtain ⟨f, hf, hfK, hh, -, hint, hne⟩ := GlobalTheory.T.induced_intertwining_integral_nonzero hHC hL n ε I hI ν hν (φ.1 1) hφ1
  obtain ⟨⟨f', hf', hf'K, hf'φ⟩, hφM, -⟩ := GlobalTheory.T.induced_k_finite_restriction n ε I.toDatum φ.1 φ.2 hφK
  obtain ⟨c, hc, -, hlim⟩ := hLim n ε I.toDatum hI ν hν
  have hf'1 : f' 1 = φ.1 1 := hf'φ 1 (one_mem _)
  have hL0 : (c : ℂ) * ∫ u, ⟪f' 1, f u⟫_ℂ ∂ν ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast hc.ne') ?_
    have := (hint 1 (φ.1 1) hφM).2
    simp only [mul_one] at this
    rw [hf'1, ← this]; exact hne
  have hιf : IsKFin ε I.ρ (I.ι ⟨f, hf⟩) := (hkfin _).2 ⟨⟨f, hf⟩, hfK, rfl⟩
  refine re_le_of_chamber I.j I.pos I.s h0 fun x hx => ?_
  choose t ht using fun r : ℝ => exists_isSplit I.flag (r • x)
  refine re_nonneg_of_tendsto (B := ‖w‖ * ‖T (I.ι ⟨f, hf⟩)‖) (fun r => ?_) hL0
    ((hlim f hf hfK f' hf' hf'K x hx t fun r => (ht r).1).2)
  have e1 : ∫ k : KG ε, ⟪f' k, f (k * t r)⟫_ℂ ∂muK ε = ⟪I.ι φ, I.ρ (uMat (t r)) (I.ι ⟨f, hf⟩)⟫_ℂ := by
    rw [I.model.transl (t r) trivial ⟨f, hf⟩ ⟨_, indFun_mul_right hf trivial⟩ fun g => rfl, inner_ι]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    simp only
    rw [hf'φ k k.2]
  rw [e1, hcoef _ hιf _ (t r).2]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [hπu.2.1 _ (t r).2]

end GlobalTheory.UnitaryBound
end
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_factor_kernel : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε π → IsURepOn (UJset ε) π → ∀ I : IndModule ε, I.Positive → ∀ Z, IsFactor ε I.ρ Z (kFinVec ε I.ρ) π → (∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν → (Z : Set I.H) = I.intKer ν) → ∀ h : 0 < I.a, (I.s ⟨0, h⟩).re ≤ (n : ℝ) - 1 := by
  atlas_forward_decl GlobalTheory.UnitaryBound.unitary_bound
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

noncomputable section

namespace GlobalTheory.StdInfChar

theorem exists_ker_sup_range {M : Type} [AddCommGroup M] [Module ℂ M] (φ : Module.End ℂ M)
    (S : Submodule ℂ M → Prop) (hS : ∀ i : ℕ, S (LinearMap.range (φ ^ i))) (l : ℕ)
    (hl : ∀ (r : ℕ) (Y : Fin (r + 1) → Submodule ℂ M), (∀ i, S (Y i)) → StrictMono Y → r ≤ l) :
    ∃ N : ℕ, LinearMap.ker (φ ^ (N + 1)) ⊔ LinearMap.range (φ ^ (N + 1)) = ⊤ := by
  have hsucc : ∀ i : ℕ, LinearMap.range (φ ^ (i + 1)) = (LinearMap.range (φ ^ i)).map φ := fun i => by
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
  have hle : ∀ i : ℕ, LinearMap.range (φ ^ (i + 1)) ≤ LinearMap.range (φ ^ i) := fun i => by
    rw [pow_succ, Module.End.mul_eq_comp]
    exact LinearMap.range_comp_le_range _ _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, LinearMap.range (φ ^ (N + 1)) = LinearMap.range (φ ^ N) := by
    by_contra h
    push Not at h
    have ha : StrictAnti fun i : ℕ => LinearMap.range (φ ^ i) :=
      strictAnti_nat_of_succ_lt fun i => lt_of_le_of_ne (hle i) (h i)
    have := hl (l + 1) (fun i => LinearMap.range (φ ^ (l + 1 - i.val))) (fun i => hS _) fun i j hij =>
      ha (by have := j.2; have : i.val < j.val := hij; omega)
    omega
  have hst : ∀ m : ℕ, LinearMap.range (φ ^ (N + m)) = LinearMap.range (φ ^ N) := fun m => by
    induction m with
    | zero => rfl
    | succ m ih => rw [← add_assoc, hsucc, ih, ← hsucc, hN]
  refine ⟨N, eq_top_iff.2 fun v _ => ?_⟩
  have : (φ ^ (N + 1)) v ∈ LinearMap.range (φ ^ (N + (N + 2))) := by
    rw [hst, ← hN]; exact ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := this
  refine Submodule.mem_sup.2 ⟨v - (φ ^ (N + 1)) w, ?_, _, ⟨w, rfl⟩, sub_add_cancel _ _⟩
  rw [LinearMap.mem_ker, map_sub, ← hw, ← Module.End.mul_apply, ← pow_add,
    show N + 1 + (N + 1) = N + (N + 2) by omega, sub_self]

variable {n : ℕ} {ε : Fin n → Bool}

theorem exists_lieSet_add (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ X₁ ∈ lieSet ε, ∃ X₂ ∈ lieSet ε, Y = X₁ + Complex.I • X₂ := by
  have hJ := Jm_mul_self ε
  have hJ' : ∀ B : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * B) = B := fun B => by
    rw [← mul_assoc, hJ, one_mul]
  refine ⟨(1 / 2 : ℂ) • (Y - Jm ε * Yᴴ * Jm ε), ?_, (-Complex.I / 2) • (Y + Jm ε * Yᴴ * Jm ε), ?_, ?_⟩
  · change _ᴴ * Jm ε + Jm ε * _ = 0
    simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, Jm_conjTranspose,
      conjTranspose_conjTranspose, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, mul_assoc, hJ, hJ', mul_one]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this]
    module
  · change _ᴴ * Jm ε + Jm ε * _ = 0
    simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, Jm_conjTranspose,
      conjTranspose_conjTranspose, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, mul_assoc, hJ, hJ', mul_one]
    have : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by simp
    rw [this]
    module
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by
      linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]
    module

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_isKFin_ne_zero [CompleteSpace H] [Nontrivial H] (hσ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) σ)
    (hcont : ∀ v, ContinuousOn (fun g => σ g v) (UJset ε)) : ∃ s : H, s ≠ 0 ∧ IsKFin ε σ s := by
  have hKU : ∀ k : KG ε, toMK k ∈ UJset ε := fun k => (maximal_compact_facts n ε).1 _ k.2
  have hc : ∀ x : H, Continuous (fun k : KG ε => σ (toMK k) x) := fun x =>
    (hcont x).comp_continuous (GlobalTheory.KHolExt.isEmb ε).continuous hKU
  have hint : ∀ {E : Type} [NormedAddCommGroup E] {G : KG ε → E}, Continuous G → Integrable G (muK ε) :=
    fun hG => integrableOn_univ.1 (hG.continuousOn.integrableOn_compact isCompact_univ)
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have h1 : σ (toMK (1 : KG ε)) = 1 := hσ.1
  have hex : ∃ p : C(KG ε, ℂ), GlobalTheory.KHolExt.Sep ε p ∧ ∫ k, p k • σ (toMK k) x ∂(muK ε) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := GlobalTheory.KHolExt.eq_zero_of_orth (ε := ε)
      ⟨fun k => ⟪x, σ (toMK k) x⟫_ℂ, continuous_const.inner (hc x)⟩
      (fun p hp => by
        have hi : Integrable (fun k => p k • σ (toMK k) x) (muK ε) := hint (p.continuous.smul (hc x))
        have h2 := integral_inner (𝕜 := ℂ) hi x
        rw [hcon p hp, inner_zero_right] at h2
        simpa only [inner_smul_right, ContinuousMap.coe_mk] using h2)
    have h3 : ⟪x, σ (toMK (1 : KG ε)) x⟫_ℂ = 0 := congrArg (fun f : C(KG ε, ℂ) => f 1) h0
    rw [h1] at h3
    exact hx (inner_self_eq_zero.1 h3)
  obtain ⟨p, ⟨ι, _, a, b, -, h⟩, hp⟩ := hex
  set s := ∫ k, p k • σ (toMK k) x ∂(muK ε) with hs
  have hL : ∀ g : KG ε, σ (toMK g) s ∈
      Submodule.span ℂ (Set.range fun i => ∫ k, b i k • σ (toMK k) x ∂(muK ε)) := by
    intro g
    have hi : Integrable (fun k => p k • σ (toMK k) x) (muK ε) := hint (p.continuous.smul (hc x))
    have e : σ (toMK g) s = ∑ i, a i g • ∫ k, b i k • σ (toMK k) x ∂(muK ε) := by
      rw [hs, ← ContinuousLinearMap.integral_comp_comm _ hi]
      have h2 := integral_mul_left_eq_self (μ := muK ε) (fun k => p (g⁻¹ * k) • σ (toMK k) x) g
      simp only [inv_mul_cancel_left] at h2
      have h3 : ∀ k, σ (toMK g) (p k • σ (toMK k) x) = p k • σ (toMK (g * k)) x := by
        intro k
        rw [map_smul, GlobalTheory.KHolExt.toMK_mul, hσ.2 _ (hKU g) _ (hKU k)]
        rfl
      simp only [h3]
      rw [h2]
      simp only [h, Finset.sum_smul, mul_smul]
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl fun i _ => integral_smul _ _
      · intro i _
        exact hint (continuous_const.smul ((b i).continuous.smul (hc x)))
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range fun i => ∫ k, b i k • σ (toMK k) x ∂(muK ε))
  refine ⟨s, hp, Submodule.span ℂ (Set.range fun g : KG ε => σ (toMK g) s),
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (Set.range_subset_iff.2 hL)),
    Submodule.subset_span ⟨1, by simp only [h1]; rfl⟩, fun k hk v hv => ?_⟩
  rw [← range_toMK] at hk
  obtain ⟨g, rfl⟩ := hk
  refine (Submodule.span_le (p := (Submodule.span ℂ (Set.range fun g : KG ε => σ (toMK g) s)).comap
    (σ (toMK g) : H →ₗ[ℂ] H))).2 ?_ hv
  rintro _ ⟨g', rfl⟩
  refine Submodule.subset_span ⟨g * g', ?_⟩
  dsimp only
  rw [GlobalTheory.KHolExt.toMK_mul, hσ.2 _ (hKU g) _ (hKU g')]
  rfl

theorem isGKSub_map (hσ : IsGKSub ε σ (kFinVec ε σ)) (Y : Submodule ℂ (kFinVec ε σ))
    (hK : ∀ κ ∈ Kset ε, ∀ v w : kFinVec ε σ, (w : H) = σ κ v → v ∈ Y → w ∈ Y)
    (hL : ∀ X ∈ lieSet ε, ∀ v w : kFinVec ε σ, (w : H) = dRep σ X v → v ∈ Y → w ∈ Y) :
    IsGKSub ε σ (Y.map (kFinVec ε σ).subtype) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, -, rfl⟩
    exact hσ.smooth _ v.2
  · rintro _ ⟨v, -, rfl⟩
    exact v.2
  · rintro κ hκ _ ⟨v, hv, rfl⟩
    exact ⟨⟨_, hσ.kStable κ hκ _ v.2⟩, hK κ hκ v _ rfl hv, rfl⟩
  · rintro X hX _ ⟨v, hv, rfl⟩
    exact ⟨⟨_, hσ.lieStable X hX _ v.2⟩, hL X hX v _ rfl hv, rfl⟩

theorem isGKSub_ker_range (hσ : IsGKSub ε σ (kFinVec ε σ)) {φ : Module.End ℂ (kFinVec ε σ)}
    (hφ : IsGKHom ε σ σ φ) : IsGKSub ε σ ((LinearMap.ker φ).map (kFinVec ε σ).subtype) ∧
      IsGKSub ε σ ((LinearMap.range φ).map (kFinVec ε σ).subtype) := by
  have h0 : ∀ X, dRep σ X 0 = 0 := fun X => by simp [dRep]
  refine ⟨isGKSub_map hσ _ (fun κ hκ v w e hv => Subtype.ext ?_) (fun X hX v w e hv => Subtype.ext ?_),
    isGKSub_map hσ _ ?_ ?_⟩
  · rw [hφ.1 κ hκ v w e, LinearMap.mem_ker.1 hv]; simp
  · rw [hφ.2 X hX v w e, LinearMap.mem_ker.1 hv]; simp [h0]
  · rintro κ hκ _ w e ⟨v, rfl⟩
    exact ⟨⟨_, hσ.kStable κ hκ _ v.2⟩, Subtype.ext ((hφ.1 κ hκ v _ rfl).trans e.symm)⟩
  · rintro X hX _ w e ⟨v, rfl⟩
    exact ⟨⟨_, hσ.lieStable X hX _ v.2⟩, Subtype.ext ((hφ.2 X hX v _ rfl).trans e.symm)⟩

theorem isGKHom_pow {φ : Module.End ℂ (kFinVec ε σ)} (hφ : IsGKHom ε σ σ φ) (i : ℕ) : IsGKHom ε σ σ (φ ^ i) := by
  induction i with
  | zero => exact isGKHom_id ε σ
  | succ i ih =>
    rw [pow_succ']
    exact ⟨fun κ hκ v w e => hφ.1 κ hκ _ _ (ih.1 κ hκ v w e), fun X hX v w e => hφ.2 X hX _ _ (ih.2 X hX v w e)⟩

theorem map_etr {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M')
    {E : Fin n → Fin n → Module.End ℂ M} {E' : Fin n → Fin n → Module.End ℂ M'}
    (h : ∀ a b v, T (E a b v) = E' a b (T v)) (k : ℕ) (v : M) : T (etr E k v) = etr E' k (T v) := by
  have : ∀ a b v, T (epow E k a b v) = epow E' k a b (T v) := by
    induction k with
    | zero => intro a b v; simp only [epow]; split_ifs <;> simp
    | succ k ih => intro a b v; simp only [epow, LinearMap.sum_apply, map_sum, Module.End.mul_apply, ih, h]
  simp only [etr, LinearMap.sum_apply, map_sum, this]

theorem ringHom_etr {A B : Type} [Ring A] [Ring B] (f : A →+* B) (E : Fin n → Fin n → A) (k : ℕ) :
    f (etr E k) = etr (fun a b => f (E a b)) k := by
  have : ∀ a b, f (epow E k a b) = epow (fun a b => f (E a b)) k a b := by
    induction k with
    | zero => intro a b; simp only [epow]; split_ifs <;> simp
    | succ k ih => intro a b; simp only [epow, map_sum, map_mul, ih]
  simp only [etr, map_sum, this]

theorem genInfChar_of_isFactor : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε π → (∀ v, IsKFin ε π v → Formalism.QuantumDeterminants.SmoothOnH (Jm ε) (fun g => π g v)) → ∀ χ : Fin n → ℂ, HasInfChar ε χ π → ∀ I : IndModule ε, I.Positive → ∀ Z, IsFactor ε I.ρ Z (kFinVec ε I.ρ) π → (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) := by
  intro hL n ε V _ _ _ π hπ hsm χ hχ I hI Z hF k v hv
  obtain ⟨hadm, ⟨l, hl⟩, hGK, -⟩ := hL.1 n ε I
  obtain ⟨ν, hν⟩ := GlobalTheory.Published.Langlands.exists_isHaarSub_nbar I.toDatum
  obtain ⟨-, -, Z₀, -, hZg, hZ₀, hmax, -⟩ := hL.2.1 n ε I hI ν hν
  obtain ⟨-, -, -, T, hT, -, -, hTL⟩ := hF
  have hTm : ∀ w ∈ kFinVec ε I.ρ, T w ∈ kFinVec ε π := fun w hw => hT ▸ Submodule.mem_map_of_mem hw
  have hGK' : IsGKSub ε π (kFinVec ε π) := by
    refine ⟨fun w hw => GlobalTheory.SmoothCyclicApprox.smoothVec_of_smoothOnH
      (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) (hsm w hw), fun w hw => hw, isKStableOn_kFinVec ε π,
      fun X hX w hw => ?_⟩
    rw [← hT] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rw [← hTL X hX u hu]
    exact hTm _ (hGK.lieStable X hX u hu)
  obtain ⟨A, hA, hP, hact, hK, -⟩ := GlobalTheory.T.gl_relations_on_k_finite_vectors n ε I.H I.ρ hadm hGK
  obtain ⟨A', hA', -, -, -, hχ'⟩ := GlobalTheory.T.gl_relations_on_k_finite_vectors n ε V π hπ.2.1 hGK'
  set E : Fin n → Fin n → Module.End ℂ (kFinVec ε I.ρ) := fun a b => A (Matrix.single a b 1) with hE
  have hgl : GlRel E := by simpa using (hP 1 isUnit_one).1
  set c := gelfVal χ (k + 1)
  set φ : Module.End ℂ (kFinVec ε I.ρ) := etr E (k + 1) - algebraMap ℂ _ c with hφ
  have hφv : ∀ u, φ u = etr E (k + 1) u - c • u := fun u => by simp [hφ]

  have hcomm : ∀ X u, etr E (k + 1) (A X u) = A X (etr E (k + 1) u) := fun X u => by
    have h1 : A X = ∑ a, ∑ b, X a b • E a b := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp only [map_sum, hE, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    have h2 := fun a b u => LinearMap.congr_fun (generatorTraceCentral_holds _ n E hgl (k + 1) a b) u
    simp only [Module.End.mul_apply] at h2
    simp only [h1, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h2]
  have hhom : IsGKHom ε I.ρ I.ρ φ := by
    refine ⟨fun κ hκ u w e => ?_, fun X hX u w e => ?_⟩
    · simp only [hφv, Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul, hK κ hκ (k + 1) u w e, e]
    · obtain rfl : w = A X u := Subtype.ext (e.trans (hA X hX u).symm)
      rw [← hA X hX, hφv, hφv, hcomm, map_sub, map_smul]

  let T' : kFinVec ε I.ρ →ₗ[ℂ] kFinVec ε π := T.restrict hTm
  have hTA : ∀ Y u, T' (A Y u) = A' Y (T' u) := fun Y u => by
    have h1 : ∀ X ∈ lieSet ε, T' (A X u) = A' X (T' u) := fun X hX => Subtype.ext (by
      rw [hA' X hX]
      change T (A X u) = dRep π X (T u)
      rw [hA X hX, hTL X hX _ u.2])
    obtain ⟨X₁, h₁, X₂, h₂, rfl⟩ := exists_lieSet_add ε Y
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h1 _ h₁, h1 _ h₂]
  have hTφ : ∀ u, T' (φ u) = 0 := fun u => by
    rw [hφv, map_sub, map_smul, map_etr T' (fun a b u => hTA _ u), hχ' χ hχ, sub_self]
  obtain ⟨N, hN⟩ := exists_ker_sup_range φ (fun Y => IsGKSub ε I.ρ (Y.map (kFinVec ε I.ρ).subtype))
    (fun i => (isGKSub_ker_range hGK (isGKHom_pow hhom i)).2) l fun r Y hY hm =>
      hl r _ hY ((Submodule.map_strictMono_of_injective (kFinVec ε I.ρ).injective_subtype).comp hm)
  obtain ⟨hker, hran⟩ := isGKSub_ker_range hGK (isGKHom_pow hhom (N + 1))
  have hran' : (LinearMap.range (φ ^ (N + 1))).map (kFinVec ε I.ρ).subtype ≤ Z₀ := by
    refine (hmax _ hran).resolve_left fun e => ?_
    haveI := hπ.1
    obtain ⟨s, hs0, hs⟩ := exists_isKFin_ne_zero hπ.2.1.1 hπ.2.1.2.1
    have : s ∈ (kFinVec ε I.ρ).map T := hT ▸ hs
    obtain ⟨u, hu, rfl⟩ := this
    rw [← e] at hu
    obtain ⟨_, ⟨w, rfl⟩, rfl⟩ := hu
    rw [pow_succ'] at hs0
    exact hs0 (congrArg Subtype.val (hTφ _))
  have hker' : (LinearMap.ker (φ ^ (N + 1))).map (kFinVec ε I.ρ).subtype = kFinVec ε I.ρ := by
    refine (hmax _ hker).resolve_right fun e => hZ₀ (le_antisymm (fun w hw => hZg.kFin w hw) ?_)
    have := sup_le e hran'
    rwa [← Submodule.map_sup, hN, Submodule.map_subtype_top] at this
  refine ⟨N + 1, ?_⟩
  have hv' : v ∈ (LinearMap.ker (φ ^ (N + 1))).map (kFinVec ε I.ρ).subtype := hker'.symm ▸ hv
  obtain ⟨u, hu, rfl⟩ := hv'
  rw [Submodule.subtype_apply, hact, map_pow, map_sub, AlgHom.commutes]
  have := ringHom_etr (FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => A (Matrix.single ab.1 ab.2 1))).toRingHom
    (Egl n) (k + 1)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Egl, FreeAlgebra.lift_ι_apply] at this
  erw [this]
  exact congrArg Subtype.val (LinearMap.mem_ker.1 hu)

end GlobalTheory.StdInfChar
end
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitesimal_character_factor : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε π → (∀ v, IsKFin ε π v → Formalism.QuantumDeterminants.SmoothOnH (Jm ε) (fun g => π g v)) → ∀ χ : Fin n → ℂ, HasInfChar ε χ π → ∀ I : IndModule ε, I.Positive → ∀ Z, IsFactor ε I.ρ Z (kFinVec ε I.ρ) π → (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) := by
  atlas_forward_decl GlobalTheory.StdInfChar.genInfChar_of_isFactor
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.KFinExists

theorem exists_kfin (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [Nontrivial V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V))
    (hπ : IsURepOn (UJset ε) π) : ∃ v, IsKFin ε π v ∧ v ≠ 0 := by
  obtain ⟨⟨h1, hmul⟩, hnorm, hcont⟩ := hπ
  have hmem : ∀ k : Formalism.REAL.KG ε, Formalism.REAL.toMK k ∈ UJset ε := fun k => (k : Formalism.REAL.UJ ε).2
  have hone : Formalism.REAL.toMK (1 : Formalism.REAL.KG ε) = 1 := rfl
  have hmk : ∀ a b : Formalism.REAL.KG ε, Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b :=
    fun _ _ => rfl
  let ρ : Formalism.REAL.KG ε →* (V →L[ℂ] V) :=
    { toFun := fun k => π (Formalism.REAL.toMK k)
      map_one' := by simp only [hone, h1]
      map_mul' := fun a b => by
        simp only [hmk]
        exact hmul _ (hmem a) _ (hmem b) }
  have hcK : Continuous fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  obtain ⟨S, hS0, hSfd, hSinv⟩ := GlobalTheory.T.compact_unitary_finite_invariant_subspace (Formalism.REAL.KG ε) V ρ
    (fun k x => hnorm _ (hmem k) x)
    (fun x => (hcont x).comp_continuous hcK hmem)
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  refine ⟨v, ⟨S, hSfd, hvS, ?_⟩, hv0⟩
  intro g hg x hx
  have hr : g ∈ Set.range (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) := by
    rw [Formalism.REAL.range_toMK]; exact hg
  obtain ⟨k, rfl⟩ := hr
  exact hSinv k x hx

end GlobalTheory.KFinExists
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_k_finite : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] [Nontrivial V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (UJset ε) π → ∃ v, IsKFin ε π v ∧ v ≠ 0 := by
  atlas_forward_decl GlobalTheory.KFinExists.exists_kfin
end

section
open Matrix Formalism.REAL Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.GraphIntertwiner

theorem starProjection_comm {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Γ : Submodule ℂ E) [Γ.HasOrthogonalProjection] (s t : E →L[ℂ] E)
    (hs : ∀ u v, ⟪s u, s v⟫_ℂ = ⟪u, v⟫_ℂ) (hst : ∀ v, s (t v) = v)
    (hsΓ : ∀ v ∈ Γ, s v ∈ Γ) (htΓ : ∀ v ∈ Γ, t v ∈ Γ) (x : E) :
    Γ.starProjection (s x) = s (Γ.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal (hsΓ _ (Γ.starProjection_apply_mem x))
  rw [← map_sub, Submodule.mem_orthogonal]
  intro u hu
  rw [← hst u, hs]
  exact (Submodule.mem_orthogonal _ _).1 (Submodule.sub_starProjection_mem_orthogonal x) _ (htΓ u hu)

noncomputable def inlL (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] : H →L[ℂ] WithLp 2 (H × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H V).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H V)

noncomputable def sumL {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (a : H →L[ℂ] H) (b : V →L[ℂ] V) :
    WithLp 2 (H × V) →L[ℂ] WithLp 2 (H × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H V).symm.toContinuousLinearMap.comp
    ((a.prodMap b).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H V).toContinuousLinearMap)

theorem inlL_apply {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : H) :
    inlL H V x = WithLp.toLp 2 (x, 0) := rfl

theorem sumL_apply {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (a : H →L[ℂ] H) (b : V →L[ℂ] V)
    (z : WithLp 2 (H × V)) :
    sumL a b z = WithLp.toLp 2 (a z.ofLp.1, b z.ofLp.2) := rfl

theorem exists_intertwiner_of_group {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ)) (h1 : 1 ∈ G)
    (hmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) (hinv : ∀ a ∈ G, ∃ b ∈ G, a * b = 1)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V))
    (hρ : IsURepOn G ρ) (hirr : IsIrredOn G ρ) (hπ : IsURepOn G π)
    (T : H →ₗ[ℂ] V) (Y₀ : Set H) (y₀ a₀ : H) (hy₀ : y₀ ∈ Y₀) (hT : T y₀ ≠ 0)
    (hco : ∀ y ∈ Y₀, ∀ g ∈ G, ⟪a₀, ρ g y⟫_ℂ = ⟪T y₀, π g (T y)⟫_ℂ) :
    ∃ B : H →L[ℂ] V, B ≠ 0 ∧ ∀ g ∈ G, ∀ x, B (ρ g x) = π g (B x) := by
  obtain ⟨⟨hρ1, hρm⟩, hρn, -⟩ := hρ
  obtain ⟨⟨hπ1, hπm⟩, hπn, -⟩ := hπ
  have hρi : ∀ g ∈ G, ∀ u v, ⟪ρ g u, ρ g v⟫_ℂ = ⟪u, v⟫_ℂ := fun g hg =>
    (LinearMap.norm_map_iff_inner_map_map (ρ g)).1 (hρn g hg)
  have hπi : ∀ g ∈ G, ∀ u v, ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ := fun g hg =>
    (LinearMap.norm_map_iff_inner_map_map (π g)).1 (hπn g hg)
  let S : Set (WithLp 2 (H × V)) :=
    {z | ∃ g ∈ G, ∃ y ∈ Y₀, z = WithLp.toLp 2 (ρ g y, π g (T y))}
  let Γ : Submodule ℂ (WithLp 2 (H × V)) := (Submodule.span ℂ S).topologicalClosure
  have hΓc : IsClosed (Γ : Set (WithLp 2 (H × V))) := Submodule.isClosed_topologicalClosure _
  have hSΓ : ∀ z ∈ S, z ∈ Γ := fun z hz =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span hz)
  have hle : ∀ K : Submodule ℂ (WithLp 2 (H × V)), IsClosed (K : Set (WithLp 2 (H × V))) →
      (∀ z ∈ S, z ∈ K) → Γ ≤ K := fun K hK hS =>
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 hS) hK
  haveI : CompleteSpace Γ := hΓc.completeSpace_coe
  have hinvt : ∀ g ∈ G, ∀ v ∈ Γ, sumL (ρ g) (π g) v ∈ Γ := by
    intro g hg
    refine hle (Γ.comap (sumL (ρ g) (π g)).toLinearMap)
      (hΓc.preimage (sumL (ρ g) (π g)).continuous) ?_
    rintro z ⟨h, hh, y, hy, rfl⟩
    refine hSΓ _ ⟨g * h, hmul g hg h hh, y, hy, ?_⟩
    rw [hρm g hg h hh, hπm g hg h hh]
    rfl
  have hcomm : ∀ g ∈ G, ∀ x, Γ.starProjection (sumL (ρ g) (π g) x)
      = sumL (ρ g) (π g) (Γ.starProjection x) := by
    intro g hg x
    obtain ⟨b, hb, hgb⟩ := hinv g hg
    refine starProjection_comm Γ _ (sumL (ρ b) (π b)) ?_ ?_ (hinvt g hg) (hinvt b hb) x
    · intro u v
      simp only [sumL_apply, WithLp.prod_inner_apply, hρi g hg, hπi g hg]
    · intro v
      have e1 : ∀ w, ρ g (ρ b w) = w := fun w => by
        have := congrArg (fun f : H →L[ℂ] H => f w) (hρm g hg b hb)
        simpa [hgb, hρ1] using this.symm
      have e2 : ∀ w, π g (π b w) = w := fun w => by
        have := congrArg (fun f : V →L[ℂ] V => f w) (hπm g hg b hb)
        simpa [hgb, hπ1] using this.symm
      simp only [sumL_apply, e1, e2]
  have hy₀Γ : WithLp.toLp 2 (y₀, T y₀) ∈ Γ := hSΓ _ ⟨1, h1, y₀, hy₀, by simp [hρ1, hπ1]⟩
  have horth : ∀ z ∈ Γ, ⟪WithLp.toLp 2 (a₀, -T y₀), z⟫_ℂ = 0 := by
    intro z hz
    have := hle (ℂ ∙ (WithLp.toLp 2 (a₀, -T y₀) : WithLp 2 (H × V)))ᗮ
      (Submodule.isClosed_orthogonal _) (by
        rintro z ⟨g, hg, y, hy, rfl⟩
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
        simp [WithLp.prod_inner_apply, hco y hy g hg]) hz
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 this
  have hinl : ∀ g, ∀ x, inlL H V (ρ g x) = sumL (ρ g) (π g) (inlL H V x) := by
    intro g x
    simp [inlL_apply, sumL_apply]
  refine ⟨(WithLp.sndL 2 ℂ H V).comp (Γ.starProjection.comp (inlL H V)), ?_, ?_⟩
  · intro hB
    have hB' : ∀ x, (Γ.starProjection (inlL H V x)).ofLp.2 = 0 := fun x =>
      congrArg (fun f : H →L[ℂ] V => f x) hB
    rcases hirr (Γ.comap (inlL H V).toLinearMap) (hΓc.preimage (inlL H V).continuous)
      (fun g hg v hv => by
        have : inlL H V (ρ g v) ∈ Γ := by rw [hinl]; exact hinvt g hg _ hv
        exact this) with hL | hL
    · have hP : Γ.starProjection (inlL H V y₀) = 0 := by
        have e : Γ.starProjection (inlL H V y₀)
            = inlL H V (Γ.starProjection (inlL H V y₀)).ofLp.1 := by
          rw [inlL_apply (Γ.starProjection (inlL H V y₀)).ofLp.1, ← hB' y₀]
        have hm : (Γ.starProjection (inlL H V y₀)).ofLp.1 ∈ Γ.comap (inlL H V).toLinearMap := by
          have := Γ.starProjection_apply_mem (inlL H V y₀)
          rw [e] at this
          exact this
        rw [hL, Submodule.mem_bot] at hm
        rw [e, hm, map_zero]
      have ho := Submodule.sub_starProjection_mem_orthogonal (K := Γ) (inlL H V y₀)
      rw [hP, sub_zero] at ho
      have h0 := (Submodule.mem_orthogonal _ _).1 ho _ hy₀Γ
      have h0' : ⟪y₀, y₀⟫_ℂ = 0 := by
        simpa only [inlL_apply, WithLp.prod_inner_apply, inner_zero_right, add_zero] using h0
      exact hT (by rw [inner_self_eq_zero.1 h0', map_zero])
    · have hm : a₀ ∈ Γ.comap (inlL H V).toLinearMap := by rw [hL]; trivial
      have h0 := horth _ hm
      have h0' : ⟪a₀, a₀⟫_ℂ = 0 := by
        have e : (inlL H V).toLinearMap a₀ = WithLp.toLp 2 (a₀, 0) := rfl
        simpa only [e, WithLp.prod_inner_apply, inner_zero_right, add_zero] using h0
      have h2 := hco y₀ hy₀ 1 h1
      rw [inner_self_eq_zero.1 h0', inner_zero_left, hπ1] at h2
      exact hT (inner_self_eq_zero.1 h2.symm)
  · intro g hg x
    show (Γ.starProjection (inlL H V (ρ g x))).ofLp.2 = π g (Γ.starProjection (inlL H V x)).ofLp.2
    rw [hinl, hcomm g hg, sumL_apply]

theorem Jm_mul_Jm {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem exists_right_inv {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : g ∈ UJset ε) : ∃ b ∈ UJset ε, g * b = 1 := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have h1 : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [← Jm_mul_Jm ε]
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg']
  have h2 := mul_eq_one_comm.1 h1
  refine ⟨_, ?_, h2⟩
  generalize Jm ε * gᴴ * Jm ε = b at h2
  show bᴴ * Jm ε * b = Jm ε
  calc bᴴ * Jm ε * b = bᴴ * (gᴴ * Jm ε * g) * b := by rw [hg']
    _ = (g * b)ᴴ * Jm ε * (g * b) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [h2]; simp

theorem exists_intertwiner : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (UJset ε) ρ → IsIrredOn (UJset ε) ρ → IsURepOn (UJset ε) π → ∀ (T : H →ₗ[ℂ] V) (Y₀ : Set H) (y₀ a₀ : H), y₀ ∈ Y₀ → T y₀ ≠ 0 → (∀ y ∈ Y₀, ∀ g ∈ UJset ε, ⟪a₀, ρ g y⟫_ℂ = ⟪T y₀, π g (T y)⟫_ℂ) → ∃ B : H →L[ℂ] V, B ≠ 0 ∧ ∀ g ∈ UJset ε, ∀ x, B (ρ g x) = π g (B x) := by
  intro n ε H _ _ _ ρ V _ _ _ π hρ hirr hπ T Y₀ y₀ a₀ hy₀ hT hco
  refine exists_intertwiner_of_group (UJset ε) ?_ ?_ (exists_right_inv ε) H ρ V π hρ hirr hπ T Y₀ y₀ a₀
    hy₀ hT hco
  · show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  · intro a ha b hb
    have ha' : aᴴ * Jm ε * a = Jm ε := ha
    have hb' : bᴴ * Jm ε * b = Jm ε := hb
    show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
    calc (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Jm ε := by rw [ha', hb']

end GlobalTheory.GraphIntertwiner
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_nonzero_on_generating_set : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (UJset ε) ρ → IsIrredOn (UJset ε) ρ → IsURepOn (UJset ε) π → ∀ (T : H →ₗ[ℂ] V) (Y₀ : Set H) (y₀ a₀ : H), y₀ ∈ Y₀ → T y₀ ≠ 0 → (∀ y ∈ Y₀, ∀ g ∈ UJset ε, ⟪a₀, ρ g y⟫_ℂ = ⟪T y₀, π g (T y)⟫_ℂ) → ∃ B : H →L[ℂ] V, B ≠ 0 ∧ ∀ g ∈ UJset ε, ∀ x, B (ρ g x) = π g (B x) := by
  atlas_forward_decl GlobalTheory.GraphIntertwiner.exists_intertwiner
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory

theorem jm_mul_self_uj {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem jm_conjTranspose_uj {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

theorem exists_inv_mem_UJset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : ∃ h ∈ UJset ε, h * g = 1 ∧ g * h = 1 := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hJ := jm_mul_self_uj ε
  have hJs := jm_conjTranspose_uj ε
  set J := Formalism.REAL.Jm ε
  have hhg : (J * gᴴ * J) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hJ]
  have hgh : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.1 hhg
  refine ⟨J * gᴴ * J, ?_, hhg, hgh⟩
  have hgJ : g * J * gᴴ = J := by
    have : g * J * gᴴ * J * J = J := by
      rw [show g * J * gᴴ * J = g * (J * gᴴ * J) by simp only [Matrix.mul_assoc], hgh, Matrix.one_mul]
    rwa [Matrix.mul_assoc (g * J * gᴴ), hJ, Matrix.mul_one] at this
  show (J * gᴴ * J)ᴴ * J * (J * gᴴ * J) = J
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJs]
  calc J * (g * J) * J * (J * gᴴ * J) = J * (g * J * (J * J) * gᴴ) * J := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [hJ, Matrix.mul_one, hgJ, hJ, Matrix.one_mul]

theorem star_eq_of_inv_UJset {n : ℕ} {ε : Fin n → Bool} {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] {σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)}
    (hσ : IsURepOn (UJset ε) σ) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε)
    (hgh : g * h = 1) : star (σ g) = σ h := by
  have h1 : star (σ g) * σ g = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (σ g)).1 (hσ.2.1 g hg)
  have h2 : σ g * σ h = 1 := by
    rw [ContinuousLinearMap.mul_def, ← hσ.1.2 g hg h hh, hgh, hσ.1.1]
  calc star (σ g) = star (σ g) * (σ g * σ h) := by rw [h2, mul_one]
    _ = σ h := by rw [← mul_assoc, h1, one_mul]

end GlobalTheory

namespace GlobalTheory

theorem uEquiv_of_intertwiner_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (UJset ε) ρ → IsIrredOn (UJset ε) ρ → IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → ∀ B : H →L[ℂ] V, B ≠ 0 → (∀ g ∈ UJset ε, ∀ x, B (ρ g x) = π g (B x)) → UEquiv ε π ρ := by
  intro n ε H _ _ _ ρ V _ _ _ π hρ hρi hπ hπi B hB hBc

  have hBadj : ∀ g ∈ UJset ε, ∀ v, B.adjoint (π g v) = ρ g (B.adjoint v) := by
    intro g hg v
    obtain ⟨h, hh, hhg, hgh⟩ := exists_inv_mem_UJset hg
    have hcomp : B ∘L ρ h = π h ∘L B := ContinuousLinearMap.ext fun x => hBc h hh x
    have := congrArg ContinuousLinearMap.adjoint hcomp
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      star_eq_of_inv_UJset hρ hh hg hhg, star_eq_of_inv_UJset hπ hh hg hhg] at this
    exact (DFunLike.congr_fun this v).symm
  set A : H →L[ℂ] H := B.adjoint ∘L B with hAdef
  have hAsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, hAdef, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  obtain ⟨c, hc⟩ := hilbert_schur_selfAdjoint H (UJset ε) (fun g => ρ g.1)
    (fun S hS hinv => hρi S hS (fun g hg v hv => hinv ⟨g, hg⟩ v hv)) A hAsa
    (fun g => ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.mul_apply, hAdef, ContinuousLinearMap.comp_apply]
      rw [hBc g.1 g.2 x, hBadj g.1 g.2])

  have hnorm : ∀ x, ((‖B x‖ ^ 2 : ℝ) : ℂ) = c * ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have h1 : ⟪x, A x⟫_ℂ = ⟪B x, B x⟫_ℂ := by
      simp only [hAdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [hc] at h1
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right] at h1
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    push_cast
    exact_mod_cast h1.symm
  obtain ⟨x0, hx0⟩ : ∃ x0, B x0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hB (ContinuousLinearMap.ext hcon)
  have hx0' : x0 ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  set r : ℝ := c.re with hr
  have hcr : c = (r : ℂ) := by
    have := hnorm x0
    have hpos : (0 : ℝ) < ‖x0‖ ^ 2 := by positivity
    have hc' : c = ((‖B x0‖ ^ 2 / ‖x0‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, this, mul_div_assoc, div_self (by exact_mod_cast hpos.ne'), mul_one]
    rw [hr, hc', Complex.ofReal_re]
  have hnormr : ∀ x, ‖B x‖ ^ 2 = r * ‖x‖ ^ 2 := by
    intro x
    have := hnorm x
    rw [hcr, ← Complex.ofReal_mul] at this
    exact_mod_cast this
  have hrpos : 0 < r := by
    have := hnormr x0
    have h1 : (0 : ℝ) < ‖B x0‖ ^ 2 := by positivity
    have h2 : (0 : ℝ) < ‖x0‖ ^ 2 := by positivity
    nlinarith
  set s : ℝ := Real.sqrt r with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hrpos

  let U : H →L[ℂ] V := ((s⁻¹ : ℝ) : ℂ) • B
  have hU : ∀ x, ‖U x‖ = ‖x‖ := by
    intro x
    have hBx : ‖B x‖ = s * ‖x‖ := by
      rw [hs, ← Real.sqrt_sq (norm_nonneg (B x)), hnormr x, Real.sqrt_mul hrpos.le,
        Real.sqrt_sq (norm_nonneg x)]
    simp only [U, ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos hspos, hBx]
    field_simp
  have hUc : ∀ g ∈ UJset ε, ∀ x, U (ρ g x) = π g (U x) := by
    intro g hg x
    simp only [U, ContinuousLinearMap.smul_apply, hBc g hg x, map_smul]
  let L : H →ₗᵢ[ℂ] V := { toLinearMap := U.toLinearMap, norm_map' := hU }
  have hrange : LinearMap.range L.toLinearMap = ⊤ := by
    rcases hπi (LinearMap.range L.toLinearMap)
      (L.antilipschitz.isClosed_range L.isometry.uniformContinuous) (by
        rintro g hg v ⟨x, rfl⟩
        exact ⟨ρ g x, (hUc g hg x)⟩) with h | h
    · exfalso
      have hmem : L x0 ∈ LinearMap.range L.toLinearMap := ⟨x0, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      apply hx0'
      rw [← norm_eq_zero, ← L.norm_map x0, hmem, norm_zero]
    · exact h
  have hsurj : Function.Surjective L := by
    intro y
    have : y ∈ LinearMap.range L.toLinearMap := by rw [hrange]; trivial
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩
  let e : H ≃ₗᵢ[ℂ] V := LinearIsometryEquiv.ofSurjective L hsurj
  refine ⟨e.symm, fun g hg v => e.injective ?_⟩
  rw [LinearIsometryEquiv.apply_symm_apply]
  show π g v = U (ρ g (e.symm v))
  rw [hUc g hg]
  congr 1
  exact (e.apply_symm_apply v).symm

end GlobalTheory
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_intertwiner_schur : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (UJset ε) ρ → IsIrredOn (UJset ε) ρ → IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → ∀ B : H →L[ℂ] V, B ≠ 0 → (∀ g ∈ UJset ε, ∀ x, B (ρ g x) = π g (B x)) → UEquiv ε π ρ := by
  atlas_forward_decl GlobalTheory.uEquiv_of_intertwiner_ne_zero
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.UnitaryFromModules

theorem uEquiv_of_isFactor : GlobalTheory.Published.HarishChandraAnalyticity → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε ρ → IsURepOn (UJset ε) ρ → IsIrrAdm ε π → IsURepOn (UJset ε) π → ∀ Z, IsFactor ε ρ Z (kFinVec ε ρ) π → UEquiv ε π ρ := by
  intro hHC n ε H _ _ _ ρ V _ _ _ π hρ hρU hπ hπU Z hF
  obtain ⟨-, hY, -, T, hmap, -, hK, hL⟩ := hF
  haveI : Nontrivial V := hπ.1
  obtain ⟨w, hwK, hw0⟩ := GlobalTheory.T.exists_nonzero_k_finite n ε V π hπU
  have hw : w ∈ (kFinVec ε ρ).map T := hmap ▸ hwK
  obtain ⟨y₀, hy₀, rfl⟩ := hw
  have hTK : ∀ y, IsKFin ε ρ y → IsKFin ε π (T y) := fun y hy =>
    (hmap ▸ Submodule.mem_map_of_mem (f := T) (show y ∈ kFinVec ε ρ from hy) : T y ∈ kFinVec ε π)
  obtain ⟨a₀, ha₀, hrz⟩ := (GlobalTheory.T.intertwiner_of_k_finite_vectors n ε H ρ V π hρ.2.1 hπ.2.1 T hmap
    (fun k hk y hy => hK k hk y hy)).2 (T y₀) hwK
  have hsm := (GlobalTheory.T.irreducible_K_stable_finite_subspace n ε V π hπU hπ.2.2).2
  have hco := GlobalTheory.T.smooth_intertwiner_extension hHC n ε H ρ V π hρ.2.1 hπ.2.1 hY hsm T hTK (fun k hk y hy => hK k hk y hy)
    (fun X hX y hy => hL X hX y hy) a₀ (T y₀) ha₀ hwK hrz
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.intertwiner_nonzero_on_generating_set n ε H ρ V π hρU hρ.2.2 hπU T {y | IsKFin ε ρ y} y₀ a₀ hy₀ hw0 hco
  exact GlobalTheory.T.bounded_intertwiner_schur n ε H ρ V π hρU hρ.2.2 hπU hπ.2.2 B hB0 hB

end GlobalTheory.UnitaryFromModules

end
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_factor_equivalence : GlobalTheory.Published.HarishChandraAnalyticity → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε ρ → IsURepOn (UJset ε) ρ → IsIrrAdm ε π → IsURepOn (UJset ε) π → ∀ Z, IsFactor ε ρ Z (kFinVec ε ρ) π → UEquiv ε π ρ := by
  atlas_forward_decl GlobalTheory.UnitaryFromModules.uEquiv_of_isFactor
end

section
section
noncomputable section

open MeasureTheory
open Formalism.REAL (UJ)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset)
open GlobalTheory.Dec (HasInfChar UEquiv)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep IsUnitEquiv)
open GlobalTheory.OpTrace (HasTrace repOp)
open GlobalTheory.RealInd (IsIrrAdm groupRep IndModule)
open GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation (HasWideGaps)

namespace GlobalTheory.SepPseudo

theorem wide_gap {r : ℕ} {lam : Fin r → ℤ} (h : HasWideGaps lam) {i j : Fin r} (hij : i < j) :
    (r : ℤ) ≤ lam i - lam j := by
  have hij' : (i : ℕ) < j := hij
  have hk : (i : ℕ) + 1 < r := by omega
  have h1 := h.2 i ⟨(i : ℕ) + 1, hk⟩ rfl
  have h2 : lam j ≤ lam ⟨(i : ℕ) + 1, hk⟩ := h.1.antitone (by rw [Fin.le_def]; simp; omega)
  linarith

theorem ujMat_surj {n : ℕ} {ε : Fin n → Bool} : ∀ x ∈ UJset ε, ∃ g, ujMat ε g = x := fun x hx => by
  obtain ⟨g, hg, -⟩ := GlobalTheory.RealIwasawa.exists_uMat x hx
  exact ⟨g, hg⟩

theorem isIrredOn_of_equiv {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H H' : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (U : H ≃ₗᵢ[ℂ] H') (hU : ∀ g ∈ G, ∀ v, U (ρ g v) = σ g (U v)) (h : IsIrredOn G σ) : IsIrredOn G ρ := by
  intro S hS hst
  let e := U.toLinearEquiv
  have hS' : IsClosed ((S.map (e : H →ₗ[ℂ] H') : Submodule ℂ H') : Set H') := by
    rw [Submodule.map_coe]
    exact U.toHomeomorph.isClosedMap _ hS
  rcases h _ hS' (fun g hg w hw => by
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨ρ g v, hst g hg v hv, hU g hg v⟩) with h0 | h1
  · left
    rw [eq_bot_iff]
    intro v hv
    have : e v ∈ S.map (e : H →ₗ[ℂ] H') := ⟨v, hv, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    simpa using this
  · right
    rw [eq_top_iff]
    intro v _
    have : e v ∈ S.map (e : H →ₗ[ℂ] H') := h1 ▸ Submodule.mem_top
    obtain ⟨w, hw, hwe⟩ := this
    rwa [e.injective hwe] at hw

theorem isTempered_of_isUnitEquiv {G V W : Type} [Group G] [MeasurableSpace G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {μ : Measure G}
    {π : G →* (V →L[ℂ] V)} {π' : G →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') (ht : GlobalTheory.Orb.IsTempered μ π) :
    GlobalTheory.Orb.IsTempered μ π' := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨v, hv, hi⟩ := ht
  refine ⟨A v, by simpa using hv, fun r hr => ?_⟩
  simpa [← hA, LinearIsometryEquiv.inner_map_map] using hi r hr

theorem pseudoCoeffSeparation (hA : GlobalTheory.Published.HarishChandraAnalyticity) (_hP : GlobalTheory.Published.PseudoCoefficientUpq)
    (hC : GlobalTheory.Published.HarishChandraCharacters) (hL : GlobalTheory.Published.LanglandsClassification) :
    GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation := by
  intro r _ ε lam hlam X _ _ _ D hD μ _ f hf V _ _ _ π hπ c hc hc0
  have hinf : HasInfChar ε (fun a => (lam a : ℂ)) π :=
    GlobalTheory.T.pseudocoefficient_trace_infinitesimal hL hC r ε _ X D hD.1.2.2.1 hD.2 μ f hf V π hπ c hc hc0
  refine ⟨hinf, fun hU => ?_⟩
  obtain ⟨b, W₀, hW₀⟩ := GlobalTheory.RealInd.exists_isMinimalFlag ε
  obtain ⟨⟨I, hI, Z, hZ, hker⟩, -⟩ := hL.2.2.1 r ε b W₀ hW₀ V π hπ
  by_cases ha : 0 < I.a
  · exfalso
    have hsm := (GlobalTheory.T.irreducible_K_stable_finite_subspace r ε V π hU hπ.2.2).2
    have hgen := GlobalTheory.T.infinitesimal_character_factor hL r ε V π hπ hsm _ hinf I hI.2 Z hZ
    obtain ⟨I', ha', hj', hre, hgen'⟩ := GlobalTheory.T.positive_induced_module_shift hL r ε I ha _ hgen
    obtain ⟨i, j, hij, he⟩ := GlobalTheory.T.infinitesimal_character_difference hL r ε I' ha' hj' _ hgen'
    have hb := GlobalTheory.T.unitary_factor_kernel hA hL r ε V π hπ hU I hI.2 Z hZ hker ha
    have hpos : 0 < (I.s ⟨0, ha⟩).re := hI.2.2 _
    have hre' : ((lam i : ℝ) - lam j) = (I.s ⟨0, ha⟩).re := by
      rw [← hre, ← he]; simp
    rcases lt_or_gt_of_ne hij with h | h
    · have h1 : ((r : ℤ) : ℝ) ≤ ((lam i - lam j : ℤ) : ℝ) := Int.cast_le.2 (wide_gap hlam h)
      push_cast at h1
      linarith
    · have h1 : ((r : ℤ) : ℝ) ≤ ((lam j - lam i : ℤ) : ℝ) := Int.cast_le.2 (wide_gap hlam h)
      push_cast at h1
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
  · have ha0 : I.a = 0 := by omega
    obtain ⟨hM, U, hUρ⟩ := GlobalTheory.Published.Langlands.equiv_of_zero I ha0
    have ht := I.temp
    rw [show GlobalTheory.RealInd.leviOne ε I.W = ⊤ from hM] at ht
    obtain ⟨hσn, hσi, hσU, hσt⟩ := (GlobalTheory.RealInd.isIrrTempered_top_iff μ).1 ht
    have hAdm := (hL.1 r ε I).1
    have hρn : Nontrivial I.H := U.toLinearEquiv.toEquiv.nontrivial
    have hρU : IsURepOn (UJset ε) I.ρ := ⟨I.isCRepOn, fun g hg v => by
      rw [← U.norm_map, hUρ g hg v, hσU.2.1 g hg, U.norm_map], hAdm.2.1⟩
    have hρ : IsIrrAdm ε I.ρ := ⟨hρn, hAdm, isIrredOn_of_equiv U hUρ hσi⟩
    obtain ⟨T, hT⟩ := GlobalTheory.T.unitary_factor_equivalence hA r ε I.H I.ρ V π hρ hρU hπ hU Z hZ
    have hπσ : IsUnitEquiv (ujRep hσU) (ujRep hU) :=
      ⟨(T.trans U).symm, fun g v => by
        have hg : ujMat ε g ∈ UJset ε := g.2
        change (T.trans U).symm (I.σ (ujMat ε g) v) = π (ujMat ε g) ((T.trans U).symm v)
        apply (T.trans U).injective
        rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.trans_apply, hT _ hg, hUρ _ hg,
          ← LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]⟩
    have hπt : GlobalTheory.Orb.IsTempered μ (ujRep hU) := isTempered_of_isUnitEquiv hπσ hσt
    haveI := hπ.1
    have hc' : HasTrace (repOp (ujRep hU) μ f) c := hc
    have hπD : IsUnitEquiv (ujRep hU) (ujRep hD.1.2.2.1) := by
      by_contra hne
      have h0 := hf.trace_other V (ujRep hU)
        (GlobalTheory.Orb.isUnitaryRep_repVia hU (fun g => g.2) GlobalTheory.HCChar.continuous_ujMat)
        (GlobalTheory.Orb.isTopIrreducible_repVia hU (fun g => g.2) ujMat_surj hπ.2.2) hπt hne
      exact hc0 (hc'.2.symm.trans h0.2)
    refine ⟨?_, ?_⟩
    · obtain ⟨A, hA'⟩ := hπD
      refine ⟨A, fun g hg v => ?_⟩
      obtain ⟨g', rfl⟩ := ujMat_surj g hg
      exact hA' g' v
    · have h1 := hπD.symm.hasTrace hf.trace_self
      exact hc'.2.symm.trans h1.2

end GlobalTheory.SepPseudo
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudocoefficient_separation_of_harish_chandra : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.PseudoCoefficientUpq → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.Published.LanglandsClassification → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation := by
  atlas_forward_decl GlobalTheory.SepPseudo.pseudoCoeffSeparation
end
