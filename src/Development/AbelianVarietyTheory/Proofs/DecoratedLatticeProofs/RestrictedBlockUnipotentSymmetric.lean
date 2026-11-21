import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCongruenceIffFlagConditions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterArgumentCongrRootEntrySumMod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralAdeleCongrZeroOfResiduesSquarefree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesProductNotMemSqPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdelePrescribedResiduesAndConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueSupportSinglePlaceToConjugatePairPosition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterResidueFieldsEqProdGenericShift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameRescaleConjReductionsDiagonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteField

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeConjPg

theorem pg_places_not_isConjPl : ∀ {D : D7} (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D Pg _ he PP hP PP' hP'
  obtain ⟨e, he⟩ := he
  exact GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he PP hP PP' hP'

end GlobalTheory.SeeConjPg
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces : ∀ {D : D7} (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  atlas_forward_decl GlobalTheory.SeeConjPg.pg_places_not_isConjPl
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.FlagBasis

theorem flagVec_mem_and_span (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I)
    (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 →
      (∀ j, flagVec e0 f0 z0 bw bwd j ∈ I.Lf) ∧
        ∀ y ∈ I.Lf, InMod I g (Set.range fun j : Fin I.n => flagVec e0 f0 z0 bw bwd j.val) y := by
  intro hF hn
  obtain ⟨⟨hef, hz, hb⟩, -, -, -, ⟨hidem, horth, hint, -⟩, ⟨hbw, hbwd⟩, -, hspan⟩ := hF
  refine ⟨fun j => ?_, fun y hy => ?_⟩
  · unfold flagVec
    split_ifs with h1 h2 h3 h4
    · exact (hef _).1
    · exact I.Lf.add_mem (hb _).1 (hb _).2
    · exact hz
    · exact (hef _).2
    · exact I.Lf.zero_mem
  · set R : Set (VA I) := Set.range fun j : Fin I.n => flagVec e0 f0 z0 bw bwd j.val with hR
    have hmem : ∀ j, j < I.n → flagVec e0 f0 z0 bw bwd j ∈ Submodule.span (IntAf I.F I.E) R :=
      fun j hj => Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    have hsig : sigA I ew ∈ IntAf I.F I.E := Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem I hint
    have hc : ∀ l : Fin k, flagVec e0 f0 z0 bw bwd (ρ + l.val) = bw l + bwd (Fin.rev l) := by
      intro l
      have h1 : ¬ (ρ + l.val < ρ) := by omega
      have h2 : ρ + l.val - ρ < k := by omega
      unfold flagVec
      rw [dif_neg h1, dif_pos h2]
      congr <;> simp
    have hcl : ∀ l : Fin k, flagVec e0 f0 z0 bw bwd (ρ + l.val) ∈ Submodule.span (IntAf I.F I.E) R :=
      fun l => hmem _ (by omega)
    have hsub : Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd ⊆
        (Submodule.span (IntAf I.F I.E) R : Set (VA I)) := by
      rintro v ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | hv) | ⟨l, rfl⟩) | ⟨l, rfl⟩)
      · have h := hmem a.val (by omega)
        unfold flagVec at h
        rwa [dif_pos a.isLt] at h
      · have h := hmem (2 * ρ + k - a.val) (by omega)
        have h1 : ¬ (2 * ρ + k - a.val < ρ) := by omega
        have h2 : ¬ (2 * ρ + k - a.val - ρ < k) := by omega
        have h3 : ¬ (2 * ρ + k - a.val = ρ + k) := by omega
        have h4 : 2 * ρ + k - (2 * ρ + k - a.val) < ρ := by omega
        unfold flagVec at h
        rw [dif_neg h1, dif_neg h2, if_neg h3, dif_pos h4] at h
        have e : (⟨2 * ρ + k - (2 * ρ + k - a.val), h4⟩ : Fin ρ) = a := by ext; simp; omega
        rwa [e] at h
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        have h := hmem (ρ + k) (by omega)
        have h1 : ¬ (ρ + k < ρ) := by omega
        have h2 : ¬ (ρ + k - ρ < k) := by omega
        unfold flagVec at h
        rwa [dif_neg h1, dif_neg h2, if_pos rfl] at h
      · have h := Submodule.smul_mem _ (⟨ew, hint⟩ : IntAf I.F I.E) (hcl l)
        rw [hc l] at h
        have e : ((⟨ew, hint⟩ : IntAf I.F I.E) • (bw l + bwd (Fin.rev l)) : VA I) = bw l := by
          show ew • (bw l + bwd (Fin.rev l)) = bw l
          rw [smul_add, hbwd (Fin.rev l), smul_smul, horth, zero_smul, add_zero, ← hbw l]
        rwa [e] at h
      · have h := Submodule.smul_mem _ (⟨sigA I ew, hsig⟩ : IntAf I.F I.E) (hcl (Fin.rev l))
        rw [hc (Fin.rev l), Fin.rev_rev] at h
        have e : ((⟨sigA I ew, hsig⟩ : IntAf I.F I.E) • (bw (Fin.rev l) + bwd l) : VA I) = bwd l := by
          show sigA I ew • (bw (Fin.rev l) + bwd l) = bwd l
          rw [smul_add, hbw (Fin.rev l), smul_smul, mul_comm, horth, zero_smul, zero_add,
            hbwd l, smul_smul, ← map_mul, hidem]
        rwa [e] at h
    have := hspan y hy
    exact sup_le_sup_right (Submodule.span_le.2 hsub) _ this

end GlobalTheory.FlagBasis
end

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagVec_mem_Lf_and_inMod : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → (∀ j, flagVec e0 f0 z0 bw bwd j ∈ I.Lf) ∧ ∀ y ∈ I.Lf, InMod I g (Set.range fun j : Fin I.n => flagVec e0 f0 z0 bw bwd j.val) y := by
  atlas_forward_decl GlobalTheory.FlagBasis.flagVec_mem_and_span
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftFrameMod

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

theorem det_one_sub_smul (c : R) (X : Matrix (Fin n) (Fin n) R) :
    ∃ a : R, (1 - c • X).det = 1 - c * a := by
  have h : Ideal.Quotient.mk (Ideal.span {c}) (1 - c • X).det = 1 := by
    rw [RingHom.map_det]
    have : (Ideal.Quotient.mk (Ideal.span {c})).mapMatrix (1 - c • X) = 1 := by
      ext i j
      simp [Matrix.one_apply, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self c)]
    rw [this, Matrix.det_one]
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {c})), Ideal.Quotient.eq] at h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨-a, by linear_combination -ha⟩

theorem isUnit_mix {e g : R} (he : e * e = e) (hu : ∀ a : R, IsUnit (1 - e * g * a))
    (M C X : Matrix (Fin n) (Fin n) R) (h : M * C = 1 - g • X) :
    IsUnit (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) := by
  have h1 : (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) * (e • C + (1 - e) • 1) = 1 - (e * g) • X := by
    rw [GlobalTheory.IdemSupport.mix_mul he, h, Matrix.one_mul, smul_sub, smul_smul, sub_add_eq_add_sub,
      GlobalTheory.IdemSupport.mix_self]
  obtain ⟨a, ha⟩ := det_one_sub_smul (e * g) X
  rw [Matrix.isUnit_iff_isUnit_det]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, ha] at h2
  exact isUnit_of_mul_isUnit_left (h2 ▸ hu a : IsUnit _)

theorem exists_lift {A : Type} [CommRing A] (S : Subring A) (g : ℕ) {e t : S} (he : e * e = e) (ht : 1 - e = g * t)
    (hu : ∀ a : S, IsUnit (1 - e * g * a)) (Λ : Submodule S (Fin n → A)) (β₀ : GL (Fin n) A)
    (hβ : ∀ x, x ∈ Λ ↔ ∀ i, ((β₀⁻¹).val *ᵥ x) i ∈ S) (b : Fin n → Fin n → A) (hb : ∀ j, b j ∈ Λ)
    (hs : ∀ y ∈ Λ, y ∈ Submodule.span S (Set.range b) ⊔ Submodule.span S {y | ∃ x ∈ Λ, y = (g : A) • x}) :
    ∃ β : GL (Fin n) A, (∀ x, x ∈ Λ ↔ ∀ i, ((β⁻¹).val *ᵥ x) i ∈ S) ∧
      ∀ j, ∃ x ∈ Λ, (fun i => β.val i j) - b j = (g : A) • x := by
  have hback : ∀ v : Fin n → A, (β₀⁻¹).val *ᵥ (β₀.val *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  have hback' : ∀ v : Fin n → A, β₀.val *ᵥ ((β₀⁻¹).val *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  have hint : ∀ v : Fin n → S, β₀.val *ᵥ (fun i => (v i : A)) ∈ Λ := fun v => (hβ _).2 fun i => by
    rw [hback]; exact (v i).2
  let M : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨((β₀⁻¹).val *ᵥ b j) i, (hβ _).1 (hb j) i⟩
  have hg : ∀ z ∈ Submodule.span S {y | ∃ x ∈ Λ, y = (g : A) • x}, ∃ x ∈ Λ, z = (g : A) • x := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨x + y, add_mem hx hy, (smul_add _ _ _).symm⟩
    | smul a x _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact ⟨a • x, Λ.smul_mem a hx, smul_comm _ _ _⟩
  have hcol : ∀ k : Fin n, ∃ c r : Fin n → S, ∀ i, (M *ᵥ c) i = (1 : Matrix (Fin n) (Fin n) S) i k - g * r i := by
    intro k
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hs _ (hint fun i => (1 : Matrix (Fin n) (Fin n) S) i k))
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hy
    obtain ⟨x, hx, rfl⟩ := hg z hz
    refine ⟨c, fun i => ⟨_, (hβ x).1 hx i⟩, fun i => Subtype.ext ?_⟩
    have h1 := congrArg (fun v => ((β₀⁻¹).val *ᵥ v) i) hyz
    simp only [hback, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_sum,
      Finset.sum_apply] at h1
    have h2 : (((M *ᵥ c) i : S) : A) = ∑ j, c j • ((β₀⁻¹).val *ᵥ b j) i := by
      change S.subtype (∑ j, M i j * c j) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h2, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, SubringClass.coe_natCast, ← h1, add_sub_cancel_right]
  choose c r hcr using hcol
  obtain ⟨U, hU⟩ := isUnit_mix he hu M (Matrix.of fun i k => c k i) (Matrix.of fun i k => r k i) (by
    ext i k
    exact congrArg Subtype.val (hcr k i))
  have hmv : ∀ (V : GL (Fin n) S) (v : Fin n → A), (∀ i, v i ∈ S) →
      ∀ i, ((GeneralLinearGroup.map S.subtype V).val *ᵥ v) i ∈ S := fun V v hv i => by
    change ∑ j, (V.val i j : A) * v j ∈ S
    exact sum_mem fun j _ => mul_mem (V.val i j).2 (hv j)
  refine ⟨β₀ * GeneralLinearGroup.map S.subtype U, fun x => ?_, fun j => ?_⟩
  · rw [hβ, _root_.mul_inv_rev, Units.val_mul, ← mulVec_mulVec, ← map_inv]
    refine ⟨hmv _ _, fun h => ?_⟩
    have := hmv U _ h
    rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec] at this
  · refine ⟨_, hint fun i => t * ((1 : Matrix (Fin n) (Fin n) S) i j - M i j), ?_⟩
    have h1 : (fun i => (β₀ * GeneralLinearGroup.map S.subtype U).val i j) =
        β₀.val *ᵥ fun i => (U.val i j : A) := rfl
    rw [h1, ← hback' (b j), ← mulVec_sub, ← mulVec_smul]
    congr 1
    funext i
    have h2 : U.val i j - M i j = g * (t * ((1 : Matrix (Fin n) (Fin n) S) i j - M i j)) := by
      rw [hU, ← mul_assoc, ← ht]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have h3 := congrArg Subtype.val h2
    rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, SubringClass.coe_natCast] at h3
    exact h3

end Alg

open GlobalTheory.StdFrames GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

theorem valued_natCast_lt_one_iff {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) (N : ℕ) :
    Valued.v (N : Q.adicCompletion E) < 1 ↔ (N : 𝓞 E) ∈ Q.asIdeal := by
  rw [← Q.valuation_lt_one_iff_mem (K := E) (N : 𝓞 E), ← Formalism.UG.P.levelaf_valued_algebraMap]
  simp

theorem exists_inv_of_valued {D : D7} (z : Ef D) (h : ∀ Q : Pl D.host.E, Valued.v (cpt Q z) = 1) :
    ∃ y ∈ OA D, z * y = 1 := by
  have hi : ∀ Q : Pl D.host.E, (cpt Q z)⁻¹ ∈ Q.adicCompletionIntegers D.host.E := fun Q => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]
  obtain ⟨y, hy⟩ := GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)
    (⟨fun Q => (cpt Q z)⁻¹, Filter.Eventually.of_forall hi⟩ : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  have h1 : ∀ Q : Pl D.host.E, cpt Q y = (cpt Q z)⁻¹ := fun Q => by
    change toAd D y Q = _
    rw [hy]
    rfl
  refine ⟨y, (mem_OA_iff y).2 fun Q => h1 Q ▸ hi Q, cpt_ext fun Q => ?_⟩
  rw [RingHom.map_mul, RingHom.map_one, h1, mul_inv_cancel₀]
  intro h0
  have := h Q
  rw [h0, Valuation.map_zero] at this
  exact zero_ne_one this

theorem coe_one_sub {A : Type} [CommRing A] (S : Subring A) (g : ℕ) (e a : S) :
    ((1 - e * g * a : S) : A) = 1 - e * g * a := by
  push_cast
  rfl

theorem one_sub_eq {A : Type} [CommRing A] (S : Subring A) {g : ℕ} {c e : A} (hc : (g : A) * c = 1) (he : e ∈ S)
    (ht : c * (1 - e) ∈ S) : (1 - ⟨e, he⟩ : S) = g * ⟨_, ht⟩ := by
  refine Subtype.ext ?_
  push_cast
  rw [← mul_assoc, hc, one_mul]

section Val

variable {A K Γ : Type} [CommRing A] [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (φ : A →+* K)

theorem val_quot_le {g : ℕ} {c e : A} (hc : (g : A) * c = 1) (h : φ e = 1 ∨ φ e = 0 ∧ v (g : K) = 1) :
    v (φ (c * (1 - e))) ≤ 1 := by
  rcases h with h | ⟨h, h1⟩
  · simp [h]
  · have h2 := congrArg (fun x => v (φ x)) hc
    simp only [map_mul, map_natCast, map_one, h1, one_mul] at h2
    simp [h, h2]

theorem val_one_sub {g : ℕ} {a e : A} (ha : v (φ a) ≤ 1) (h : φ e = 1 ∧ v (g : K) < 1 ∨ φ e = 0) :
    v (φ (1 - e * g * a)) = 1 := by
  rcases h with ⟨h, h1⟩ | h
  · rw [map_sub, map_one, map_mul, map_mul, map_natCast, h, one_mul]
    refine Valuation.map_one_sub_of_lt _ ?_
    rw [map_mul]
    exact (mul_le_of_le_one_right' ha).trans_lt h1
  · simp [h]

end Val

theorem quot_mem {D : D7} {g : ℕ} {c e : Ef D} (hc : (g : Ef D) * c = 1)
    (he1 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∈ Q.asIdeal → cpt Q e = 1)
    (he0 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∉ Q.asIdeal → cpt Q e = 0) : c * (1 - e) ∈ OA D :=
  (mem_OA_iff _).2 fun Q => by
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (val_quot_le Valued.v (cpt Q) hc ?_)
    by_cases hQ : (g : 𝓞 D.host.E) ∈ Q.asIdeal
    · exact Or.inl (he1 Q hQ)
    · exact Or.inr ⟨he0 Q hQ, le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
        (natCast_mem (Q.adicCompletionIntegers D.host.E) g))
        (not_lt.1 fun h => hQ ((valued_natCast_lt_one_iff Q g).1 h))⟩

theorem valued_one_sub {D : D7} {g : ℕ} {a e : Ef D} (ha : a ∈ OA D)
    (he1 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∈ Q.asIdeal → cpt Q e = 1)
    (he0 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∉ Q.asIdeal → cpt Q e = 0) (Q : Pl D.host.E) :
    Valued.v (cpt Q (1 - e * g * a)) = 1 := by
  refine val_one_sub Valued.v (cpt Q)
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((mem_OA_iff _).1 ha Q)) ?_
  by_cases hQ : (g : 𝓞 D.host.E) ∈ Q.asIdeal
  · exact Or.inl ⟨he1 Q hQ, (valued_natCast_lt_one_iff Q g).2 hQ⟩
  · exact Or.inr (he0 Q hQ)

theorem exists_idem_over (D : D7) {g : ℕ} (hg : g ≠ 0) :
    ∃ e c : Ef D, e * e = e ∧ e ∈ OA D ∧ (g : Ef D) * c = 1 ∧ c * (1 - e) ∈ OA D ∧
      ∀ a ∈ OA D, ∃ y ∈ OA D, (1 - e * g * a) * y = 1 := by
  obtain ⟨e, he, heO, he1, he0⟩ := exists_idem {Q : Pl D.host.E | (g : 𝓞 D.host.E) ∈ Q.asIdeal}
  obtain ⟨c, hc⟩ : ∃ c : Ef D, (g : Ef D) * c = 1 := by
    refine ⟨algebraMap D.host.E (Ef D) (g : D.host.E)⁻¹, ?_⟩
    rw [← map_natCast (algebraMap D.host.E (Ef D)), ← RingHom.map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hg),
      RingHom.map_one]
  exact ⟨e, c, he, heO, hc, quot_mem hc he1 he0, fun a ha => exists_inv_of_valued _ (valued_one_sub ha he1 he0)⟩

theorem idem_subring {A : Type} [CommRing A] (S : Subring A) {g : ℕ}
    (h : ∃ e c : A, e * e = e ∧ e ∈ S ∧ (g : A) * c = 1 ∧ c * (1 - e) ∈ S ∧
      ∀ a ∈ S, ∃ y ∈ S, (1 - e * g * a) * y = 1) :
    ∃ e t : S, e * e = e ∧ 1 - e = g * t ∧ ∀ a : S, IsUnit (1 - e * g * a) := by
  obtain ⟨e, c, he, heS, hc, ht, hu⟩ := h
  refine ⟨⟨e, heS⟩, ⟨_, ht⟩, Subtype.ext he, one_sub_eq S hc heS ht, fun a => ?_⟩
  obtain ⟨y, hy, h⟩ := hu a a.2
  refine IsUnit.of_mul_eq_one ⟨y, hy⟩ (Subtype.ext ?_)
  rw [MulMemClass.coe_mul, coe_one_sub]
  exact h

theorem hatL_eq_Lf (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => ⟨⟨y, hy⟩, h⟩, fun ⟨y, h⟩ => ⟨y.1, y.2, h⟩⟩

theorem exists_isLiftFrame : ∀ (D : D7) (g : ℕ), g ≠ 0 → ∀ b : ℕ → VA (instOf D), (∀ j, b j ∈ (instOf D).Lf) →
    (∀ y ∈ (instOf D).Lf, InMod (instOf D) g (Set.range fun j : Fin (instOf D).n => b j.val) y) →
    ∃ β, IsLiftFrame (instOf D) g b β := by
  intro D g hg b hb hs
  obtain ⟨e, t, he, ht, hu⟩ := idem_subring (IntAf (instOf D).F (instOf D).E) (g := g) (exists_idem_over D hg)
  generalize instOf D = I at *
  obtain ⟨β₀, h₀⟩ := GlobalTheory.latticeFrame.exists_frame I.F I.E I.n I.L ⟨I.L_fg, I.L_span⟩
  obtain ⟨β, h1, h2⟩ := exists_lift (IntAf I.F I.E) g he ht hu I.Lf β₀ (fun x => hatL_eq_Lf I ▸ h₀ x)
    (fun j => b j.val) (fun j => hb j.val) hs
  exact ⟨β, fun x => (hatL_eq_Lf I).symm ▸ h1 x, fun j => Submodule.subset_span (h2 j)⟩

end GlobalTheory.LiftFrameMod

end
end

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeFrame_lifting_spanning_vectors_mod : ∀ (D : D7) (g : ℕ), g ≠ 0 → ∀ b : ℕ → VA (instOf D), (∀ j, b j ∈ (instOf D).Lf) → (∀ y ∈ (instOf D).Lf, InMod (instOf D) g (Set.range fun j : Fin (instOf D).n => b j.val) y) → ∃ β, IsLiftFrame (instOf D) g b β := by
  atlas_forward_decl GlobalTheory.LiftFrameMod.exists_isLiftFrame
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FlagBasis.GramLift
open Formalism.L2.SG.Pf.unitaryCongruence

theorem hatL_eq (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩; exact ⟨y, hy, rfl⟩

theorem col_mem (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hF : IsFrame β I.L) (j : Fin I.n) :
    (fun i => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j) ∈ I.Lf := by
  rw [← hatL_eq]
  refine (hF _).2 fun i => ?_
  have h1 : ((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β = 1 := Units.inv_mul β
  have h2 : ((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)).mulVec
      (fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j) i = (1 : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j := by
    rw [← h1]; rfl
  have h3 : (1 : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ IntAf I.F I.E := by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← h2] at h3
  exact h3

section
variable (I : AutInst) (g : ℕ)

theorem Z_of_eq {a b : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (h : a = b) (hb : ZMod' I g b) : ZMod' I g a := h ▸ hb

theorem Z_symm {x y : VA I} (h : ZMod' I g (hA I x y)) : ZMod' I g (hA I y x) := by
  rw [hA_symm]; exact Z_sig I g h

theorem Z_symm_sub {x y : VA I} {c : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (h : ZMod' I g (hA I x y - c)) :
    ZMod' I g (hA I y x - sigA I c) := by
  rw [hA_symm, ← map_sub]; exact Z_sig I g h

theorem Z_sub_zero {a : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (h : ZMod' I g a) : ZMod' I g (a - 0) := by rwa [sub_zero]

theorem Z_addR {x y z : VA I} (h : ZMod' I g (hA I x y)) (h' : ZMod' I g (hA I x z)) :
    ZMod' I g (hA I x (y + z)) := by
  rw [hA_add_right]; exact Z_add I g h h'

theorem idem_sum {z0 : VA I} {ew : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hz : z0 ∈ I.Lf) (hzz : ZMod' I g (hA I z0 z0 + 1))
    (hint : ew ∈ IntAf I.F I.E) (hfull : ∀ y ∈ I.Lf, (1 - ew - sigA I ew) • y ∈ mL I g) :
    ZMod' I g (1 - ew - sigA I ew) := by
  have hc : (1 - ew - sigA I ew) ∈ IntAf I.F I.E := sub_mem (sub_mem (one_mem _) hint) (sigA_mem I hint)
  have h1 : ZMod' I g (hA I z0 ((1 - ew - sigA I ew) • z0)) := mL_Qs I g hz (hfull z0 hz)
  rw [hA_smul_right] at h1
  exact Z_of_eq I g (by ring) (Z_sub I g (Z_smul I g hc hzz) h1)

theorem middle {k : ℕ} {bw bwd : Fin k → VA I} {ew : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (horth : ew * sigA I ew = 0)
    (hbw : ∀ i, bw i = ew • bw i) (hbwd : ∀ i, bwd i = sigA I ew • bwd i)
    (hdual : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0))
    (hsum : ZMod' I g (1 - ew - sigA I ew)) (l m : Fin k) :
    ZMod' I g (hA I (bw l + bwd l.rev) (bw m + bwd m.rev) - if m = l.rev then 1 else 0) := by
  have hbb : hA I (bw l) (bw m) = 0 := by
    calc hA I (bw l) (bw m) = hA I (ew • bw l) (ew • bw m) := by rw [← hbw l, ← hbw m]
      _ = (ew * sigA I ew) * hA I (bw l) (bw m) := by rw [hA_smul_left, hA_smul_right]; ring
      _ = 0 := by rw [horth, zero_mul]
  have hdd : hA I (bwd l.rev) (bwd m.rev) = 0 := by
    calc hA I (bwd l.rev) (bwd m.rev) = hA I (sigA I ew • bwd l.rev) (sigA I ew • bwd m.rev) := by
          rw [← hbwd l.rev, ← hbwd m.rev]
      _ = (ew * sigA I ew) * hA I (bwd l.rev) (bwd m.rev) := by
          rw [hA_smul_left, hA_smul_right, sigA_sigA]; ring
      _ = 0 := by rw [horth, zero_mul]
  have h3 := hdual l.rev m
  have h4 := Z_symm_sub I g (hdual m.rev l)
  rw [hA_add_left, hA_add_right, hA_add_right, hbb, hdd]
  by_cases hml : m = l.rev
  · rw [if_pos hml.symm] at h3
    rw [if_pos (by rw [hml, Fin.rev_rev])] at h4
    rw [if_pos hml]
    exact Z_of_eq I g (by ring) (Z_sub I g (Z_add I g h3 h4) hsum)
  · rw [if_neg (fun h => hml h.symm)] at h3
    rw [if_neg (fun h => hml (by rw [← h, Fin.rev_rev])), map_zero] at h4
    rw [if_neg hml]
    exact Z_of_eq I g (by ring) (Z_add I g h3 h4)

end

theorem flagVec_cases {V : Type} [AddCommGroup V] {ρ k : ℕ} (e0 f0 : Fin ρ → V) (z0 : V) (bw bwd : Fin k → V)
    (j : ℕ) (hj : j < 2 * ρ + k + 1) :
    (∃ a : Fin ρ, j = a.1 ∧ dualIdx ρ k j = 2 * ρ + k - a.1 ∧ flagVec e0 f0 z0 bw bwd j = e0 a) ∨
    (∃ l : Fin k, j = ρ + l.1 ∧ dualIdx ρ k j = ρ + (k - (l.1 + 1)) ∧
      flagVec e0 f0 z0 bw bwd j = bw l + bwd l.rev) ∨
    (j = ρ + k ∧ dualIdx ρ k j = ρ + k ∧ flagVec e0 f0 z0 bw bwd j = z0) ∨
    (∃ a : Fin ρ, j = 2 * ρ + k - a.1 ∧ dualIdx ρ k j = a.1 ∧ flagVec e0 f0 z0 bw bwd j = f0 a) := by
  by_cases h1 : j < ρ
  · refine Or.inl ⟨⟨j, h1⟩, rfl, ?_, ?_⟩
    · unfold dualIdx; rw [if_pos h1]
    · unfold flagVec; rw [dif_pos h1]
  by_cases h2 : j - ρ < k
  · refine Or.inr (Or.inl ⟨⟨j - ρ, h2⟩, ?_, ?_, ?_⟩)
    · show j = ρ + (j - ρ); omega
    · show dualIdx ρ k j = ρ + (k - (j - ρ + 1)); unfold dualIdx; split_ifs <;> omega
    · unfold flagVec; rw [dif_neg h1, dif_pos h2]
  by_cases h3 : j = ρ + k
  · refine Or.inr (Or.inr (Or.inl ⟨h3, ?_, ?_⟩))
    · unfold dualIdx; split_ifs <;> omega
    · unfold flagVec; rw [dif_neg h1, dif_neg h2, if_pos h3]
  have h4 : 2 * ρ + k - j < ρ := by omega
  refine Or.inr (Or.inr (Or.inr ⟨⟨2 * ρ + k - j, h4⟩, ?_, ?_, ?_⟩))
  · show j = 2 * ρ + k - (2 * ρ + k - j); omega
  · show dualIdx ρ k j = 2 * ρ + k - j; unfold dualIdx; split_ifs <;> omega
  · unfold flagVec; rw [dif_neg h1, dif_neg h2, if_neg h3, dif_pos h4]

section
variable {R : Type} [CommRing R] {n ρ k : ℕ} {i j : Fin n}

theorem flagGram_zero (h : j.val ≠ dualIdx ρ k i.val) : flagGram R n ρ k i j = 0 := if_neg h

theorem flagGram_neg (h : j.val = dualIdx ρ k i.val) (h' : i.val = ρ + k) : flagGram R n ρ k i j = -1 :=
  (if_pos h).trans (if_pos h')

theorem flagGram_ite {p : Prop} [Decidable p] (h : j.val = dualIdx ρ k i.val ↔ p) (h' : i.val ≠ ρ + k) :
    flagGram R n ρ k i j = if p then 1 else 0 := by
  by_cases hp : p
  · rw [if_pos hp]; exact (if_pos (h.2 hp)).trans (if_neg h')
  · rw [if_neg hp]; exact if_neg fun hh => hp (h.1 hh)

end

section
variable {I : AutInst} {g : ℕ} {ρ k : ℕ} {e0 f0 : Fin ρ → VA I} {z0 : VA I} {bw bwd : Fin k → VA I} {ew : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)}

theorem flagVec_mem (hR : IsRefFrame I g e0 f0 z0 bw bwd ew) (j : ℕ) (hj : j < 2 * ρ + k + 1) :
    flagVec e0 f0 z0 bw bwd j ∈ I.Lf := by
  obtain ⟨⟨hef, hz, hb⟩, -⟩ := hR
  rcases flagVec_cases e0 f0 z0 bw bwd j hj with ⟨a, -, -, hv⟩ | ⟨l, -, -, hv⟩ | ⟨-, -, hv⟩ | ⟨a, -, -, hv⟩ <;> rw [hv]
  · exact (hef a).1
  · exact add_mem (hb l).1 (hb _).2
  · exact hz
  · exact (hef a).2

theorem flagVec_gram (hR : IsRefFrame I g e0 f0 z0 bw bwd ew) {n : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    ZMod' I g (hA I (flagVec e0 f0 z0 bw bwd i.val) (flagVec e0 f0 z0 bw bwd j.val) - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) n ρ k i j) := by
  obtain ⟨⟨hef, hz, hb⟩, hgram, ⟨hzz, hez⟩, hW, ⟨hid, horth, hint, hfull⟩, ⟨hbw, hbwd⟩, hdual, -⟩ := hR
  have hsum := idem_sum I g hz hzz hint hfull
  have hec : ∀ a m, ZMod' I g (hA I (e0 a) (bw m + bwd m.rev)) := fun a m =>
    Z_addR I g ((hW m).2.2 a).1 ((hW m.rev).2.2 a).2.2.1
  have hfc : ∀ a m, ZMod' I g (hA I (f0 a) (bw m + bwd m.rev)) := fun a m =>
    Z_addR I g ((hW m).2.2 a).2.1 ((hW m.rev).2.2 a).2.2.2
  have hzc : ∀ m, ZMod' I g (hA I z0 (bw m + bwd m.rev)) := fun m =>
    Z_addR I g (hW m).1 (hW m.rev).2.1
  have hi0 : i.val < 2 * ρ + k + 1 := hn ▸ i.isLt
  have hj0 : j.val < 2 * ρ + k + 1 := hn ▸ j.isLt
  rcases flagVec_cases e0 f0 z0 bw bwd i hi0 with ⟨a, hi, hd, hv⟩ | ⟨a, hi, hd, hv⟩ | ⟨hi, hd, hv⟩ | ⟨a, hi, hd, hv⟩ <;>
    rcases flagVec_cases e0 f0 z0 bw bwd j hj0 with ⟨b, hj, -, hw⟩ | ⟨b, hj, -, hw⟩ | ⟨hj, -, hw⟩ | ⟨b, hj, -, hw⟩ <;>
    rw [hv, hw]
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hgram a b).1
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hec a b)
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hez a).1
  · rw [flagGram_ite (p := a = b) (by rw [Fin.ext_iff]; omega) (by omega)]; exact (hgram a b).2.2
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hec b a))
  · rw [flagGram_ite (p := b = a.rev) (by rw [Fin.ext_iff, Fin.val_rev]; omega) (by omega)]
    exact middle I g horth hbw hbwd hdual hsum a b
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hzc a))
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hfc b a))
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hez b).1)
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hzc b)
  · rw [flagGram_neg (by omega) hi, sub_neg_eq_add]; exact hzz
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hez b).2)
  · rw [flagGram_ite (p := b = a) (by rw [Fin.ext_iff]; omega) (by omega)]
    have h := Z_symm_sub I g (hgram b a).2.2
    rwa [apply_ite (sigA I), map_one, map_zero] at h
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hfc a b)
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hez a).2
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hgram a b).2.1

end

theorem gramIn_lift : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)
    (ew : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 →
    ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β →
      ZMod' I g (1 - ew - sigA I ew) ∧
        (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) := by
  intro I g ρ k e0 f0 z0 bw bwd ew hR hn β hL
  refine ⟨idem_sum I g hR.1.2.1 hR.2.2.1.1 hR.2.2.2.2.1.2.2.1 hR.2.2.2.2.1.2.2.2, fun i j => ?_⟩
  have h0 := flagVec_gram hR hn i j
  have hi0 : i.val < 2 * ρ + k + 1 := by have := i.isLt; omega
  have h1 := Z_symm I g (mL_Qs I g (col_mem I hL.1 j) (hL.2 i))
  have h2 : ZMod' I g (hA I _ _) := mL_Qs I g (flagVec_mem hR i hi0) (hL.2 j)
  rw [hA_sub_right] at h2
  have h3 := hA_add_left I ((fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l i) - flagVec e0 f0 z0 bw bwd i.val)
    (flagVec e0 f0 z0 bw bwd i.val) (fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j)
  rw [sub_add_cancel] at h3
  refine Z_of_eq I g ?_ (Z_add I g (Z_add I g h1 h2) h0)
  unfold gramIn
  rw [h3]; ring

end GlobalTheory.FlagBasis.GramLift
end
end

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftFrame_gram_congr_flagGram : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → ZMod' I g (1 - ew - sigA I ew) ∧ (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) := by
  atlas_forward_decl GlobalTheory.FlagBasis.GramLift.gramIn_lift
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FlagUnit

theorem flagGram_map' {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n ρ k : ℕ) :
    (flagGram A n ρ k).map f = flagGram B n ρ k := by
  ext i j; simp only [flagGram, Matrix.map_apply]; split_ifs <;> simp

theorem gramIn_eq_cT (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    gramIn I β = Formalism.UG.cT (sigA I) (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  ext i j
  simp only [gramIn, hA, Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gramIn_invariant (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (x : I.Gf)
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
    (hM : I.fmat x * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * M) :
    Formalism.UG.cT (sigA I) M * gramIn I β * M = gramIn I β := by
  have hx : Formalism.UG.cT (sigA I) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * I.fmat x =
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := x.2
  rw [gramIn_eq_cT]
  calc Formalism.UG.cT (sigA I) M * (Formalism.UG.cT (sigA I) (β : Matrix _ _ _) *
        I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix _ _ _)) * M
      = Formalism.UG.cT (sigA I) ((β : Matrix _ _ _) * M) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) *
          ((β : Matrix _ _ _) * M) := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT (sigA I) (β : Matrix _ _ _) * (Formalism.UG.cT (sigA I) (I.fmat x) *
          I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * I.fmat x) * (β : Matrix _ _ _) := by
        rw [← hM, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hx]

theorem unitary_reduce : ∀ (I : AutInst) (g ρ k : ℕ) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ (K : Type) [CommRing K] (p : Formalism.L2.Herm.intAf I.F I.E →+* K), (g : K) = 0 → ∀ (x : I.Gf) (m : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)), frGL β m = (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) → ((m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (p.comp (sigInt I)))ᵀ * flagGram K I.n ρ k * (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map p = flagGram K I.n ρ k := by
  intro I g ρ k β hG K _ p hg x m hx
  have hG' : ∀ i j, ∃ t ∈ IntAf I.F I.E, gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j =
      (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t := hG
  choose t ht htt using hG'
  let ts : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E) := fun i j => ⟨t i j, ht i j⟩
  let GS : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E) := fun i j => flagGram (Formalism.L2.Herm.intAf I.F I.E) I.n ρ k i j + (g : (Formalism.L2.Herm.intAf I.F I.E)) * ts i j
  have hGS : GS.map (Formalism.L2.Herm.intAf I.F I.E).subtype = gramIn I β := by
    ext i j
    have := htt i j
    have h2 : (Formalism.L2.Herm.intAf I.F I.E).subtype (flagGram (Formalism.L2.Herm.intAf I.F I.E) I.n ρ k i j) = flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j := by
      rw [← Matrix.map_apply (f := (Formalism.L2.Herm.intAf I.F I.E).subtype), flagGram_map']
    show (Formalism.L2.Herm.intAf I.F I.E).subtype (GS i j) = _
    simp only [GS, ts, map_add, map_mul, map_natCast, h2]
    show _ + (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t i j = _
    rw [← this]; ring
  have hM : I.fmat x * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (Formalism.L2.Herm.intAf I.F I.E).subtype := by
    show ((x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * _ = _
    rw [← hx]
    simp only [frGL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, Units.val_mul]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rfl
  have hinv := gramIn_invariant I β x _ hM
  have hS : ((m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (sigInt I))ᵀ * GS * (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) = GS := by
    apply Matrix.map_injective (f := (Formalism.L2.Herm.intAf I.F I.E).subtype) Subtype.val_injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, hGS]
    convert hinv using 3
    ext i j
    simp [Formalism.UG.cT, sigInt_coe]
  have := congrArg (fun N => N.map p) hS
  simp only [Matrix.map_mul] at this
  have hGK : GS.map p = flagGram K I.n ρ k := by
    ext i j
    show p (GS i j) = _
    have h2 : p (flagGram (Formalism.L2.Herm.intAf I.F I.E) I.n ρ k i j) = flagGram K I.n ρ k i j := by
      rw [← Matrix.map_apply (f := p), flagGram_map']
    simp only [GS, map_add, map_mul, map_natCast, hg, zero_mul, add_zero, h2]
  rw [hGK] at this
  convert this using 3
  ext i j
  simp [Matrix.map_apply]

end GlobalTheory.FlagUnit

end
end

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_liftedFlagBasis_reduce_mod_level : ∀ (I : AutInst) (g ρ k : ℕ) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ (K : Type) [CommRing K] (p : Formalism.L2.Herm.intAf I.F I.E →+* K), (g : K) = 0 → ∀ (x : I.Gf) (m : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)), frGL β m = (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) → ((m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (p.comp (sigInt I)))ᵀ * flagGram K I.n ρ k * (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map p = flagGram K I.n ρ k := by
  atlas_forward_decl GlobalTheory.FlagUnit.unitary_reduce
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.FlagDual

theorem dualIdx_lt {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) {i : ℕ} (hi : i < n) : dualIdx ρ k i < n := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_dualIdx {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) {i : ℕ} (hi : i < n) :
    dualIdx ρ k (dualIdx ρ k i) = i := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_eq_self_iff {n ρ k i : ℕ} (hn : n = 2 * ρ + k + 1) (hi : i < n) : dualIdx ρ k i = ρ + k ↔ i = ρ + k := by
  unfold dualIdx; split_ifs <;> omega

def tau {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) : Fin n := ⟨dualIdx ρ k i.val, dualIdx_lt hn i.2⟩

def sgn (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : K := if i.val = ρ + k then -1 else 1

theorem sgn_mul_self (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : sgn K ρ k i * sgn K ρ k i = 1 := by
  unfold sgn; split_ifs <;> simp

theorem gram_col (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    flagGram K n ρ k i j = if i = tau hn j then sgn K ρ k j else 0 := by
  have hi := dualIdx_dualIdx hn i.2
  have hj := dualIdx_dualIdx hn j.2
  unfold flagGram sgn
  by_cases h1 : j.val = dualIdx ρ k i.val
  · have h2 : i = tau hn j := by
      ext; show i.val = dualIdx ρ k j.val; rw [h1, hi]
    rw [if_pos h1, if_pos h2]
    have h3 : (i.val = ρ + k ↔ j.val = ρ + k) := by
      rw [h1, dualIdx_eq_self_iff hn i.2]
    by_cases h4 : i.val = ρ + k
    · rw [if_pos h4, if_pos (h3.1 h4)]
    · rw [if_neg h4, if_neg (fun h => h4 (h3.2 h))]
  · have h2 : i ≠ tau hn j := by
      intro h; apply h1; rw [h]; show j.val = dualIdx ρ k (dualIdx ρ k j.val); rw [hj]
    rw [if_neg h1, if_neg h2]

theorem gram_row (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    flagGram K n ρ k i j = if j = tau hn i then sgn K ρ k i else 0 := by
  unfold flagGram sgn
  by_cases h1 : j.val = dualIdx ρ k i.val
  · rw [if_pos h1, if_pos (Fin.ext h1)]
  · rw [if_neg h1, if_neg (fun h => h1 (congrArg Fin.val h))]

theorem gram_mul_gram (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) :
    flagGram K n ρ k * flagGram K n ρ k = 1 := by
  ext i j
  rw [mul_apply, Finset.sum_eq_single (tau hn i)]
  · rw [gram_row K hn i (tau hn i), if_pos rfl, gram_row K hn (tau hn i) j]
    have hii : tau hn (tau hn i) = i := Fin.ext (dualIdx_dualIdx hn i.2)
    rw [hii]
    by_cases hij : j = i
    · subst hij; rw [if_pos rfl, one_apply_eq]
      have : sgn K ρ k (tau hn j) = sgn K ρ k j := by
        unfold sgn tau; simp only [dualIdx_eq_self_iff hn j.2]
      rw [this, sgn_mul_self]
    · rw [if_neg hij, mul_zero, one_apply_ne (Ne.symm hij)]
  · intro b _ hb; rw [gram_row K hn i b, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem gram_conj_apply (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1)
    (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (flagGram K n ρ k * A * flagGram K n ρ k) i j = sgn K ρ k i * sgn K ρ k j * A (tau hn i) (tau hn j) := by
  rw [mul_apply, Finset.sum_eq_single (tau hn j)]
  · rw [gram_col K hn (tau hn j) j, if_pos rfl, mul_apply, Finset.sum_eq_single (tau hn i)]
    · rw [gram_row K hn i (tau hn i), if_pos rfl]; ring
    · intro b _ hb; rw [gram_row K hn i b, if_neg hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; rw [gram_col K hn b j, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.FlagDual

namespace GlobalTheory.FlagDual

theorem dual_apply (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (M M' : GL (Fin n) K)
    (h : (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k)
    (i j : Fin n) :
    (M' : Matrix (Fin n) (Fin n) K) i j =
      sgn K ρ k j * sgn K ρ k i * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (tau hn j) (tau hn i) := by
  set G := flagGram K n ρ k
  have h1 : (M' : Matrix (Fin n) (Fin n) K)ᵀ * G = G * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have hM : (M : Matrix (Fin n) (Fin n) K) * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (M' : Matrix (Fin n) (Fin n) K)ᵀ * G
        = (M' : Matrix (Fin n) (Fin n) K)ᵀ * G * ((M : Matrix (Fin n) (Fin n) K) *
            ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hM, Matrix.mul_one]
      _ = G * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [← Matrix.mul_assoc, h]
  have h2 : (M' : Matrix (Fin n) (Fin n) K)ᵀ = G * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * G := by
    rw [← h1, Matrix.mul_assoc, gram_mul_gram K hn, Matrix.mul_one]
  have h3 := congrFun (congrFun h2 j) i
  rw [transpose_apply] at h3
  rw [h3, gram_conj_apply K hn]

end GlobalTheory.FlagDual

theorem GlobalTheory.FlagDual.unipSym_of_dual :
    ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K,
      (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k →
      M ∈ unipSym K n ρ k → M' ∈ unipSym K n ρ k := by
  intro K _ n ρ k hn M M' h hM
  have hN : M⁻¹ ∈ unipSym K n ρ k := Subgroup.inv_mem _ hM
  obtain ⟨⟨hNl, hNd⟩, hNc⟩ := hN
  have hd := GlobalTheory.FlagDual.dual_apply K hn M M' h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j hji
    have hji' : j.val < i.val := hji
    rw [hd i j]
    by_cases hi : i.val = ρ + k
    · by_cases hj : j.val < ρ
      · rw [hNl (show (GlobalTheory.FlagDual.tau hn i).val < (GlobalTheory.FlagDual.tau hn j).val by
          show dualIdx ρ k i.val < dualIdx ρ k j.val
          unfold dualIdx; split_ifs <;> omega), mul_zero]
      · rw [hNc (GlobalTheory.FlagDual.tau hn j) (GlobalTheory.FlagDual.tau hn i)
          (by show ρ ≤ dualIdx ρ k j.val; unfold dualIdx; split_ifs <;> omega)
          (by show dualIdx ρ k j.val < ρ + k; unfold dualIdx; split_ifs <;> omega)
          (by show dualIdx ρ k i.val = ρ + k; unfold dualIdx; split_ifs <;> omega), mul_zero]
    · rw [hNl (show (GlobalTheory.FlagDual.tau hn i).val < (GlobalTheory.FlagDual.tau hn j).val by
        have := i.2; have := j.2
        show dualIdx ρ k i.val < dualIdx ρ k j.val
        unfold dualIdx; split_ifs <;> omega), mul_zero]
  · intro i
    rw [hd i i, hNd, mul_one, GlobalTheory.FlagDual.sgn_mul_self]
  · intro i j h0 h1 h2
    rw [hd i j, hNl (show (GlobalTheory.FlagDual.tau hn i).val < (GlobalTheory.FlagDual.tau hn j).val by
      show dualIdx ρ k i.val < dualIdx ρ k j.val
      unfold dualIdx; split_ifs <;> omega), mul_zero]
end

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricUnipotent_mem_of_flagBasisDual : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → M ∈ unipSym K n ρ k → M' ∈ unipSym K n ρ k := by
  atlas_forward_decl GlobalTheory.FlagDual.unipSym_of_dual
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.FlagCase

theorem dualIdx_lt' {ρ k a : ℕ} (h : a < 2 * ρ + k + 1) : dualIdx ρ k a < 2 * ρ + k + 1 := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_iff' {ρ k a b : ℕ} (ha : a < 2 * ρ + k + 1) (hb : b < 2 * ρ + k + 1) :
    a = dualIdx ρ k b ↔ b = dualIdx ρ k a := by
  unfold dualIdx; split_ifs <;> omega

theorem mul_flagGram_apply {K : Type} [CommRing K] {ρ k : ℕ}
    (A : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) (i j : Fin (2 * ρ + k + 1)) :
    (A * flagGram K (2 * ρ + k + 1) ρ k) i j =
      A i ⟨dualIdx ρ k j.val, dualIdx_lt' j.2⟩ * (if dualIdx ρ k j.val = ρ + k then -1 else 1) := by
  rw [mul_apply, Finset.sum_eq_single ⟨dualIdx ρ k j.val, dualIdx_lt' j.2⟩]
  · simp only [flagGram, Fin.val_mk]
    rw [if_pos ((dualIdx_iff' j.2 (dualIdx_lt' j.2)).mpr rfl)]
  · intro l _ hl
    simp only [flagGram]
    rw [if_neg, mul_zero]
    intro h
    exact hl (Fin.ext ((dualIdx_iff' j.2 l.2).mp h))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem flagGram_mul_apply {K : Type} [CommRing K] {ρ k : ℕ}
    (A : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) (i j : Fin (2 * ρ + k + 1)) :
    (flagGram K (2 * ρ + k + 1) ρ k * A) i j =
      (if i.val = ρ + k then -1 else 1) * A ⟨dualIdx ρ k i.val, dualIdx_lt' i.2⟩ j := by
  rw [mul_apply, Finset.sum_eq_single ⟨dualIdx ρ k i.val, dualIdx_lt' i.2⟩]
  · simp only [flagGram, Fin.val_mk, if_true]
  · intro l _ hl
    simp only [flagGram]
    rw [if_neg, zero_mul]
    intro h
    exact hl (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem flagCond_dual_unipSym : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K,
    (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k →
    FlagCond (fun c : K => c = 0) ρ k 1 (M : Matrix (Fin n) (Fin n) K) →
    FlagCond (fun c : K => c = 0) ρ k 0 (M' : Matrix (Fin n) (Fin n) K) → M ∈ unipSym K n ρ k := by
  intro K _ n ρ k hn M M' hrel hM hM'
  subst hn

  have hkey : (M' : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K)ᵀ * flagGram K (2 * ρ + k + 1) ρ k =
      flagGram K (2 * ρ + k + 1) ρ k * ((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) := by
    have h := congrArg (· * ((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K)) hrel
    simp only [Matrix.mul_assoc] at h
    rw [← h, Units.mul_inv, Matrix.mul_one]

  have hN : ∀ p q : Fin (2 * ρ + k + 1), ρ + k < p.val → q.val ≤ p.val →
      ((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q := by
    intro p q hp hq
    have hp2 := p.2
    have hq2 := q.2
    have h1 := congrFun (congrFun hkey ⟨dualIdx ρ k p.val, dualIdx_lt' p.2⟩) q
    rw [mul_flagGram_apply, flagGram_mul_apply, transpose_apply] at h1
    have e1 : (⟨dualIdx ρ k (dualIdx ρ k p.val), dualIdx_lt' (dualIdx_lt' p.2)⟩ : Fin (2 * ρ + k + 1)) = p :=
      Fin.ext ((dualIdx_iff' p.2 (dualIdx_lt' p.2)).mpr rfl).symm
    have hs : (if dualIdx ρ k p.val = ρ + k then (-1 : K) else 1) = 1 :=
      if_neg (by unfold dualIdx; split_ifs <;> omega)
    simp only [Fin.val_mk] at h1
    rw [e1, hs, one_mul] at h1
    have hc := hM'.1 ⟨dualIdx ρ k q.val, dualIdx_lt' q.2⟩ ⟨dualIdx ρ k p.val, dualIdx_lt' p.2⟩
      (by simp only [Fin.val_mk]; unfold dualIdx; split_ifs <;> omega)
      (by simp only [Fin.val_mk]; unfold dualIdx; split_ifs <;> omega)
    simp only [Matrix.sub_apply, sub_eq_zero] at hc
    rw [← h1, hc]
    by_cases hpq : p = q
    · subst hpq
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, hs, one_mul]
    · have hne : (⟨dualIdx ρ k q.val, dualIdx_lt' q.2⟩ : Fin (2 * ρ + k + 1)) ≠ ⟨dualIdx ρ k p.val, dualIdx_lt' p.2⟩ := by
        intro h
        apply hpq
        have h' := congrArg Fin.val h
        simp only [Fin.val_mk] at h'
        apply Fin.ext
        unfold dualIdx at h'
        split_ifs at h' <;> omega
      rw [Matrix.one_apply_ne hne, zero_mul, Matrix.one_apply_ne hpq]

  have hMrow : ∀ t, ∀ p q : Fin (2 * ρ + k + 1), p.val + t = 2 * ρ + k → ρ + k < p.val → q.val ≤ p.val →
      (M : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro p q ht hp hq
      have hNM : (((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) * (M : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K)) p q = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q := by
        rw [Units.inv_mul]
      rw [mul_apply, Finset.sum_eq_single p] at hNM
      · rw [hN p p hp le_rfl, Matrix.one_apply_eq, one_mul] at hNM
        exact hNM
      · intro l _ hl
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hl) with h | h
        · rw [hN p l hp (le_of_lt h), Matrix.one_apply_ne (fun e => hl (e.symm)), zero_mul]
        · have hl2 := l.2
          rw [ih (2 * ρ + k - l.val) (by omega) l q (by omega) (by omega) (by omega),
            Matrix.one_apply_ne (fun e => by rw [e] at h; omega), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hall : ∀ i j : Fin (2 * ρ + k + 1), j.val ≤ i.val → (M : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) i j = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) i j := by
    intro i j hji
    have hi2 := i.2
    by_cases h1 : j.val < ρ
    · have h := hM.1 i j h1 hji
      simp only [Matrix.sub_apply, sub_eq_zero] at h
      exact h
    by_cases h2 : j.val < ρ + k
    · have h := hM.2.2 i j (by omega) h2 hji
      simp only [Matrix.sub_apply, one_mul, sub_eq_zero] at h
      exact h
    by_cases h3 : j.val = ρ + k
    · have h := hM.2.1 i j h3 (by omega)
      simp only [Matrix.sub_apply, sub_eq_zero] at h
      exact h
    · exact hMrow (2 * ρ + k - i.val) i j (by omega) (by omega) hji
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
  · have hij' : j.val < i.val := hij
    rw [hall i j (le_of_lt hij'), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
  · rw [hall i i le_rfl, Matrix.one_apply_eq]
  · have h := hM.2.1 i j h2 h0
    simp only [Matrix.sub_apply, sub_eq_zero] at h
    rw [h, Matrix.one_apply_ne (fun e => by rw [e] at h1; omega)]

end GlobalTheory.FlagCase
end

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricUnipotent_mem_of_flagCongruence_dual : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → FlagCond (fun c : K => c = 0) ρ k 1 (M : Matrix (Fin n) (Fin n) K) → FlagCond (fun c : K => c = 0) ρ k 0 (M' : Matrix (Fin n) (Fin n) K) → M ∈ unipSym K n ρ k := by
  atlas_forward_decl GlobalTheory.FlagCase.flagCond_dual_unipSym
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RootSumDual

theorem dualIdx_lt {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : ℕ) (hi : i < n) : dualIdx ρ k i < n := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_invol {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : ℕ) (hi : i < n) :
    dualIdx ρ k (dualIdx ρ k i) = i := by
  unfold dualIdx; split_ifs <;> omega

def tau {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (fun i => ⟨dualIdx ρ k i.val, dualIdx_lt hn i.val i.2⟩)
    (fun i => Fin.ext (dualIdx_invol hn i.val i.2))

theorem tau_val {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) : (tau hn i).val = dualIdx ρ k i.val := rfl

theorem tau_tau {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) : tau hn (tau hn i) = i :=
  Fin.ext (dualIdx_invol hn i.val i.2)

def sgn (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : K := if i.val = ρ + k then -1 else 1

theorem sgn_tau (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) :
    sgn K ρ k (tau hn i) = sgn K ρ k i := by
  unfold sgn; rw [tau_val]; unfold dualIdx; split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : sgn K ρ k i * sgn K ρ k i = 1 := by
  unfold sgn; split_ifs <;> simp

theorem flagGram_apply (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    flagGram K n ρ k i j = if j = tau hn i then sgn K ρ k i else 0 := by
  unfold flagGram sgn; simp only [Fin.ext_iff, tau_val]

theorem flagGram_mul (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (X : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) : (flagGram K n ρ k * X) i j = sgn K ρ k i * X (tau hn i) j := by
  rw [mul_apply]; simp only [flagGram_apply K hn, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mul_flagGram (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (X : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) : (X * flagGram K n ρ k) i j = X i (tau hn j) * sgn K ρ k j := by
  rw [mul_apply]
  have e : ∀ b : Fin n, (j = tau hn b) ↔ (b = tau hn j) := fun b =>
    ⟨fun h => by rw [h, tau_tau], fun h => by rw [h, tau_tau]⟩
  simp only [flagGram_apply K hn, e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, sgn_tau]

theorem flagGram_mul_self (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) :
    flagGram K n ρ k * flagGram K n ρ k = 1 := by
  ext i j
  rw [flagGram_mul K hn, flagGram_apply K hn, tau_tau, one_apply, sgn_tau]
  split_ifs with h h' h'
  · exact sgn_mul_self K ρ k i
  · exact absurd h.symm h'
  · exact absurd h'.symm h
  · exact mul_zero _

end GlobalTheory.RootSumDual

namespace GlobalTheory.RootSumDual

theorem inv_adj {K : Type} [CommRing K] {n ρ k : ℕ} {M : GL (Fin n) K} (hM : M ∈ unipSym K n ρ k) (i j : Fin n)
    (hij : j.val = i.val + 1) :
    ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = - (M : Matrix (Fin n) (Fin n) K) i j := by
  have h1 : M ∈ unip K n := hM.1
  have h := unip_mul_entry ((unip K n).inv_mem h1) h1 (show i < j by show i.val < j.val; omega)
    (fun l hil hlj => by
      have a : i.val < l.val := hil
      have b : l.val < j.val := hlj
      omega)
  rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (by intro e; rw [e] at hij; omega)] at h
  linear_combination -h

theorem dual_entry {K : Type} [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (M M' : GL (Fin n) K)
    (h : (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k)
    (i j : Fin n) :
    (M' : Matrix (Fin n) (Fin n) K) (tau hn j) (tau hn i) =
      sgn K ρ k i * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j * sgn K ρ k j := by
  set G := flagGram K n ρ k
  set Mi := ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hMM : (M : Matrix (Fin n) (Fin n) K) * Mi = 1 := Units.mul_inv M
  have h2 : (M' : Matrix (Fin n) (Fin n) K)ᵀ * G = G * Mi := by
    conv_rhs => rw [← h, Matrix.mul_assoc _ (M : Matrix (Fin n) (Fin n) K), hMM, Matrix.mul_one]
  have h3 : (M' : Matrix (Fin n) (Fin n) K)ᵀ = G * Mi * G := by
    rw [← h2, Matrix.mul_assoc, flagGram_mul_self K hn, Matrix.mul_one]
  have h4 := congrFun (congrFun h3 (tau hn i)) (tau hn j)
  rw [transpose_apply] at h4
  rw [h4, mul_flagGram K hn, flagGram_mul K hn, tau_tau, tau_tau, sgn_tau, sgn_tau]

theorem sum_reindex {K : Type} [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (f : Fin n → Fin n → K) :
    ∑ i, ∑ j, f i j = ∑ i, ∑ j, f (tau hn j) (tau hn i) := by
  rw [Finset.sum_comm]
  refine (Equiv.sum_comp (tau hn) _).symm.trans (Finset.sum_congr rfl fun x _ => ?_)
  exact (Equiv.sum_comp (tau hn) (fun i => f i (tau hn x))).symm

theorem rootSum_dual_edges : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ ε ε' a₁ a₂ : K, (ε = 1 ∧ ε' = 0) ∨ (ε = 0 ∧ ε' = 1) → a₁ ≠ 0 → a₂ ≠ 0 → ∃ a : Fin n → Fin n → K, (∀ i j, symEdge ρ k i j → a i j ≠ 0) ∧ ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → M ∈ unipSym K n ρ k → a₁ * rootSum ρ k ε (M : Matrix (Fin n) (Fin n) K) + a₂ * rootSum ρ k ε' (M' : Matrix (Fin n) (Fin n) K) = ∑ i, ∑ j, if symEdge ρ k i j then a i j * (M : Matrix (Fin n) (Fin n) K) i j else 0 := by
  intro K _ n ρ k hn ε ε' a₁ a₂ hε ha₁ ha₂
  refine ⟨fun i _ => if i.val < ρ then a₁ else if i.val < ρ + k then ε * a₁ - ε' * a₂
    else if i.val = ρ + k then a₂ else -a₂, ?_, ?_⟩
  · intro i j _
    rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> dsimp only <;> split_ifs <;> simp [ha₁, ha₂]
  · intro M M' h hM
    unfold rootSum
    rw [sum_reindex hn (fun i j => if (i.val + 1 < ρ ∧ j.val = i.val + 1) ∨ (i.val + 1 = ρ ∧ j.val = ρ + k)
      then (M' : Matrix (Fin n) (Fin n) K) i j
      else if ρ ≤ i.val ∧ j.val = i.val + 1 ∧ j.val < ρ + k then ε' * (M' : Matrix (Fin n) (Fin n) K) i j else 0)]
    simp only [dual_entry hn M M' h]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hi := i.2
    have hj := j.2
    have c1 : (((tau hn j).val + 1 < ρ ∧ (tau hn i).val = (tau hn j).val + 1) ∨
        ((tau hn j).val + 1 = ρ ∧ (tau hn i).val = ρ + k)) ↔ (j.val = i.val + 1 ∧ ρ + k ≤ i.val) := by
      simp only [tau_val]; unfold dualIdx; split_ifs <;> omega
    have c2 : (ρ ≤ (tau hn j).val ∧ (tau hn i).val = (tau hn j).val + 1 ∧ (tau hn i).val < ρ + k) ↔
        (ρ ≤ i.val ∧ j.val = i.val + 1 ∧ j.val < ρ + k) := by
      simp only [tau_val]; unfold dualIdx; split_ifs <;> omega
    have c3 : symEdge ρ k i j ↔ ((j.val = i.val + 1 ∧ i.val + 1 ≠ ρ ∧ i.val + 1 ≠ ρ + k) ∨
        (i.val + 1 = ρ ∧ j.val = ρ + k)) := Iff.rfl
    simp only [c1, c2, c3]
    by_cases hij : j.val = i.val + 1
    · rw [inv_adj hM i j hij]
      unfold sgn
      split_ifs <;> first | (exfalso; omega) | ring1
    · split_ifs <;> first | (exfalso; omega) | ring1

end GlobalTheory.RootSumDual

end
end

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRootSum_dual_eq_symmetricEdge_sum : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ ε ε' a₁ a₂ : K, (ε = 1 ∧ ε' = 0) ∨ (ε = 0 ∧ ε' = 1) → a₁ ≠ 0 → a₂ ≠ 0 → ∃ a : Fin n → Fin n → K, (∀ i j, symEdge ρ k i j → a i j ≠ 0) ∧ ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → M ∈ unipSym K n ρ k → a₁ * rootSum ρ k ε (M : Matrix (Fin n) (Fin n) K) + a₂ * rootSum ρ k ε' (M' : Matrix (Fin n) (Fin n) K) = ∑ i, ∑ j, if symEdge ρ k i j then a i j * (M : Matrix (Fin n) (Fin n) K) i j else 0 := by
  atlas_forward_decl GlobalTheory.RootSumDual.rootSum_dual_edges
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoverConj

theorem isConjugatePlace_conjugateIdealPlace (D : D7) (P : Pl D.host.E) : Formalism.L2.DIV.IsConjPl P (Formalism.DivisionValues.conjPl P) := by
  intro a b hab
  have hb : b = Formalism.DivisionValues.cO D.host.E a := RingOfIntegers.ext (by rw [hab]; rfl)
  subst hb
  show a ∈ P.asIdeal ↔ Formalism.DivisionValues.cO D.host.E a ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)
  constructor
  · exact fun h => Ideal.mem_map_of_mem _ h
  · intro h
    rw [Ideal.mem_map_of_equiv] at h
    obtain ⟨x, hx, hxa⟩ := h
    rwa [← (Formalism.DivisionValues.cO D.host.E).injective hxa]

theorem cover : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (resS D.host.F Q s = 0 ↔ resS D.host.F PP (sigInt (instOf D) s) = 0) := by
  intro D Pg hPg Q hQ
  have hv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal
    rw [map_natCast]
    exact hQ
  obtain ⟨PP, ⟨hPP, hunder⟩, -⟩ := hPg.2 _ hv
  refine ⟨PP, hPP, ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hunder.symm with h | h
  · exact Or.inl h
  · right
    intro s
    have hc : Formalism.L2.DIV.IsConjPl PP Q := h ▸ isConjugatePlace_conjugateIdealPlace D PP
    exact (Formalism.L2.DIV.resS_sigS_eq_zero_iff (instOf D).cm hc.symm s).symm

end GlobalTheory.CoverConj
end

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimePlace_mem_or_conj_genusTypePlaceSet : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (resS D.host.F Q s = 0 ↔ resS D.host.F PP (sigInt (instOf D) s) = 0) := by
  atlas_forward_decl GlobalTheory.CoverConj.cover
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagFrameWeights

theorem isUnit_res {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) (x : Formalism.L2.DIV.kP PP) (hx : x ≠ 0) :
    IsUnit x := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (Formalism.L2.DIV.kP PP) := Ideal.Quotient.field PP.asIdeal
  exact isUnit_iff_ne_zero.mpr hx

set_option maxHeartbeats 1000000 in

theorem exists_diag_frame : ∀ {D : D7} {n : ℕ} (ρ k : ℕ) (Pg : Finset (Pl D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β₀ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)), Formalism.L2.DIV.IsFrame β₀ Λ → ∀ a : ∀ PP : Pl D.host.E, Fin n → Fin n → kP PP, (∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → a PP i j ≠ 0) → ∃ β₃ : GL (Fin n) (Formalism.IndefR.Lev.EAf D), Formalism.L2.DIV.IsFrame β₃ Λ ∧ Formalism.L2.DIV.St β₃ = Formalism.L2.DIV.St β₀ ∧ ∀ PP ∈ Pg, ∀ y ∈ Formalism.L2.DIV.St β₀, (Formalism.L2.DIV.redFn β₃ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k ↔ Formalism.L2.DIV.redFn β₀ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k) ∧ (∑ i, ∑ j, if Formalism.L2.DIV.symEdge ρ k i j then a PP i j * ((Formalism.L2.DIV.redFn β₀ PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j else 0) = Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge ρ k) (Formalism.L2.DIV.redFn β₃ PP y) := by
  intro D n ρ k Pg Λ β₀ hβ a ha
  classical
  let w : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → Fin n → (Formalism.L2.DIV.kP PP)ˣ := fun PP i j =>
    if h : PP ∈ Pg ∧ Formalism.L2.DIV.symEdge ρ k i j then (isUnit_res PP (a PP i j) (ha PP h.1 i j h.2)).unit else 1
  let d : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → (Formalism.L2.DIV.kP PP)ˣ := fun PP =>
    GlobalTheory.SeeConjScale.forestLift (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k) (w PP)
  have hd : ∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → (((d PP i)⁻¹ : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP) * (d PP j : Formalism.L2.DIV.kP PP) = a PP i j := by
    intro PP hPP i j h
    have e := congrArg Units.val (GlobalTheory.SeeConjScale.forestLift_edge (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k)
      (GlobalTheory.SeeConjScale.symEdge_uniq ρ k) (w PP) h)
    rw [Units.val_mul] at e
    rw [e]
    simp only [w, dif_pos (And.intro hPP h), IsUnit.unit_spec]
  choose u hu using fun j : Fin n => GlobalTheory.FrameRescale.exists_unit_res (D := D) Pg (fun PP => d PP j)
  have hSt : ∀ M, M ∈ Formalism.L2.DIV.St (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ↔ M ∈ Formalism.L2.DIV.St β₀ := by
    intro M
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨GlobalTheory.SeeConjRead.diagGL u * y * (GlobalTheory.SeeConjRead.diagGL u)⁻¹, (GlobalTheory.FrameRescale.frGL_mul β₀ (GlobalTheory.SeeConjRead.diagGL u) y).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨(GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u, ?_⟩
      rw [GlobalTheory.FrameRescale.frGL_mul]
      congr 1
      group
  have hred : ∀ PP ∈ Pg, ∀ M ∈ Formalism.L2.DIV.St β₀,
      Formalism.L2.DIV.redFn (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP M =
        (GlobalTheory.SeeConjRead.diagGL (d PP))⁻¹ * Formalism.L2.DIV.redFn β₀ PP M * GlobalTheory.SeeConjRead.diagGL (d PP) := by
    intro PP hPP M hM
    obtain ⟨y, rfl⟩ := hM
    have e1 : Formalism.L2.DIV.frGL β₀ y =
        Formalism.L2.DIV.frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u) := by
      rw [GlobalTheory.FrameRescale.frGL_mul]
      congr 1
      group
    have hb : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (GlobalTheory.SeeConjRead.diagGL u) = GlobalTheory.SeeConjRead.diagGL (d PP) := by
      apply Units.ext
      ext i j
      show Formalism.L2.DIV.resS D.host.F PP (((GlobalTheory.SeeConjRead.diagGL u : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j) =
        ((GlobalTheory.SeeConjRead.diagGL (d PP) : GL (Fin n) (Formalism.L2.DIV.kP PP)) : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.kP PP)) i j
      rw [GlobalTheory.SeeConjRead.diagGL_val, GlobalTheory.SeeConjRead.diagGL_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs with h
      · subst h
        exact hu i PP hPP
      · exact map_zero _
    have e3 := Formalism.L2.DIV.redFn_frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u)
    have e4 := Formalism.L2.DIV.redFn_frGL β₀ PP y
    rw [← e1] at e3
    rw [e3, e4, GlobalTheory.FrameRescale.bc_conj, hb]
  refine ⟨β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u), ?_, ?_, ?_⟩
  · intro x
    rw [hβ x]
    have hinv : ((β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u))⁻¹).val = Matrix.diagonal (fun i => ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D)) *
          (β₀⁻¹).val := by
      rw [_root_.mul_inv_rev, Units.val_mul, ← map_inv, GlobalTheory.SeeConjRead.diagGL_inv, GlobalTheory.FrameRescale.intGL_diagGL_val]
    rw [hinv]
    refine forall_congr' fun i => ?_
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    have hm : ((u i : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) * ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) = 1 := congrArg Subtype.val (u i).mul_inv
    constructor
    · intro h
      exact Subring.mul_mem _ ((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ).val.2 h
    · intro h
      have h2 := Subring.mul_mem _ (u i).val.2 h
      rwa [← mul_assoc, hm, one_mul] at h2
  · ext M
    exact hSt M
  · intro PP hPP y hy
    rw [hred PP hPP y hy]
    refine ⟨(GlobalTheory.SeeConjRead.unipSym_conj_iff ρ k (d PP) _).symm, ?_⟩
    unfold Formalism.L2.DIV.edgeSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [GlobalTheory.SeeConjRead.diagGL_conj_apply, ← hd PP hPP i j h]
      ring
    · rfl

end GlobalTheory.DiagFrameWeights
end
end

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonal_frame_change_unweighting_symEdges : ∀ {D : D7} {n : ℕ} (ρ k : ℕ) (Pg : Finset (Pl D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β₀ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)), Formalism.L2.DIV.IsFrame β₀ Λ → ∀ a : ∀ PP : Pl D.host.E, Fin n → Fin n → kP PP, (∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → a PP i j ≠ 0) → ∃ β₃ : GL (Fin n) (Formalism.IndefR.Lev.EAf D), Formalism.L2.DIV.IsFrame β₃ Λ ∧ Formalism.L2.DIV.St β₃ = Formalism.L2.DIV.St β₀ ∧ ∀ PP ∈ Pg, ∀ y ∈ Formalism.L2.DIV.St β₀, (Formalism.L2.DIV.redFn β₃ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k ↔ Formalism.L2.DIV.redFn β₀ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k) ∧ (∑ i, ∑ j, if Formalism.L2.DIV.symEdge ρ k i j then a PP i j * ((Formalism.L2.DIV.redFn β₀ PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j else 0) = Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge ρ k) (Formalism.L2.DIV.redFn β₃ PP y) := by
  atlas_forward_decl GlobalTheory.DiagFrameWeights.exists_diag_frame
end

section
noncomputable section

namespace GlobalTheory.FlagBasis

section Alg
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV
open scoped TensorProduct

theorem flagCond_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (P : B → Prop) (ρ k : ℕ) (ε : A)
    (m : Matrix (Fin n) (Fin n) A) :
    FlagCond P ρ k (f ε) (m.map f) ↔ FlagCond (fun a => P (f a)) ρ k ε m := by
  have e : ∀ i j, (m.map f - 1) i j = f ((m - 1) i j) := fun i j => by
    simp only [Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp
  simp only [FlagCond, e, ← map_mul]

theorem rootSum_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (ρ k : ℕ) (ε : A)
    (m : Matrix (Fin n) (Fin n) A) : rootSum ρ k (f ε) (m.map f) = f (rootSum ρ k ε m) := by
  simp only [rootSum, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem flagGram_transpose (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) :
    (flagGram K n ρ k)ᵀ = flagGram K n ρ k := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [Matrix.transpose_apply, flagGram, dualIdx]
  split_ifs <;> first | rfl | omega

theorem flagCond_of_unipSym {K : Type} [CommRing K] {n ρ k : ℕ} (ε : K) {M : GL (Fin n) K} (hM : M ∈ unipSym K n ρ k) :
    FlagCond (fun c : K => c = 0) ρ k ε (M : Matrix (Fin n) (Fin n) K) := by
  have low : ∀ i j : Fin n, j.val ≤ i.val → ((M : Matrix (Fin n) (Fin n) K) - 1) i j = 0 := by
    intro i j h
    rcases eq_or_lt_of_le h with h | h
    · obtain rfl : j = i := Fin.ext h
      simp [unip_diag hM.1]
    · rw [Matrix.sub_apply, unip_lower hM.1 (show j < i from h), Matrix.one_apply_ne (ne_of_gt (show j < i from h)), sub_zero]
  refine ⟨fun i j _ h => low i j h, fun i j hj hi => ?_, fun i j _ _ h => by rw [low i j h, mul_zero]⟩
  by_cases h : j.val ≤ i.val
  · exact low i j h
  · rw [Matrix.sub_apply, hM.2 i j hi (by omega) hj, Matrix.one_apply_ne (fun e => h (by rw [e])), sub_zero]

theorem flagCond_iff_unipSym {K : Type} [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) {ε ε' : K}
    (hε : (ε = 1 ∧ ε' = 0) ∨ (ε = 0 ∧ ε' = 1)) (M M' : GL (Fin n) K)
    (h : (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k) :
    FlagCond (fun c : K => c = 0) ρ k ε (M : Matrix (Fin n) (Fin n) K) ∧
      FlagCond (fun c : K => c = 0) ρ k ε' (M' : Matrix (Fin n) (Fin n) K) ↔ M ∈ unipSym K n ρ k := by
  have h' : (M : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M' : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k := by
    have := congrArg Matrix.transpose h
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, flagGram_transpose K hn,
      ← Matrix.mul_assoc] at this
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun hM => ⟨flagCond_of_unipSym _ hM, flagCond_of_unipSym _ (GlobalTheory.T.symmetricUnipotent_mem_of_flagBasisDual K n ρ k hn M M' h hM)⟩⟩
  rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact GlobalTheory.T.symmetricUnipotent_mem_of_flagCongruence_dual K n ρ k hn M M' h h1 h2
  · exact GlobalTheory.T.symmetricUnipotent_mem_of_flagBasisDual K n ρ k hn M' M h' (GlobalTheory.T.symmetricUnipotent_mem_of_flagCongruence_dual K n ρ k hn M' M h' h2 h1)

theorem map_eq_zero_of_zmod (I : AutInst) {g : ℕ} {K : Type} [CommRing K] (p : Formalism.L2.Herm.intAf I.F I.E →+* K)
    (hg : (g : K) = 0) {s : Formalism.L2.Herm.intAf I.F I.E} (hs : ZMod' I g s) : p s = 0 := by
  obtain ⟨t, ht, e⟩ := hs
  have : s = (g : Formalism.L2.Herm.intAf I.F I.E) * ⟨t, ht⟩ := Subtype.ext (by simpa using e)
  rw [this, map_mul, map_natCast, hg, zero_mul]

theorem kset_iff (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hβ : IsFrame β I.L) (x : I.Gf) :
    x ∈ I.Kset ↔ (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β := by
  have e : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
    show Submodule.span _ _ = Submodule.span _ _
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
  rw [GlobalTheory.LevSplit.mem_St_iff β I.L hβ, e]
  refine ⟨fun h => ⟨fun y hy => Formalism.L2.SG.Pf.unitaryCongruence.K_mv I h hy,
    fun y hy => Formalism.L2.SG.Pf.unitaryCongruence.K_mv I (Formalism.L2.SG.Pf.unitaryCongruence.K_inv I h) hy⟩, fun h y => ⟨h.1 y, fun hy => ?_⟩⟩
  have := h.2 _ hy
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem read_in_frame (I : AutInst) (g : ℕ) (hg : g ≠ 0) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)
    (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (hF : IsRefFrame I g e0 f0 z0 bw bwd ew) (hn : I.n = 2 * ρ + k + 1)
    (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (hβ : IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β)
    (Pg : Finset (Pl I.E)) (hdiv : ∀ PP ∈ Pg, (g : 𝓞 I.E) ∈ PP.asIdeal)
    (hN : ∀ s : Formalism.L2.Herm.intAf I.F I.E,
      (∀ PP ∈ Pg, resS I.F PP s = 0 ∧ resS I.F PP (sigInt I s) = 0) → ZMod' I g s)
    (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ) (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
    (ψ0 : ∀ PP : Pl I.E, AddChar (kP PP) ℂ) (a₁ a₂ : ∀ PP : Pl I.E, kP PP) (ha : ∀ PP ∈ Pg, a₁ PP ≠ 0 ∧ a₂ PP ≠ 0)
    (hχ : ∀ s : Formalism.L2.Herm.intAf I.F I.E, star (psiEf (divN I g s.1)) =
      ∏ PP ∈ Pg, ψ0 PP (a₁ PP * resS I.F PP s + a₂ PP * resS I.F PP (sigInt I s))) :
    ∃ a : ∀ PP : Pl I.E, Fin I.n → Fin I.n → kP PP, (∀ PP ∈ Pg, ∀ i j, symEdge ρ k i j → a PP i j ≠ 0) ∧
      ∀ x : I.Gf, (x ∈ K2set I g e0 z0 bw ↔ (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β ∧
          ∀ PP ∈ Pg, redFn β PP x ∈ unipSym (kP PP) I.n ρ k) ∧
        (x ∈ K2set I g e0 z0 bw → star (chi2f I psiEf g e0 f0 z0 bw bwd x) =
          ∏ PP ∈ Pg, ψ0 PP (∑ i, ∑ j, if symEdge ρ k i j then
            a PP i j * ((redFn β PP x : GL (Fin I.n) (kP PP)) : Matrix (Fin I.n) (Fin I.n) (kP PP)) i j else 0)) := by
  classical
  obtain ⟨hew, hG⟩ := GlobalTheory.T.liftFrame_gram_congr_flagGram I g e0 f0 z0 bw bwd ew hF hn β hβ
  have hpg : ∀ PP ∈ Pg, (g : kP PP) = 0 := fun PP hPP => by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hdiv PP hPP)
  let ewS : Formalism.L2.Herm.intAf I.F I.E := ⟨ew, hF.2.2.2.2.1.2.2.1⟩
  let p' : ∀ PP : Pl I.E, Formalism.L2.Herm.intAf I.F I.E →+* kP PP := fun PP => (resS I.F PP).comp (sigInt I)
  have hε : ∀ PP ∈ Pg, (resS I.F PP ewS = 1 ∧ p' PP ewS = 0) ∨ (resS I.F PP ewS = 0 ∧ p' PP ewS = 1) := by
    intro PP hPP
    have h1 : resS I.F PP (1 - ewS - sigInt I ewS) = 0 := map_eq_zero_of_zmod I _ (hpg PP hPP) hew
    have h2 : ewS * sigInt I ewS = 0 := Subtype.ext hF.2.2.2.2.1.2.1
    have h3 : resS I.F PP ewS * p' PP ewS = 0 := by
      show _ * resS I.F PP (sigInt I ewS) = 0
      rw [← map_mul, h2, map_zero]
    rw [map_sub, map_sub, map_one] at h1
    have h1' : 1 - resS I.F PP ewS - p' PP ewS = 0 := h1
    haveI := PP.isPrime
    rcases mul_eq_zero.1 h3 with h | h
    · exact Or.inr ⟨h, by rw [h] at h1'; linear_combination -h1'⟩
    · exact Or.inl ⟨by rw [h] at h1'; linear_combination -h1', h⟩
  have hZ : ∀ s : Formalism.L2.Herm.intAf I.F I.E, ZMod' I g s ↔ ∀ PP ∈ Pg, resS I.F PP s = 0 ∧ p' PP s = 0 :=
    fun s => ⟨fun h PP hPP => ⟨map_eq_zero_of_zmod I _ (hpg PP hPP) h, map_eq_zero_of_zmod I _ (hpg PP hPP) h⟩, hN s⟩
  have hroot := fun (PP : Pl I.E) (hPP : PP ∈ Pg) => GlobalTheory.T.flagRootSum_dual_eq_symmetricEdge_sum (kP PP) I.n ρ k hn _ _ (a₁ PP) (a₂ PP) (hε PP hPP)
    (ha PP hPP).1 (ha PP hPP).2
  choose! a ha1 ha2 using hroot
  have hmat : ∀ (x : I.Gf) (m : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)),
      frGL β m = (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) →
      matIn I β x = (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (Formalism.L2.Herm.intAf I.F I.E).subtype := by
    intro x m hm
    unfold matIn
    rw [← hm]
    have : β⁻¹ * frGL β m * β = intGL I.F I.E I.n m := by
      simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    rfl
  have hrel := fun (x : I.Gf) m hm (PP : Pl I.E) (hPP : PP ∈ Pg) =>
    GlobalTheory.T.unitary_liftedFlagBasis_reduce_mod_level I g ρ k β hG (kP PP) (resS I.F PP) (hpg PP hPP) x m hm
  have main : ∀ x : I.Gf, x ∈ K2set I g e0 z0 bw ↔ (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β ∧
      ∀ PP ∈ Pg, redFn β PP x ∈ unipSym (kP PP) I.n ρ k := by
    intro x
    show x ∈ I.Kset ∧ _ ↔ _
    rw [kset_iff I hβ.1]
    refine and_congr_right fun hS => ?_
    rw [GlobalTheory.T.levelCongruence_iff_flag_conditions I g e0 f0 z0 bw bwd ew hF hn β hβ x hS]
    obtain ⟨m, hm⟩ := hS
    rw [hmat x m hm, ← hm]
    refine (flagCond_map (Formalism.L2.Herm.intAf I.F I.E).subtype (ZMod' I g) ρ k ewS _).trans ?_
    have e : ∀ PP ∈ Pg, (redFn β PP (frGL β m) ∈ unipSym (kP PP) I.n ρ k ↔
        FlagCond (fun s => resS I.F PP s = 0) ρ k ewS m.1 ∧ FlagCond (fun s => p' PP s = 0) ρ k ewS m.1) := by
      intro PP hPP
      rw [redFn_frGL, ← flagCond_iff_unipSym hn (hε PP hPP) (Formalism.UG.bc (resS I.F PP) m) (Formalism.UG.bc (p' PP) m) (hrel x m hm PP hPP)]
      exact and_congr (flagCond_map (resS I.F PP) (fun c => c = 0) ρ k ewS m.1) (flagCond_map (p' PP) (fun c => c = 0) ρ k ewS m.1)
    rw [forall₂_congr e]
    constructor
    · rintro ⟨h1, h2, h3⟩ PP hPP
      exact ⟨⟨fun i j a b => ((hZ _).1 (h1 i j a b) PP hPP).1, fun i j a b => ((hZ _).1 (h2 i j a b) PP hPP).1,
          fun i j a b c => ((hZ _).1 (h3 i j a b c) PP hPP).1⟩,
        ⟨fun i j a b => ((hZ _).1 (h1 i j a b) PP hPP).2, fun i j a b => ((hZ _).1 (h2 i j a b) PP hPP).2,
          fun i j a b c => ((hZ _).1 (h3 i j a b c) PP hPP).2⟩⟩
    · intro h
      exact ⟨fun i j a b => (hZ _).2 fun PP hPP => ⟨(h PP hPP).1.1 i j a b, (h PP hPP).2.1 i j a b⟩,
        fun i j a b => (hZ _).2 fun PP hPP => ⟨(h PP hPP).1.2.1 i j a b, (h PP hPP).2.2.1 i j a b⟩,
        fun i j a b c => (hZ _).2 fun PP hPP => ⟨(h PP hPP).1.2.2 i j a b c, (h PP hPP).2.2.2 i j a b c⟩⟩
  refine ⟨a, ha1, fun x => ⟨main x, fun hx => ?_⟩⟩
  obtain ⟨hS, hU⟩ := (main x).1 hx
  have hc := GlobalTheory.T.characterArgument_congr_rootEntrySum_mod I g e0 f0 z0 bw bwd ew hF hn β hβ hG x hS
  obtain ⟨m, hm⟩ := hS
  rw [hmat x m hm] at hc
  have hr := rootSum_map (Formalism.L2.Herm.intAf I.F I.E).subtype ρ k ewS m.1
  have hc' : ZMod' I g (chiArg I e0 f0 z0 bw bwd x - (rootSum ρ k ewS m.1).1) := by
    have hr' : rootSum ρ k ew (m.1.map (Formalism.L2.Herm.intAf I.F I.E).subtype) = (rootSum ρ k ewS m.1).1 := hr
    rwa [hr'] at hc
  have e1 : chi2f I psiEf g e0 f0 z0 bw bwd x = psiEf (divN I g (rootSum ρ k ewS m.1).1) := by
    obtain ⟨t, ht, e⟩ := hc'
    rw [flagLevelCharacter_eq_psi_divN, eq_add_of_sub_eq e, Formalism.L2.SG.Pf.unitaryCongruence.divN_add, hadd, Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg, hint t ht, one_mul]
  rw [e1, hχ]
  refine Finset.prod_congr rfl fun PP hPP => congrArg _ ?_
  have hU' := hU PP hPP
  rw [← hm, redFn_frGL] at hU' ⊢
  rw [← ha2 PP hPP (Formalism.UG.bc (resS I.F PP) m) (Formalism.UG.bc (p' PP) m) (hrel x m hm PP hPP) hU']
  exact congrArg₂ (· + ·) (congrArg _ (rootSum_map (resS I.F PP) ρ k ewS m.1).symm)
    (congrArg _ (rootSum_map (p' PP) ρ k ewS m.1).symm)

end Alg

end GlobalTheory.FlagBasis

section Host
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FlagBasis.read_inst (D : D7) (e0 f0 : Fin D.R.rS → VA (instOf D)) (z0 : VA (instOf D))
    (bw bwd : Fin D.R.k → VA (instOf D)) (ew : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F)
    (hF : IsRefFrame (instOf D) (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd ew) (hn : (instOf D).n = D.R.r)
    (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ) (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1)
    (hrat : ∀ x : (instOf D).E,
      psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1)
    (Pg : Finset (Pl D.host.E)) (hPg : GlobalTheory.Core.Mi.IsTypePlaces Pg)
    (hnc : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP')
    (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (hψ : IsGenericPsi Pg ψ0) :
    ∃ β : GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D),
      IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0) ∧
      ∀ x : (instOf D).Gf, (x ∈ K2set (instOf D) (D.host.g 0 * D.host.g 1) e0 z0 bw ↔
          (x.1 : GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) ∈ St β ∧
          ∀ PP ∈ Pg, redFn β PP x.1 ∈ unipSym (kP PP) (D.sp.Y 0).rank D.R.rS D.R.k) ∧
        (x ∈ K2set (instOf D) (D.host.g 0 * D.host.g 1) e0 z0 bw →
          star (chi2f (instOf D) psiEf (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd x) =
          ∏ PP ∈ Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (redFn β PP x.1))) := by
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hn' : (instOf D).n = 2 * D.R.rS + D.R.k + 1 := by
    rw [hn]
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.flagVec_mem_Lf_and_inMod (instOf D) _ e0 f0 z0 bw bwd ew hF hn'
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.T.exists_latticeFrame_lifting_spanning_vectors_mod D _ hg _ hs1 hs2
  have hN : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (∀ PP ∈ Pg, resS D.host.F PP s = 0 ∧ resS D.host.F PP (sigInt (instOf D) s) = 0) →
      ZMod' (instOf D) (D.host.g 0 * D.host.g 1) s.1 := by
    intro s hs
    refine GlobalTheory.T.integralAdele_congr_zero_of_residues_squarefree (instOf D) _ hg (GlobalTheory.T.typePrimes_product_not_mem_sq_place D) s fun Q hQ => ?_
    obtain ⟨PP, hPP, rfl | h⟩ := GlobalTheory.T.typePrimePlace_mem_or_conj_genusTypePlaceSet D Pg hPg Q hQ
    · exact (hs _ hPP).1
    · exact (h s).2 (hs _ hPP).2
  obtain ⟨a₁, a₂, ha, hχ⟩ := GlobalTheory.T.character_residueFields_eq_prod_genericShift D.host.E (Formalism.L2.Herm.intAf D.host.F D.host.E) Pg (fun PP => resS D.host.F PP)
    (fun PP => (resS D.host.F PP).comp (sigInt (instOf D)))
    (fun s => star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1))) ψ0 hψ
    (fun s t => (congrArg (fun z => star (psiEf z))
        (Formalism.L2.SG.Pf.unitaryCongruence.divN_add (instOf D) (D.host.g 0 * D.host.g 1) s.1 t.1)).trans (by rw [hadd, star_mul']))
    (fun s hs => by
      obtain ⟨t, ht, e⟩ := hN s hs
      have : divN (instOf D) (D.host.g 0 * D.host.g 1) s.1 = t :=
        (congrArg _ e).trans (Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg t)
      show star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) = 1
      rw [this, hint t ht, star_one])
    (GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj D Pg hnc)
    (GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position D Pg hPg.1 hnc (fun s => star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) ≠ 1) fun Q hQ => by
      obtain ⟨s, h1, h2⟩ := GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime D psiEf hadd hint hrat Q hQ
      exact ⟨s, h1, fun h => h2 (by simpa using congrArg star h)⟩)
  obtain ⟨a, ha1, hK⟩ := read_in_frame (instOf D) _ hg e0 f0 z0 bw bwd ew hF hn' β₀ hβ₀ Pg hPg.1 hN psiEf hadd hint ψ0 a₁ a₂ ha hχ
  have hL : (instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 := Lv_eq_map D
  obtain ⟨β, hβ, hSt, hred⟩ := GlobalTheory.T.exists_diagonal_frame_change_unweighting_symEdges (D := D) (n := (D.sp.Y 0).rank) D.R.rS D.R.k Pg _ β₀ hβ₀.1 a ha1
  refine ⟨β, hL ▸ hβ, fun x => ⟨?_, fun hx => ?_⟩⟩
  · rw [hSt]
    exact (hK x).1.trans (and_congr_right fun hS => forall₂_congr fun PP hPP => (hred PP hPP _ hS).1.symm)
  · exact ((hK x).2 hx).trans
      (Finset.prod_congr rfl fun PP hPP => congrArg _ (hred PP hPP _ ((hK x).1.1 hx).1).2)

end Host

section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeConjRead

open Formalism.L2.DIV

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (hr : n ≤ n) (g : GL (Fin n) κ) : upperLeftBlock hr g = g := by
  have hg : g ∈ blockTri (κ := κ) (blk2 n) := fun i j h => by
    simp [blk2, i.2, j.2] at h
  apply Units.ext
  rw [upper_block_val_submatrix hr hg]
  ext i j
  simp

theorem blockTri_blkOf_top {κ : Type} [CommRing κ] {n r : ℕ} (t : ℕ) (hn : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ blockTri (κ := κ) (blkOf r t) := fun i j h => by
  have hi : i.val < r := lt_of_lt_of_le i.2 hn
  have hj : j.val < r := lt_of_lt_of_le j.2 hn
  simp [blkOf, hi, hj] at h

theorem iotaX_fst_eq_one_iff {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (κ : GA D (D.sp.Y 0)) : (iotaX X h κ).1 = 1 ↔ κ ∈ GfC (D.sp.Y 0) := by
  have key : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
      (y : (Formalism.L2.SG.InstExistsPf.instOf D).GA), ((castGA hI.symm) y).1 = 1 ↔ y.1 = 1 := by
    intro I hI y
    subst hI
    exact Iff.rfl
  show ((castGA h.symm) (Formalism.IndefR.RationalEmbedding.iota D κ)).1 = 1 ↔ _
  rw [key X.B.I h, ← Formalism.L2.SG.EvalTIota.brg_mem_GfC_i, ContinuousMulEquiv.symm_apply_apply]

theorem eq_symm_one {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (κ : GA D (D.sp.Y 0)) (h1 : (iotaX X h κ).1 = 1) : (iotaX X h).symm (1, (iotaX X h κ).2) = κ := by
  rw [ContinuousMulEquiv.symm_apply_eq]
  exact Prod.ext h1.symm rfl

end GlobalTheory.SeeConjRead

theorem GlobalTheory.SeeConjRead.read_fin {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (Pg : Finset (Pl D.host.E)) (hPg : GlobalTheory.Core.Mi.IsTypePlaces Pg)
    (hnc : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP')
    (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (hψ : IsGenericPsi Pg ψ0) :
    ∃ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D),
      Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0) ∧
      ∀ κ : GA D (D.sp.Y 0), ((iotaX X h κ).2 ∈ X.K2 ↔ Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β ∧
          ∀ PP ∈ Pg, redFn β PP (Lev.finE (D.sp.Y 0) κ) ∈ unipSym (kP PP) (D.sp.Y 0).rank D.R.rS D.R.k) ∧
        ((iotaX X h κ).2 ∈ X.K2 → star (X.chi2 (iotaX X h κ).2) =
          ∏ PP ∈ Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (redFn β PP (Lev.finE (D.sp.Y 0) κ)))) := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (g : ℕ) (_ : g = D.host.g 0 * D.host.g 1)
      (e0 f0 : Fin D.R.rS → VA I) (z0 : VA I) (bw bwd : Fin D.R.k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
      (_ : GlobalTheory.FlagBasis.IsRefFrame I g e0 f0 z0 bw bwd ew) (_ : I.n = D.R.r) (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ)
      (_ : ∀ x y, psiEf (x + y) = psiEf x * psiEf y) (_ : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
      (_ : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1),
      ∃ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D),
      Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0) ∧
      ∀ κ : GA D (D.sp.Y 0), ((castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ K2set I g e0 z0 bw ↔
          Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β ∧
          ∀ PP ∈ Pg, redFn β PP (Lev.finE (D.sp.Y 0) κ) ∈ unipSym (kP PP) (D.sp.Y 0).rank D.R.rS D.R.k) ∧
        ((castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ K2set I g e0 z0 bw →
          star (chi2f I psiEf g e0 f0 z0 bw bwd (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2) =
          ∏ PP ∈ Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (redFn β PP (Lev.finE (D.sp.Y 0) κ)))) := by
    intro I hI g hg e0 f0 z0 bw bwd ew hF hn psiEf hadd hint hrat
    subst hI hg
    obtain ⟨β, hβ, hK⟩ := GlobalTheory.FlagBasis.read_inst D e0 f0 z0 bw bwd ew hF hn psiEf hadd hint hrat Pg hPg hnc ψ0 hψ
    refine ⟨β, hβ, fun κ => ?_⟩
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx := hK (Formalism.IndefR.RationalEmbedding.iota D κ).2
    generalize Lev.finE (D.sp.Y 0) κ = y at e2 ⊢
    subst e2
    exact hx
  exact key X.B.I h X.B.g X.g_eq X.e0 X.f0 X.z0 X.bw X.bwd X.ew (GlobalTheory.FlagBasis.isRefFrame_setting X) X.n_eq X.psiEf
    X.psiEf_add X.psiEf_int X.psiEf_rat

end Main

end
end
