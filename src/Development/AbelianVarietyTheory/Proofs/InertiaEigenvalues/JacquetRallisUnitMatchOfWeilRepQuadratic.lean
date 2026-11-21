import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchOfWeilRepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepresentationHyperbolicSplit
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
import GroundTheory.LocalFields.UnramifiedNormSurj
import GroundTheory.LocalFields.UnramifiedGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorRepApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransfer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSucc

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR

theorem weilAt_of_subsingleton (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (hK : Subsingleton A.K) : WeilAt A := by
  have h01 : (0 : A.L) = 1 := by
    rw [← map_zero (algebraMap A.K A.L), ← map_one (algebraMap A.K A.L), Subsingleton.elim (0 : A.K) 1]
  haveI hL : Subsingleton A.L := subsingleton_of_zero_eq_one h01
  have hpsi : ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ t : A.K, A.psiK ψ t = 1 := by
    intro ψ _ t
    unfold Et.psiK
    rw [Subsingleton.elim t 0, map_zero, AddChar.map_zero_eq_one]
  intro ψ hψ x μ hμ
  haveI := hμ.1
  have hpos : 0 < μ Set.univ := (isOpen_univ.measure_pos μ Set.univ_nonempty)
  have hfin : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
  have hreal : μ.real Set.univ ≠ 0 := by
    rw [measureReal_def]; exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  refine ⟨(μ.real Set.univ : ℂ)⁻¹, fun _ φ => φ, ?_, ?_⟩
  · exact ⟨fun _ _ hf => hf, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  · intro φ _
    refine ⟨?_, ?_, ?_⟩
    · intro z y; simp [hpsi ψ hψ]
    · intro s y
      have he : A.etaK (s : A.K) = 1 := by
        unfold Et.etaK eta
        rw [Subsingleton.elim (s : A.K) 1, map_one]
        rw [if_pos ⟨1, by simp⟩]
      have ha : A.absK (s : A.K) = 1 := by
        unfold Et.absK
        rw [dif_pos s.isUnit]
        rw [Subsingleton.elim (s.isUnit.unit) 1, map_one]
        rfl
      rw [he, ha, Subsingleton.elim ((s : A.K) • y) y]
      simp
    · intro y
      unfold fourB
      have : (fun x' => φ x' * A.kerL ψ x x' y) = fun _ => φ y := by
        funext x'
        unfold Et.kerL
        rw [hpsi ψ hψ, Subsingleton.elim x' y, mul_one]
      rw [this, integral_const, Complex.real_smul]
      show φ y = _
      have hc : ((μ.real Set.univ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hreal
      field_simp

end GlobalTheory.JR
end
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationExistsEtale_of_subsingleton : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Subsingleton A.K → WeilAt A := by
  atlas_forward_decl GlobalTheory.JR.weilAt_of_subsingleton
end

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.NonNorm

open ValuativeRel GroundTheory.LocalField IntermediateField

theorem not_two_dvd_ord_norm (F K L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Field L] [Algebra K L] (h2 : Module.finrank K L = 2) (ζ : L)
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[F] ^ 2 - 1)) (htop : K⟮ζ⟯ = ⊤) (s : K) (hs0 : s ≠ 0)
    (hs : ¬ ∃ y : L, Algebra.norm K y = s) : ¬ (2 : ℤ) ∣ ord (Algebra.norm F s) := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  obtain ⟨vK, tK, hK, eK⟩ := exists_isNonarchimedeanLocalField_valuativeExtension F K
  obtain ⟨vL, tL, hL, eL⟩ := exists_isNonarchimedeanLocalField_valuativeExtension K L
  have hm : ((Nat.card 𝓀[F] ^ 2 - 1 : ℕ) : 𝓀[K]) ≠ 0 :=
    natCast_residueField_ne_zero K (natCast_card_pow_sub_one_ne_zero (K := F) two_ne_zero)
  haveI : IsUnramified K L := ⟨ramificationIndex_eq_one_of_adjoin_eq_top hζ hm htop⟩
  have hodd : ¬ (2 : ℤ) ∣ ord s := by
    intro hd
    have h := (mem_range_normUnits_iff (K := K) (L := L) (Units.mk0 s hs0)).2 (by rw [h2]; exact hd)
    obtain ⟨y, hy⟩ := h
    exact hs ⟨y, congrArg Units.val hy⟩
  have hf : ¬ 2 ∣ residueDegree F K := by
    rintro ⟨j, hj⟩
    have hcard : Nat.card 𝓀[K] = Nat.card 𝓀[F] ^ residueDegree F K := by
      rw [residueDegree_eq_finrank]
      exact Module.natCard_eq_pow_finrank
    obtain ⟨z, hz⟩ := exists_isPrimitiveRoot_card_residueField_sub_one (L := K)
    have hz1 : IsPrimitiveRoot (z : K) (Nat.card 𝓀[K] - 1) :=
      hz.map_of_injective (f := (𝒪[K]).subtype) Subtype.val_injective
    have hz2 : IsPrimitiveRoot (algebraMap K L z) (Nat.card 𝓀[K] - 1) :=
      hz1.map_of_injective (algebraMap K L).injective
    haveI : NeZero (Nat.card 𝓀[K] - 1) := ⟨by have := one_lt_card_residueField K; omega⟩
    have hdvd : Nat.card 𝓀[F] ^ 2 - 1 ∣ Nat.card 𝓀[K] - 1 := by
      rw [hcard, hj, pow_mul]
      exact Nat.sub_one_dvd_pow_sub_one _ _
    obtain ⟨i, -, hi⟩ := hz2.eq_pow_of_pow_eq_one ((hζ.pow_eq_one_iff_dvd _).2 hdvd)
    have hbot : K⟮ζ⟯ = ⊥ := by
      rw [adjoin_simple_eq_bot_iff, ← hi, ← map_pow]
      exact IntermediateField.algebraMap_mem _ _
    have h1 : Module.finrank K L = 1 := by
      rw [← finrank_top', ← htop, hbot, IntermediateField.finrank_bot]
    omega
  rw [ord_norm]
  intro hd
  rcases (Int.prime_two.dvd_or_dvd hd) with h | h
  · exact hf (by exact_mod_cast h)
  · exact hodd h

@[reducible] noncomputable def normRel (F : Type) [NormedField F] [IsUltrametricDist F] : ValuativeRel F :=
  ValuativeRel.ofValuation (NormedField.valuation (K := F))

theorem isLocalField (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    letI := normRel F
    IsNonarchimedeanLocalField F := by
  letI := normRel F
  have hc : (NormedField.valuation (K := F)).Compatible := Valuation.Compatible.ofValuation _
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := inferInstance, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := F))
      (fun {s} => (NormedField.toValued (K := F)).is_topological_valuation s)
  · rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))]
    infer_instance

theorem ord_eq_of_norm_eq (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (x y : F) (h : ‖x‖ = ‖y‖) :
    letI := normRel F
    haveI := isLocalField F
    ord x = ord y := by
  letI := normRel F
  haveI := isLocalField F
  have h1 : x ≤ᵥ y := h.le
  have h2 : y ≤ᵥ x := h.ge
  rw [(valuation F).vle_iff_le] at h1 h2
  unfold ord
  rw [normalizedValuation_eq_iff.2 (le_antisymm h1 h2)]

theorem etaK_eq_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by
  intro F E _ _ _ _ hU A hK hL s hs
  haveI := hU.ultraF
  haveI := hU.ultraE
  haveI := hU.lcF
  haveI := hU.lcE
  letI := normRel F
  letI := normRel E
  haveI := isLocalField F
  haveI := isLocalField E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : ValuativeExtension F E := ⟨fun a b => by
    change ‖algebraMap F E a‖ ≤ ‖algebraMap F E b‖ ↔ ‖a‖ ≤ ‖b‖
    rw [norm_algebraMap', norm_algebraMap']⟩
  have he : ramificationIndex F E = 1 := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
    obtain ⟨x, hx⟩ := hU.unram (π : E)
    have h1 := ord_eq_of_norm_eq E (π : E) (algebraMap F E x) (by rw [norm_algebraMap', hx])
    rw [ord_uniformizer hπ, ord_algebraMap] at h1
    have h2 : (ramificationIndex F E : ℤ) ∣ 1 := ⟨_, h1⟩
    exact Nat.dvd_one.1 (by exact_mod_cast h2)
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified F E he
  have hcard : Nat.card 𝓀[E] = Nat.card 𝓀[F] ^ 2 := by
    rw [← hU.finrank_eq, ← residueDegree_eq_finrank_of_unramified F E he, residueDegree_eq_finrank]
    exact Module.natCard_eq_pow_finrank
  rw [hcard] at hζ
  obtain ⟨⟨b⟩, -⟩ := Et.quadratic_structure F E A
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  have h2 : Module.finrank A.K A.L = 2 := by simpa using Module.finrank_eq_card_basis b
  have hζ' : IsPrimitiveRoot (algebraMap E A.L ζ) (Nat.card 𝓀[F] ^ 2 - 1) :=
    hζ.map_of_injective (algebraMap E A.L).injective
  have hE : ∀ e : E, algebraMap E A.L e ∈ A.K⟮algebraMap E A.L ζ⟯ := by
    intro e
    have he' : e ∈ F⟮ζ⟯ := by rw [htop]; trivial
    induction he' using IntermediateField.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact mem_adjoin_simple_self _ _
    | algebraMap x =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A.K A.L]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop' : A.K⟮algebraMap E A.L ζ⟯ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hbc := A.push.symm.out
    induction y using hbc.inductionOn with
    | zero => exact zero_mem _
    | tmul e => exact hE e
    | smul k y hy => exact IntermediateField.smul_mem _ (hy trivial)
    | add y z hy hz => exact add_mem (hy trivial) (hz trivial)
  have hodd := not_two_dvd_ord_norm F A.K A.L h2 _ hζ' htop' s s.ne_zero hs
  unfold Et.etaK eta
  rw [if_neg]
  rintro ⟨y, hy⟩
  apply hodd
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h0 : Algebra.norm F (s : A.K) = 0 := norm_eq_zero.1 (by simpa using hy)
    exact s.ne_zero (Algebra.norm_eq_zero_iff.1 h0)
  have h3 := ord_eq_of_norm_eq F (Algebra.norm F (s : A.K)) (y ^ 2) (by rw [norm_pow, hy])
  rw [ord_pow hy0] at h3
  exact ⟨ord y, by exact_mod_cast h3⟩

end GlobalTheory.JR.NonNorm
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaK_eq_neg_one_of_not_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by
  atlas_forward_decl GlobalTheory.JR.NonNorm.etaK_eq_neg_one
end

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.EtQuot
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

section star
variable {L : Type} [CommRing L] [StarRing L]

def quotStarRing (J : Ideal L) (hJ : ∀ a ∈ J, star a ∈ J) : StarRing (L ⧸ J) where
  star := Ideal.Quotient.lift J ((Ideal.Quotient.mk J).comp (starRingEnd L))
    (fun a ha => by
      simp only [RingHom.comp_apply, starRingEnd_apply]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hJ a ha))
  star_involutive x := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp
  star_mul x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [← map_mul, mul_comm]
  star_add x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [← map_add]

end star

variable (A : Et F E) (e : A.K)

abbrev QK := A.K ⧸ Ideal.span {e}

abbrev QL := A.L ⧸ (Ideal.span {e}).map (algebraMap A.K A.L)

instance twQ : IsScalarTower F (QK A e) (QL A e) := IsScalarTower.of_algebraMap_eq fun x => by
  rw [IsScalarTower.algebraMap_apply F A.K (QK A e)]
  simp only [Ideal.Quotient.algebraMap_eq, RingHom.comp_apply, Ideal.Quotient.algebraMap_quotient_map_quotient]
  show Ideal.Quotient.mk _ (algebraMap F A.L x) = _
  rw [IsScalarTower.algebraMap_apply F A.K A.L]

theorem star_mem (a : A.L) (ha : a ∈ (Ideal.span {e}).map (algebraMap A.K A.L)) :
    star a ∈ (Ideal.span {e}).map (algebraMap A.K A.L) := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at ha ⊢
  obtain ⟨c, rfl⟩ := ha
  exact ⟨star c, by rw [star_mul, A.star_K, mul_comm]⟩

def eq0 : TensorProduct A.K (QK A e) A.L ≃ₗ[A.K] QL A e :=
  (TensorProduct.comm A.K (QK A e) A.L).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A.L (Ideal.span {e})).symm.toLinearEquiv.restrictScalars A.K)

theorem etaleQuotientTensorLinearEquiv_one_tmul (x : A.L) : eq0 A e (1 ⊗ₜ x) = Ideal.Quotient.mk _ x := by
  simp only [eq0, LinearEquiv.trans_apply, TensorProduct.comm_tmul, LinearEquiv.restrictScalars_apply,
    AlgEquiv.toLinearEquiv_apply]
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {e})), Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul,
    one_smul]
  rfl

theorem isBaseChange_quot : IsBaseChange (QK A e) (IsScalarTower.toAlgHom A.K A.L (QL A e)).toLinearMap :=
  IsBaseChange.of_equiv ((eq0 A e).extendScalarsOfSurjective Ideal.Quotient.mk_surjective) fun x => by
    simpa using etaleQuotientTensorLinearEquiv_one_tmul A e x

theorem push_quot : Algebra.IsPushout F E (QK A e) (QL A e) := by
  have h2 : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap :=
    (Algebra.isPushout_iff F A.K E A.L).1 A.push.symm
  have h5 := h2.comp (isBaseChange_quot A e)
  refine Algebra.IsPushout.symm ((Algebra.isPushout_iff F (QK A e) E (QL A e)).2 ?_)
  have hm : (IsScalarTower.toAlgHom F E (QL A e)).toLinearMap =
      (IsScalarTower.toAlgHom A.K A.L (QL A e)).toLinearMap.restrictScalars F ∘ₗ
        (IsScalarTower.toAlgHom F E A.L).toLinearMap := by
    ext y; rfl
  rw [hm]; exact h5

end GlobalTheory.JR.EtQuot

namespace GlobalTheory.JR.EtQuot
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable (A : Et F E) (e : A.K)

theorem isReduced_quot (he : IsIdempotentElem e) : IsReduced (QK A e) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, hn⟩ := hx
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hn
  obtain ⟨c, hc⟩ := hn
  have h1 : IsNilpotent (y * (1 - e)) := ⟨n + 1, by
    rw [mul_pow, he.one_sub.pow_succ_eq, pow_succ, ← hc]
    linear_combination (-(c * y)) * he.eq⟩
  have h2 := IsReduced.eq_zero _ h1
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨y, by linear_combination -h2⟩

def quotEt (he : IsIdempotentElem e) : Et F E :=
  letI tK : TopologicalSpace (QK A e) := moduleTopology F _
  haveI mtK : IsModuleTopology F (QK A e) := ⟨rfl⟩
  letI tL : TopologicalSpace (QL A e) := moduleTopology F _
  haveI mtL : IsModuleTopology F (QL A e) := ⟨rfl⟩
  letI mK : MeasurableSpace (QK A e) := borel _
  letI mL : MeasurableSpace (QL A e) := borel _
  letI sL : StarRing (QL A e) := quotStarRing _ (star_mem A e)
  { K := QK A e
    L := QL A e
    redK := isReduced_quot A e he
    trK := IsModuleTopology.isTopologicalRing F _
    lcK := (IsModuleTopology.isOpenQuotientMap_of_surjective (R := F) (A := A.K)
      (φ := (Ideal.Quotient.mkₐ F (Ideal.span {e})).toLinearMap) (Ideal.Quotient.mkₐ_surjective F _)).locallyCompactSpace
    bK := ⟨rfl⟩
    bL := ⟨rfl⟩
    push := push_quot A e
    star_K := fun x => by
      obtain ⟨k, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
      show Ideal.Quotient.mk _ (star _) = _
      rw [A.star_K]
    star_E := fun y => by
      show Ideal.Quotient.mk _ (star (algebraMap E A.L y)) = Ideal.Quotient.mk _ (algebraMap E A.L (star y))
      rw [A.star_E] }

theorem exists_idem (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] [Nontrivial K] (hf : ¬ IsField K) :
    ∃ e : K, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  obtain ⟨m₁, hm₁⟩ := Ideal.exists_maximal K
  have hex : ∃ m₂ : Ideal K, m₂.IsMaximal ∧ m₂ ≠ m₁ := by
    by_contra h
    push_neg at h
    haveI : IsLocalRing K := IsLocalRing.of_unique_max_ideal ⟨m₁, hm₁, fun y hy => h y hy⟩
    exact hf (IsArtinianRing.isField_of_isReduced_of_isLocalRing K)
  obtain ⟨m₂, hm₂, hne⟩ := hex
  let i : MaximalSpectrum K := ⟨m₁, hm₁⟩
  let j : MaximalSpectrum K := ⟨m₂, hm₂⟩
  have hij : j ≠ i := fun h => hne (congrArg MaximalSpectrum.asIdeal h)
  haveI : i.asIdeal.IsMaximal := hm₁
  haveI : j.asIdeal.IsMaximal := hm₂
  let φ := IsArtinianRing.equivPi K
  refine ⟨φ.symm (Pi.single i 1), ?_, ?_, ?_⟩
  · unfold IsIdempotentElem
    rw [← map_mul, ← Pi.single_mul, mul_one]
  · intro h
    have := congrArg φ h
    simp at this
  · intro h
    have := congrFun (congrArg φ h) j
    simp [Pi.single_apply, hij] at this

end GlobalTheory.JR.EtQuot

namespace GlobalTheory.JR.EtQuot

theorem idem_eq_one_of_isUnit {K : Type} [CommRing K] {e : K} (he : IsIdempotentElem e) (hu : IsUnit e) : e = 1 := by
  obtain ⟨u, rfl⟩ := hu
  calc (u : K) = u * u * ↑u⁻¹ := by simp
    _ = u * ↑u⁻¹ := by rw [he.eq]
    _ = 1 := by simp

theorem nontrivial_quot {K : Type} [CommRing K] {e : K} (he : IsIdempotentElem e) (h1 : e ≠ 1) :
    Nontrivial (K ⧸ Ideal.span {e}) :=
  Ideal.Quotient.nontrivial_iff.2 (fun h => h1 (idem_eq_one_of_isUnit he (Ideal.span_singleton_eq_top.1 h)))

theorem exists_splitting : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), Nontrivial A.K → ¬ IsField A.K →
    ∃ (A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L),
      IsSplitting A A₁ A₂ eK eL ∧ Module.finrank F A₁.K < Module.finrank F A.K ∧
        Module.finrank F A₂.K < Module.finrank F A.K := by
  intro F E _ _ _ _ _ A hnt hf
  haveI : IsArtinianRing A.K := IsArtinianRing.of_finite F A.K
  obtain ⟨e, he, h0, h1⟩ := exists_idem A.K hf
  let A₁ := quotEt A e he
  let A₂ := quotEt A (1 - e) he.one_sub
  let eK : A.K ≃ₐ[F] A₁.K × A₂.K :=
    AlgEquiv.prodQuotientOfIsIdempotentElem F he he.one_sub (by ring) he.mul_one_sub_self
  let e' := algebraMap A.K A.L e
  have he' : IsIdempotentElem e' := he.map _
  have hJ1 : (Ideal.span {e}).map (algebraMap A.K A.L) = Ideal.span {e'} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hJ2 : (Ideal.span {1 - e}).map (algebraMap A.K A.L) = Ideal.span {1 - e'} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
  let eL : A.L ≃ₐ[F] A₁.L × A₂.L :=
    (AlgEquiv.prodQuotientOfIsIdempotentElem F he' he'.one_sub (by ring) he'.mul_one_sub_self).trans
      (AlgEquiv.prodCongr (Ideal.quotientEquivAlgOfEq F hJ1.symm) (Ideal.quotientEquivAlgOfEq F hJ2.symm))
  have hsum : Module.finrank F A.K = Module.finrank F A₁.K + Module.finrank F A₂.K := by
    rw [eK.toLinearEquiv.finrank_eq, Module.finrank_prod]
  haveI : Nontrivial A₁.K := nontrivial_quot he h1
  haveI : Nontrivial A₂.K := nontrivial_quot he.one_sub (fun h => h0 (by linear_combination -h))
  have p1 : 0 < Module.finrank F A₁.K := Module.finrank_pos
  have p2 : 0 < Module.finrank F A₂.K := Module.finrank_pos
  refine ⟨A₁, A₂, eK, eL, ⟨fun k => ?_, fun y => ?_, fun y => ?_⟩, by omega, by omega⟩
  · refine Prod.ext ?_ ?_
    · show Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ (algebraMap A.K A.L k)) =
        algebraMap (QK A e) (QL A e) (Ideal.Quotient.mk _ k)
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.Quotient.algebraMap_quotient_map_quotient]
    · show Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ (algebraMap A.K A.L k)) =
        algebraMap (QK A (1 - e)) (QL A (1 - e)) (Ideal.Quotient.mk _ k)
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.Quotient.algebraMap_quotient_map_quotient]
  · refine Prod.ext ?_ ?_
    · show Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ (algebraMap E A.L y)) =
        Ideal.Quotient.mk _ (algebraMap E A.L y)
      rw [Ideal.quotientEquivAlgOfEq_mk]
    · show Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ (algebraMap E A.L y)) =
        Ideal.Quotient.mk _ (algebraMap E A.L y)
      rw [Ideal.quotientEquivAlgOfEq_mk]
  · refine Prod.ext ?_ ?_
    · show Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ (star y)) =
        (quotStarRing _ (star_mem A e)).star (Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ y))
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]
      rfl
    · show Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ (star y)) =
        (quotStarRing _ (star_mem A (1 - e))).star (Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ y))
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]
      rfl

end GlobalTheory.JR.EtQuot
end
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleInvolutiveAlgebraSplitting_smaller : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Nontrivial A.K → ¬ IsField A.K → ∃ (A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L), IsSplitting A A₁ A₂ eK eL ∧ Module.finrank F A₁.K < Module.finrank F A.K ∧ Module.finrank F A₂.K < Module.finrank F A.K := by
  atlas_forward_decl GlobalTheory.JR.EtQuot.exists_splitting
end

section
section
open GlobalTheory.JR GlobalTheory.JR.WeilProd Filter Topology

namespace GlobalTheory.JR.WeilProd.TensorTest

section Basic
variable {X : Type} [TopologicalSpace X]

theorem isTest_of_lc {g : X → ℂ} (hg : IsLocallyConstant g) {K : Set X} (hK : IsCompact K)
    (hs : Function.support g ⊆ K) : IsTest g := by
  refine ⟨hg, ?_⟩
  have hcl : IsClosed (Function.support g) := by
    show IsClosed {x | g x ≠ 0}
    exact (hg.isOpen_fiber 0).isClosed_compl
  unfold HasCompactSupport tsupport
  rw [hcl.closure_eq]
  exact hK.of_isClosed_subset hcl hs

theorem isTest_zero : IsTest (0 : X → ℂ) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

theorem isTest_add {f f' : X → ℂ} (hf : IsTest f) (hf' : IsTest f') : IsTest (f + f') :=
  ⟨hf.1.add hf'.1, hf.2.add hf'.2⟩

theorem isTest_smul (c : ℂ) {f : X → ℂ} (hf : IsTest f) : IsTest (c • f) :=
  ⟨hf.1.comp (c * ·), hf.2.smul_left⟩

theorem isTest_sum {ι : Type} (s : Finset ι) (F : ι → X → ℂ) (hF : ∀ j ∈ s, IsTest (F j)) :
    IsTest (∑ j ∈ s, F j) := by
  classical
  revert hF
  refine Finset.induction_on s (fun _ => by simpa using (isTest_zero : IsTest (0 : X → ℂ))) ?_
  intro a s ha ih hF
  rw [Finset.sum_insert ha]
  exact isTest_add (hF a (Finset.mem_insert_self a s)) (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem map_zero {G : Type} [Group G] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W) (g : G) : W g 0 = 0 := by
  have := hW.2.2.2 g 1 0 0 isTest_zero isTest_zero
  simpa using this

theorem map_sum {G : Type} [Group G] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W) (g : G) {ι : Type}
    (s : Finset ι) (c : ι → ℂ) (f : ι → X → ℂ) (hf : ∀ j ∈ s, IsTest (f j)) :
    W g (∑ j ∈ s, c j • f j) = ∑ j ∈ s, c j • W g (f j) := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => by simp [map_zero hW g]) ?_
  intro a s ha ih hf
  rw [Finset.sum_insert ha, Finset.sum_insert ha]
  have hs : IsTest (∑ j ∈ s, c j • f j) :=
    isTest_sum s _ fun j hj => isTest_smul _ (hf j (Finset.mem_insert_of_mem hj))
  rw [hW.2.2.2 g (c a) (f a) _ (hf a (Finset.mem_insert_self a s)) hs,
    ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

end Basic

section Prod
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem isTest_mul_prod {a : X → ℂ} {b : Y → ℂ} (ha : IsTest a) (hb : IsTest b) :
    IsTest (fun p : X × Y => a p.1 * b p.2) := by
  refine isTest_of_lc ?_ (ha.2.isCompact.prod hb.2.isCompact) ?_
  · exact IsLocallyConstant.comp₂ (ha.1.comp_continuous continuous_fst) (hb.1.comp_continuous continuous_snd)
      (fun x y => x * y)
  · intro p hp
    have h1 : a p.1 ≠ 0 := left_ne_zero_of_mul hp
    have h2 : b p.2 ≠ 0 := right_ne_zero_of_mul hp
    exact ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩

theorem isTest_fibre {f : X × Y → ℂ} (hf : IsTest f) (u : X) : IsTest (fun v => f (u, v)) := by
  refine isTest_of_lc (hf.1.comp_continuous (continuous_const.prodMk continuous_id)) (hf.2.isCompact.image continuous_snd) ?_
  intro v hv
  exact ⟨(u, v), subset_tsupport _ hv, rfl⟩

theorem isLocallyConstant_curry {f : X × Y → ℂ} (hf : IsTest f) :
    IsLocallyConstant (fun u => fun v => f (u, v)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u₀
  have hK : IsCompact (Prod.snd '' tsupport f) := hf.2.isCompact.image continuous_snd
  have hev : ∀ᶠ u in 𝓝 u₀, ∀ v ∈ Prod.snd '' tsupport f, f (u, v) = f (u₀, v) := by
    refine hK.eventually_forall_of_forall_eventually ?_
    intro y _
    have h1 : ∀ᶠ z in 𝓝 (u₀, y), f z = f (u₀, y) := ((IsLocallyConstant.iff_eventually_eq f).1 hf.1) (u₀, y)
    have hc : Continuous (fun z : X × Y => (u₀, z.2)) := (continuous_const.prodMk continuous_id).comp continuous_snd
    have ht : Tendsto (fun z : X × Y => (u₀, z.2)) (𝓝 (u₀, y)) (𝓝 (u₀, y)) := hc.continuousAt
    have h2 : ∀ᶠ z in 𝓝 (u₀, y), f (u₀, z.2) = f (u₀, y) :=
      ht.eventually (((IsLocallyConstant.iff_eventually_eq f).1 hf.1) (u₀, y))
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2]
  filter_upwards [hev] with u hu
  funext v
  by_cases hv : v ∈ Prod.snd '' tsupport f
  · exact hu v hv
  · have hA : (u, v) ∉ tsupport f := fun h => hv ⟨_, h, rfl⟩
    have hB : (u₀, v) ∉ tsupport f := fun h => hv ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport hA, image_eq_zero_of_notMem_tsupport hB]

theorem isTest_sum_fn {ι : Type} (s : Finset ι) (F : ι → X × Y → ℂ) (hF : ∀ j ∈ s, IsTest (F j)) :
    IsTest (fun p => ∑ j ∈ s, F j p) := by
  have := isTest_sum s F hF
  rwa [Finset.sum_fn] at this

theorem decomp {f : X × Y → ℂ} (hf : IsTest f) :
    ∃ (s : Finset (Y → ℂ)) (a : (Y → ℂ) → X → ℂ), (∀ φ ∈ s, IsTest (a φ)) ∧ (∀ φ ∈ s, IsTest φ) ∧
      ∀ p : X × Y, f p = ∑ φ ∈ s, a φ p.1 * φ p.2 := by
  classical
  have hF : IsLocallyConstant (fun u => fun v => f (u, v)) := isLocallyConstant_curry hf
  have hK₁ : IsCompact (Prod.fst '' tsupport f) := hf.2.isCompact.image continuous_fst
  have hzero : ∀ u, u ∉ Prod.fst '' tsupport f → (fun v => f (u, v)) = 0 := by
    intro u hu; funext v
    by_contra h
    exact hu ⟨(u, v), subset_tsupport _ h, rfl⟩
  have hfin : (Set.range (fun u => fun v => f (u, v))).Finite := by
    have : CompactSpace (Prod.fst '' tsupport f) := isCompact_iff_compactSpace.1 hK₁
    have h1 : (Set.range ((fun u => fun v => f (u, v)) ∘ ((↑) : Prod.fst '' tsupport f → X))).Finite :=
      (hF.comp_continuous continuous_subtype_val).range_finite
    refine (h1.union (Set.finite_singleton 0)).subset ?_
    rintro _ ⟨u, rfl⟩
    by_cases hu : u ∈ Prod.fst '' tsupport f
    · exact Or.inl ⟨⟨u, hu⟩, rfl⟩
    · exact Or.inr (hzero u hu)
  refine ⟨hfin.toFinset.erase 0, fun φ u => if (fun v => f (u, v)) = φ then 1 else 0, ?_, ?_, ?_⟩
  · intro φ hφ
    have hφ0 : φ ≠ 0 := Finset.ne_of_mem_erase hφ
    refine isTest_of_lc (hF.comp fun ψ => if ψ = φ then (1:ℂ) else 0) hK₁ ?_
    intro u hu
    by_contra hK
    apply hu
    show (if (fun v => f (u, v)) = φ then (1:ℂ) else 0) = 0
    rw [hzero u hK, if_neg (Ne.symm hφ0)]
  · intro φ hφ
    obtain ⟨u, rfl⟩ : φ ∈ Set.range (fun u => fun v => f (u, v)) :=
      (hfin.mem_toFinset).1 (Finset.mem_of_mem_erase hφ)
    exact isTest_fibre hf u
  · rintro ⟨u, v⟩
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · have h0 : (fun v => f (u, v)) = 0 := by
        by_contra h0
        exact h (Finset.mem_erase.2 ⟨h0, hfin.mem_toFinset.2 ⟨u, rfl⟩⟩)
      exact congrFun h0 v

theorem tensorRep_eq {G H : Type} [Group G] [Group H] {W₁ : G → (X → ℂ) → X → ℂ}
    {W₂ : H → (Y → ℂ) → Y → ℂ} (hW₁ : IsTestRep W₁) (hW₂ : IsTestRep W₂) {ι : Type} (s : Finset ι)
    (A : ι → X → ℂ) (B : ι → Y → ℂ) (hA : ∀ j ∈ s, IsTest (A j)) (hB : ∀ j ∈ s, IsTest (B j))
    (f : X × Y → ℂ) (hf : ∀ p : X × Y, f p = ∑ j ∈ s, A j p.1 * B j p.2) (gh : G × H) :
    tensorRep W₁ W₂ gh f = fun p => ∑ j ∈ s, W₁ gh.1 (A j) p.1 * W₂ gh.2 (B j) p.2 := by
  funext p
  have h1 : ∀ u, (fun v => f (u, v)) = ∑ j ∈ s, A j u • B j := by
    intro u; funext v; rw [hf (u, v)]; simp [Finset.sum_apply, smul_eq_mul]
  have h2 : (fun u => W₂ gh.2 (fun v => f (u, v)) p.2) = ∑ j ∈ s, W₂ gh.2 (B j) p.2 • A j := by
    funext u
    rw [h1 u, map_sum hW₂ gh.2 s _ _ hB, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [smul_eq_mul, mul_comm]
  rw [tensorRep_apply, h2, map_sum hW₁ gh.1 s _ _ hA, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [smul_eq_mul, mul_comm]

end Prod
end GlobalTheory.JR.WeilProd.TensorTest

namespace GlobalTheory.JR.WeilProd
open TensorTest

theorem isTestRep_tensorRep {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) :
    IsTestRep W₁ → IsTestRep W₂ → IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f →
      (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
  intro hW₁ hW₂
  have hslice : ∀ f : X × Y → ℂ, IsTest f → ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
    intro f hf h y
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    have e : (fun u => W₂ h (fun v => f (u, v)) y) = ∑ φ ∈ s, W₂ h φ y • a φ := by
      funext u
      have h1 : (fun v => f (u, v)) = ∑ φ ∈ s, a φ u • φ := by
        funext v; rw [hfs (u, v)]; simp [Finset.sum_apply, smul_eq_mul]
      rw [h1, map_sum hW₂ h s (fun φ => a φ u) (fun φ => φ) hb, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun φ _ => ?_
      simp [smul_eq_mul, mul_comm]
    rw [e]
    exact isTest_sum s _ fun φ hφ => isTest_smul _ (ha φ hφ)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun f hf => ⟨isTest_fibre hf, hslice f hf⟩⟩
  · intro gh f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs gh]
    exact isTest_sum_fn s _ fun φ hφ => isTest_mul_prod (hW₁.1 _ _ (ha φ hφ)) (hW₂.1 _ _ (hb φ hφ))
  · intro f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs 1]
    funext p
    rw [hfs p]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    simp only [Prod.fst_one, Prod.snd_one]
    rw [hW₁.2.1 _ (ha φ hφ), hW₂.2.1 _ (hb φ hφ)]
  · intro gh gh' f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    have hs' : ∀ p, tensorRep W₁ W₂ gh' f p = ∑ φ ∈ s, W₁ gh'.1 (a φ) p.1 * W₂ gh'.2 φ p.2 := fun p => by
      rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs gh']
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs (gh * gh'),
      tensorRep_eq hW₁ hW₂ s (fun φ => W₁ gh'.1 (a φ)) (fun φ => W₂ gh'.2 φ) (fun φ hφ => hW₁.1 _ _ (ha φ hφ))
        (fun φ hφ => hW₂.1 _ _ (hb φ hφ)) _ hs' gh]
    funext p
    refine Finset.sum_congr rfl fun φ hφ => ?_
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [hW₁.2.2.1 _ _ _ (ha φ hφ), hW₂.2.2.1 _ _ _ (hb φ hφ)]
  · intro gh c f f' hf hf'
    funext p
    have e2 : (fun u => W₂ gh.2 (fun v => (c • f + f') (u, v)) p.2) =
        c • (fun u => W₂ gh.2 (fun v => f (u, v)) p.2) + (fun u => W₂ gh.2 (fun v => f' (u, v)) p.2) := by
      funext u
      show W₂ gh.2 (c • (fun v => f (u, v)) + fun v => f' (u, v)) p.2 = _
      rw [hW₂.2.2.2 gh.2 c _ _ (isTest_fibre hf u) (isTest_fibre hf' u)]
      rfl
    rw [tensorRep_apply, e2, hW₁.2.2.2 gh.1 c _ _ (hslice f hf _ _) (hslice f' hf' _ _)]
    rfl

end GlobalTheory.JR.WeilProd
end

open GlobalTheory.JR GlobalTheory.JR.WeilProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstantTestRepresentation_tensorProduct : ∀ {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y] (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ), IsTestRep W₁ → IsTestRep W₂ → IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f → (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
  atlas_forward_decl GlobalTheory.JR.WeilProd.isTestRep_tensorRep
end

section
section
open GlobalTheory.JR MeasureTheory

theorem GlobalTheory.JR.fourB_prod_iterated : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁] [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂] [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂] (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm → ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ), Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) → (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) → ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y, fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := by
  intro V V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he hes B B₁ B₂ hB₁ hB₂ hB μ μ₁ μ₂ hμ hμ₁ hμ₂
  let h : V ≃ₜ V₁ × V₂ := { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := hes }
  let hm : V ≃ᵐ V₁ × V₂ := h.toMeasurableEquiv
  haveI : (Measure.map e μ).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e he hes
  haveI : (μ₁.prod μ₂).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ₁ μ₂
  set k := Measure.addHaarScalarFactor (Measure.map e μ) (μ₁.prod μ₂) with hk
  have hkeq : Measure.map e μ = k • (μ₁.prod μ₂) := Measure.isAddLeftInvariant_eq_smul _ _
  have hkpos : 0 < k := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨((k : ℝ) : ℂ), by exact_mod_cast hkpos.ne', fun φ hφ y => ?_⟩
  have hmap : Measure.map hm μ = Measure.map e μ := rfl
  have step1 : fourB μ B φ y = ∫ q, φ (e.symm q) * B (e.symm q) y ∂(Measure.map e μ) := by
    rw [← hmap, hm.measurableEmbedding.integral_map]
    simp [fourB, hm, h]
  rw [step1, hkeq, integral_smul_nnreal_measure]
  have hcont : Continuous fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) :=
    (hφ.1.continuous.comp hes).mul ((hB₁.comp (by fun_prop : Continuous fun q : V₁ × V₂ => (q.1, (e y).1))).mul
      (hB₂.comp (by fun_prop : Continuous fun q : V₁ × V₂ => (q.2, (e y).2))))
  have hsupp : HasCompactSupport fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) := by
    have : HasCompactSupport (φ ∘ h.symm) := hφ.2.comp_homeomorph h.symm
    exact this.mul_right
  have hint := hcont.integrable_of_hasCompactSupport hsupp (μ := μ₁.prod μ₂)
  have e2 : (fun q : V₁ × V₂ => φ (e.symm q) * B (e.symm q) y) =
      fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) := by
    ext q; rw [hB]; simp
  rw [e2, integral_prod _ hint]
  simp only [NNReal.smul_def, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← integral_mul_const]
  congr 1; ext v; ring
end

open GlobalTheory.JR MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourB_prod_iterated_alt : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁] [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂] [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂] (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm → ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ), Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) → (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) → ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y, fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := by
  atlas_forward_decl GlobalTheory.JR.fourB_prod_iterated
end

section
section
open GlobalTheory.JR MeasureTheory
open scoped Pointwise

namespace GlobalTheory.JR.EtProdAbs

theorem distribHaarChar_prod {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [LocallyCompactSpace R₁] [T2Space R₁] [SecondCountableTopology R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
    [LocallyCompactSpace R₂] [T2Space R₂] [SecondCountableTopology R₂] (v : (R₁ × R₂)ˣ) :
    distribHaarChar (R₁ × R₂) v =
      distribHaarChar R₁ (Units.map (RingHom.fst R₁ R₂ : R₁ × R₂ →* R₁) v) *
        distribHaarChar R₂ (Units.map (RingHom.snd R₁ R₂ : R₁ × R₂ →* R₂) v) := by
  borelize R₁ R₂
  let μ₁ : Measure R₁ := Measure.addHaar
  let μ₂ : Measure R₂ := Measure.addHaar
  obtain ⟨S₁⟩ : Nonempty (TopologicalSpace.PositiveCompacts R₁) := inferInstance
  obtain ⟨S₂⟩ : Nonempty (TopologicalSpace.PositiveCompacts R₂) := inferInstance
  have h0₁ : μ₁ (S₁ : Set R₁) ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ₁ S₁.interior_nonempty).ne'
  have h0₂ : μ₂ (S₂ : Set R₂) ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ₂ S₂.interior_nonempty).ne'
  have h1₁ : μ₁ (S₁ : Set R₁) ≠ ⊤ := S₁.isCompact.measure_lt_top.ne
  have h1₂ : μ₂ (S₂ : Set R₂) ≠ ⊤ := S₂.isCompact.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ₁.prod μ₂) (s := (S₁ : Set R₁) ×ˢ (S₂ : Set R₂))
    (by rw [Measure.prod_prod]; exact mul_ne_zero h0₁ h0₂)
    (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top h1₁ h1₂) ?_
  have hs : v • ((S₁ : Set R₁) ×ˢ (S₂ : Set R₂)) =
      (Units.map (RingHom.fst R₁ R₂ : R₁ × R₂ →* R₁) v • (S₁ : Set R₁)) ×ˢ
        (Units.map (RingHom.snd R₁ R₂ : R₁ × R₂ →* R₂) v • (S₂ : Set R₂)) := by
    ext ⟨x, y⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_prod, Set.mem_prod, Set.mem_smul_set_iff_inv_smul_mem,
      Set.mem_smul_set_iff_inv_smul_mem, ← map_inv, ← map_inv]
    exact Iff.rfl
  rw [hs, Measure.prod_prod, Measure.prod_prod, ← distribHaarChar_mul μ₁, ← distribHaarChar_mul μ₂]
  push_cast
  ring

theorem absK_prod : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K),
    A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by
  intro F E _ _ _ _ U A A₁ A₂ eK t
  have := U.ultraF; have := U.lcF
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₁.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₂.K
  by_cases ht : IsUnit t
  · let u : A.Kˣ := ht.unit
    let v : (A₁.K × A₂.K)ˣ := Units.map (eK : A.K →* A₁.K × A₂.K) u
    let e' : A.K ≃ₜ+ A₁.K × A₂.K :=
      { eK.toAddEquiv with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap eK.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap eK.symm.toLinearMap }
    have h1 : distribHaarChar (A₁.K × A₂.K) v = distribHaarChar A.K u :=
      ModuleNorm.distribHaarChar_transport e' u v (fun x => by
        change eK ((u : A.K) * x) = eK (u : A.K) * eK x
        rw [map_mul])
    rw [distribHaarChar_prod] at h1
    have ht' : t = (u : A.K) := (IsUnit.unit_spec ht).symm
    have e1 : (eK t).1 = ((Units.map (RingHom.fst A₁.K A₂.K : A₁.K × A₂.K →* A₁.K) v : A₁.Kˣ) : A₁.K) := by
      rw [ht']; rfl
    have e2 : (eK t).2 = ((Units.map (RingHom.snd A₁.K A₂.K : A₁.K × A₂.K →* A₂.K) v : A₂.Kˣ) : A₂.K) := by
      rw [ht']; rfl
    rw [e1, e2, ht', EtMeas.absK_unit, EtMeas.absK_unit, EtMeas.absK_unit, ← h1]
    push_cast
    rfl
  · have h0 : A.absK t = 0 := by simp [Et.absK, ht]
    have hn : ¬ IsUnit (eK t) := fun h => ht ((isUnit_map_iff eK t).1 h)
    rw [Prod.isUnit_iff, not_and_or] at hn
    rw [h0]
    rcases hn with hn | hn
    · have : A₁.absK (eK t).1 = 0 := by simp [Et.absK, hn]
      rw [this, zero_mul]
    · have : A₂.absK (eK t).2 = 0 := by simp [Et.absK, hn]
      rw [this, mul_zero]

end GlobalTheory.JR.EtProdAbs
end

open GlobalTheory.JR MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absK_mul_of_etale_splitting : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K), A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by
  atlas_forward_decl GlobalTheory.JR.EtProdAbs.absK_prod
end

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilProd

def transRep {G H X Y : Type} (ρ : G → H) (e : X ≃ Y) (W : H → (Y → ℂ) → Y → ℂ) : G → (X → ℂ) → X → ℂ :=
  fun g f x => W (ρ g) (f ∘ e.symm) (e x)

theorem isTest_comp_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {f : Y → ℂ}
    (hf : IsTest f) : IsTest (f ∘ e) :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

theorem isTestRep_transRep {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    (ρ : G →* H) (e : X ≃ₜ Y) (W : H → (Y → ℂ) → Y → ℂ) (hW : IsTestRep W) :
    IsTestRep (transRep ρ e.toEquiv W) := by
  obtain ⟨h1, h2, h3, h4⟩ := hW
  have ht : ∀ f, IsTest f → IsTest (f ∘ e.symm) := fun f hf => isTest_comp_homeomorph e.symm hf
  refine ⟨fun g f hf => isTest_comp_homeomorph e (h1 _ _ (ht f hf)), fun f hf => ?_, fun g h f hf => ?_,
    fun g c f f' hf hf' => ?_⟩
  · funext x
    simp [transRep, map_one, h2 _ (ht f hf)]
  · funext x
    show W (ρ (g * h)) (f ∘ e.symm) (e x) = W (ρ g) ((fun x => W (ρ h) (f ∘ e.symm) (e x)) ∘ e.symm) (e x)
    rw [map_mul, h3 _ _ _ (ht f hf)]
    congr 1
    funext y; simp
  · funext x
    have : (c • f + f') ∘ e.toEquiv.symm = c • (f ∘ e.symm) + f' ∘ e.symm := rfl
    simp only [transRep, this, h4 _ c _ _ (ht f hf) (ht f' hf')]
    rfl

theorem norm_prod_apply {R S T : Type} [Field R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Module.Finite R S] [Module.Finite R T] (p : S × T) :
    Algebra.norm R p = Algebra.norm R p.1 * Algebra.norm R p.2 := by
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_prodMap]
  congr 1

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem trace_split (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (k : A.K) :
    Algebra.trace F A.K k = Algebra.trace F A₁.K (eK k).1 + Algebra.trace F A₂.K (eK k).2 := by
  rw [← Algebra.trace_eq_of_algEquiv eK, Algebra.trace_prod_apply]

theorem norm_split (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (k : A.K) :
    Algebra.norm F k = Algebra.norm F (eK k).1 * Algebra.norm F (eK k).2 := by
  rw [← Algebra.norm_eq_of_algEquiv eK, norm_prod_apply]

theorem splitL [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (y : A.L) :
    eK (A.NL y) = (A₁.NL (eL y).1, A₂.NL (eL y).2) ∧
      eK (Algebra.trace A.K A.L y) = (Algebra.trace A₁.K A₁.L (eL y).1, Algebra.trace A₂.K A₂.L (eL y).2) := by
  obtain ⟨-, i₁, n₁, t₁, -⟩ := Et.quadratic_structure F E A₁
  obtain ⟨-, i₂, n₂, t₂, -⟩ := Et.quadratic_structure F E A₂
  obtain ⟨-, -, n, t, -⟩ := Et.quadratic_structure F E A
  obtain ⟨hK, -, hst⟩ := hS
  have e1 := hK (A.NL y)
  rw [n, map_mul, hst] at e1
  have e2 := hK (Algebra.trace A.K A.L y)
  rw [t, map_add, hst] at e2
  refine ⟨Prod.ext (i₁ ?_) (i₂ ?_), Prod.ext (i₁ ?_) (i₂ ?_)⟩
  · rw [n₁]; simpa using (congrArg Prod.fst e1).symm
  · rw [n₂]; simpa using (congrArg Prod.snd e1).symm
  · rw [t₁]; simpa using (congrArg Prod.fst e2).symm
  · rw [t₂]; simpa using (congrArg Prod.snd e2).symm

theorem kerL_split [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (ψ : AddChar F ℂ) (x : A.K) (y' y : A.L) :
    A.kerL ψ x y' y = A₁.kerL ψ (eK x).1 (eL y').1 (eL y).1 * A₂.kerL ψ (eK x).2 (eL y').2 (eL y).2 := by
  have h := (splitL A A₁ A₂ eK eL hS (star y' * y)).2
  rw [map_mul eL, hS.2.2] at h
  simp only [Et.kerL, Et.psiK]
  rw [trace_split A A₁ A₂ eK, AddChar.map_add_eq_mul, map_mul, h]
  rfl

theorem psiK_split [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (ψ : AddChar F ℂ) (z x : A.K) (y : A.L) :
    A.psiK ψ (z * x * A.NL y) = A₁.psiK ψ ((eK z).1 * (eK x).1 * A₁.NL (eL y).1) *
      A₂.psiK ψ ((eK z).2 * (eK x).2 * A₂.NL (eL y).2) := by
  simp only [Et.psiK]
  rw [trace_split A A₁ A₂ eK, AddChar.map_add_eq_mul, map_mul, map_mul, (splitL A A₁ A₂ eK eL hS y).1]
  rfl

theorem etaK_split [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (s : A.Kˣ) :
    A.etaK s = A₁.etaK (eK s).1 * A₂.etaK (eK s).2 := by
  have hu : IsUnit (eK (s : A.K)) := s.isUnit.map eK
  have h₁ : Algebra.norm F (eK s).1 ≠ 0 := ((Prod.isUnit_iff.1 hu).1.map (Algebra.norm F)).ne_zero
  have h₂ : Algebra.norm F (eK s).2 ≠ 0 := ((Prod.isUnit_iff.1 hu).2.map (Algebra.norm F)).ne_zero
  simp only [Et.etaK]
  rw [norm_split A A₁ A₂ eK, (GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E).1 _ _ h₁ h₂]

theorem smul_split (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (k : A.K) (y : A.L) :
    eL (k • y) = ((eK k).1 • (eL y).1, (eK k).2 • (eL y).2) := by
  rw [Algebra.smul_def, map_mul, hS.1, Algebra.smul_def, Algebra.smul_def]
  rfl

theorem continuous_kerL [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.K) :
    Continuous (fun p : A.L × A.L => A.kerL ψ x p.1 p.2) := by
  have := U.ultraF; have := U.lcF; have := EtMeas.finite_L A
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  let T : A.L →ₗ[F] F :=
    (Algebra.trace F A.K).comp ((LinearMap.mul F A.K x).comp ((Algebra.trace A.K A.L).restrictScalars F))
  have hT : Continuous T := IsModuleTopology.continuous_of_linearMap T
  have hs : Continuous (star : A.L → A.L) := IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)
  exact (DualLattice.stdChar_continuous hψ).comp (hT.comp ((hs.comp continuous_fst).mul continuous_snd))

theorem tensor_isTestRep : ∀ {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ), IsTestRep W₁ → IsTestRep W₂ →
    IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f →
      (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := GlobalTheory.T.isLocallyConstantTestRepresentation_tensorProduct

theorem fourB_split : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁]
    [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁]
    [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂]
    [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂]
    (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm →
    ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ),
    Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) →
    (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) →
    ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure →
    μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y,
      fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := GlobalTheory.T.fourB_prod_iterated_alt

theorem absK_split : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K),
    A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := GlobalTheory.T.absK_mul_of_etale_splitting

theorem map_nS {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : R) :
    SpecialLinearGroup.map f (nS z) = nS (f z) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [nS]

theorem map_mS {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (s : Rˣ) :
    SpecialLinearGroup.map f (mS s) = mS (Units.map (f : R →* S) s) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [mS]

theorem map_wS {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    SpecialLinearGroup.map f (wS R) = wS S := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [wS]

section rel
variable [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
  (hS : IsSplitting A A₁ A₂ eK eL) (ψ : AddChar F ℂ) (x : A.K)
  (W₁ : SpecialLinearGroup (Fin 2) A₁.K → (A₁.L → ℂ) → A₁.L → ℂ)
  (W₂ : SpecialLinearGroup (Fin 2) A₂.K → (A₂.L → ℂ) → A₂.L → ℂ) (γ₁ γ₂ : ℂ) (μ₁ : Measure A₁.L) (μ₂ : Measure A₂.L)
  (hW₁ : A₁.IsWeil ψ (eK x).1 A₁.etaK μ₁ γ₁ W₁) (hW₂ : A₂.IsWeil ψ (eK x).2 A₂.etaK μ₂ γ₂ W₂)
  (f : A₁.L × A₂.L → ℂ) (hf1 : ∀ u, IsTest (fun v => f (u, v)))
  (hf2 : ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y))
include hS hW₁ hW₂ hf1 hf2

theorem rel_n (z : A.K) (y : A.L) :
    tensorRep W₁ W₂ (nS (eK z).1, nS (eK z).2) f (eL y) = A.psiK ψ (z * x * A.NL y) * f (eL y) := by
  simp only [tensorRep]
  have e2 : (fun u => W₂ (nS (eK z).2) (fun v => f (u, v)) (eL y).2) =
      fun u => A₂.psiK ψ ((eK z).2 * (eK x).2 * A₂.NL (eL y).2) * f (u, (eL y).2) :=
    funext fun u => (hW₂.2 _ (hf1 u)).1 _ _
  have t := hf2 (nS (eK z).2) (eL y).2
  rw [e2] at t ⊢
  rw [(hW₁.2 _ t).1, psiK_split A A₁ A₂ eK eL hS ψ z x y]
  ring

theorem rel_m (s : A.Kˣ) (s₁ : A₁.Kˣ) (s₂ : A₂.Kˣ) (hs₁ : (s₁ : A₁.K) = (eK s).1) (hs₂ : (s₂ : A₂.K) = (eK s).2)
    (y : A.L) :
    tensorRep W₁ W₂ (mS s₁, mS s₂) f (eL y) = A.etaK s * (A.absK s : ℂ) * f (eL ((s : A.K) • y)) := by
  simp only [tensorRep]
  have e2 : (fun u => W₂ (mS s₂) (fun v => f (u, v)) (eL y).2) =
      fun u => A₂.etaK s₂ * (A₂.absK s₂ : ℂ) * f (u, (s₂ : A₂.K) • (eL y).2) :=
    funext fun u => (hW₂.2 _ (hf1 u)).2.1 _ _
  have t := hf2 (mS s₂) (eL y).2
  rw [e2] at t ⊢
  rw [(hW₁.2 _ t).2.1, smul_split A A₁ A₂ eK eL hS, etaK_split A A₁ A₂ eK s,
    absK_split F E A A₁ A₂ eK s, hs₁, hs₂]
  push_cast
  ring

theorem rel_w (y : A.L) :
    tensorRep W₁ W₂ (wS A₁.K, wS A₂.K) f (eL y) = γ₁ * γ₂ *
      ∫ u, (∫ v, f (u, v) * A₂.kerL ψ (eK x).2 v (eL y).2 ∂μ₂) * A₁.kerL ψ (eK x).1 u (eL y).1 ∂μ₁ := by
  simp only [tensorRep]
  have e2 : (fun u => W₂ (wS A₂.K) (fun v => f (u, v)) (eL y).2) =
      fun u => γ₂ * fourB μ₂ (A₂.kerL ψ (eK x).2) (fun v => f (u, v)) (eL y).2 :=
    funext fun u => (hW₂.2 _ (hf1 u)).2.2 _
  have t := hf2 (wS A₂.K) (eL y).2
  rw [e2] at t ⊢
  rw [(hW₁.2 _ t).2.2]
  simp only [fourB, mul_assoc, integral_const_mul]

end rel

theorem weilAt_prod : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L),
    IsSplitting A A₁ A₂ eK eL → WeilAt A₁ → WeilAt A₂ → WeilAt A := by
  intro F E _ _ _ _ U A A₁ A₂ eK eL hS h₁ h₂ ψ hψ x μ hμ
  have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A; have := EtMeas.finite_L A₁; have := EtMeas.finite_L A₂
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₁.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₂.L
  let f₁ : A.K →+* A₁.K := (RingHom.fst A₁.K A₂.K).comp (eK : A.K →+* A₁.K × A₂.K)
  let f₂ : A.K →+* A₂.K := (RingHom.snd A₁.K A₂.K).comp (eK : A.K →+* A₁.K × A₂.K)
  let x₁ : A₁.Kˣ := Units.map (f₁ : A.K →* A₁.K) x
  let x₂ : A₂.Kˣ := Units.map (f₂ : A.K →* A₂.K) x
  obtain ⟨μ₁, hμ₁⟩ := EtMeas.exists_selfDual_L A₁ ψ hψ x₁
  obtain ⟨μ₂, hμ₂⟩ := EtMeas.exists_selfDual_L A₂ ψ hψ x₂
  obtain ⟨γ₁, W₁, hW₁⟩ := h₁ ψ hψ x₁ μ₁ hμ₁
  obtain ⟨γ₂, W₂, hW₂⟩ := h₂ ψ hψ x₂ μ₂ hμ₂
  have hc₁ : Continuous eL := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
  have hc₂ : Continuous eL.symm := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap
  let eH : A.L ≃ₜ A₁.L × A₂.L := ⟨eL.toEquiv, hc₁, hc₂⟩
  obtain ⟨c, hc0, hc⟩ := fourB_split eL.toRingEquiv.toAddEquiv hc₁ hc₂ (A.kerL ψ x) (A₁.kerL ψ x₁)
    (A₂.kerL ψ x₂) (continuous_kerL A₁ ψ hψ _) (continuous_kerL A₂ ψ hψ _)
    (fun y' y => kerL_split A A₁ A₂ eK eL hS ψ x y' y) μ μ₁ μ₂ hμ.1 hμ₁.1 hμ₂.1
  let ρ : SpecialLinearGroup (Fin 2) A.K →* SpecialLinearGroup (Fin 2) A₁.K × SpecialLinearGroup (Fin 2) A₂.K :=
    (SpecialLinearGroup.map f₁).prod (SpecialLinearGroup.map f₂)
  obtain ⟨hT, hfib⟩ := tensor_isTestRep W₁ W₂ hW₁.1 hW₂.1
  refine ⟨γ₁ * γ₂ / c, transRep ρ eH.toEquiv (tensorRep W₁ W₂), isTestRep_transRep ρ eH _ hT, fun φ hφ => ?_⟩
  have hf : IsTest (φ ∘ eH.symm) := isTest_comp_homeomorph eH.symm hφ
  obtain ⟨hf1, hf2⟩ := hfib _ hf
  have hy : ∀ y, eH.symm (eL y) = y := fun y => eL.symm_apply_apply y
  have hx₁ : ((x₁ : A₁.Kˣ) : A₁.K) = (eK x).1 := rfl
  have hx₂ : ((x₂ : A₂.Kˣ) : A₂.K) = (eK x).2 := rfl
  refine ⟨fun z y => ?_, fun s y => ?_, fun y => ?_⟩
  · show tensorRep W₁ W₂ (ρ (nS z)) (φ ∘ eH.symm) (eL y) = _
    have hρ : ρ (nS z) = (nS (eK z).1, nS (eK z).2) := Prod.ext (map_nS f₁ z) (map_nS f₂ z)
    rw [hρ, rel_n A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2]
    simp [hy]
  · show tensorRep W₁ W₂ (ρ (mS s)) (φ ∘ eH.symm) (eL y) = _
    have hρ : ρ (mS s) = (mS (Units.map (f₁ : A.K →* A₁.K) s), mS (Units.map (f₂ : A.K →* A₂.K) s)) :=
      Prod.ext (map_mS f₁ s) (map_mS f₂ s)
    rw [hρ, rel_m A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2 s _ _ rfl rfl]
    simp [hy]
  · show tensorRep W₁ W₂ (ρ (wS A.K)) (φ ∘ eH.symm) (eL y) = _
    have hρ : ρ (wS A.K) = (wS A₁.K, wS A₂.K) := Prod.ext (map_wS f₁) (map_wS f₂)
    rw [hρ, rel_w A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2, hc φ hφ y]
    simp only [Function.comp]
    field_simp
    rfl

end GlobalTheory.JR.WeilProd
end
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_condition_product_splitting : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L), IsSplitting A A₁ A₂ eK eL → WeilAt A₁ → WeilAt A₂ → WeilAt A := by
  atlas_forward_decl GlobalTheory.JR.WeilProd.weilAt_prod
end

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilEtProof

theorem weilAt_of_isField : WeilField → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → WeilAt A := by
  intro hF F E _ _ _ _ _ A hK hL ψ hψ x μ hμ
  have hfacts := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  refine hF F E A hK hL ψ hψ x μ hμ A.etaK (fun s => ⟨?_, fun h => GlobalTheory.T.etaK_eq_neg_one_of_not_norm F E A hK hL s h⟩)
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h1 := hfacts.1 0
    rw [hy, zero_mul] at h1
    have hu : IsUnit (algebraMap A.K A.L s) := s.isUnit.map _
    rw [h1, isUnit_zero_iff] at hu
    obtain ⟨a, b, hab⟩ := hL.exists_pair_ne
    exact hab (by rw [← one_mul a, ← one_mul b, ← hu, zero_mul, zero_mul])
  obtain ⟨b, hb⟩ := hL.mul_inv_cancel hy0
  have := hfacts.2.2.2.1 y (IsUnit.of_mul_eq_one _ hb)
  rwa [hy] at this

end GlobalTheory.JR.WeilEtProof

open GlobalTheory.JR.WeilEtProof in

theorem GlobalTheory.JR.weilEt_of_weilField : WeilField → WeilEt := by
  intro hF F E _ _ _ _ _ A ψ hψ x μ hμ
  suffices h : ∀ (n : ℕ) (A : Et F E), Module.finrank F A.K = n → WeilAt A from h _ A rfl ψ hψ x μ hμ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn
    rcases subsingleton_or_nontrivial A.K with hs | hnt
    · exact GlobalTheory.T.weilRepresentationExistsEtale_of_subsingleton F E A hs
    by_cases hK : IsField A.K
    · by_cases hL : IsField A.L
      · exact weilAt_of_isField hF F E A hK hL
      · intro ψ hψ x μ hμ
        obtain ⟨W, hW⟩ := GlobalTheory.T.exists_weilRepresentation_hyperbolic_split F E A ψ hψ hK hL x μ hμ
        exact ⟨1, W, hW⟩
    · obtain ⟨A₁, A₂, eK, eL, hs, h₁, h₂⟩ := GlobalTheory.T.exists_etaleInvolutiveAlgebraSplitting_smaller F E A hnt hK
      exact GlobalTheory.T.weil_condition_product_splitting F E A A₁ A₂ eK eL hs (ih _ (hn ▸ h₁) A₁ rfl) (ih _ (hn ▸ h₂) A₂ rfl)
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationEtale_of_quadraticField : WeilField → WeilEt := by
  atlas_forward_decl GlobalTheory.JR.weilEt_of_weilField
end

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LatTop

theorem isLocallyConstant_indicator_one' {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem lattice_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)),
    IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧ IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧
      IsTest (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} (1 : A.L → ℂ)) := by
  intro F E _ _ _ _ hU A r j
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  let jF : A.L ≃ₗ[F] (Fin r → E) := j.restrictScalars F
  have hc : Continuous jF := IsModuleTopology.continuous_of_linearMap jF.toLinearMap
  have hcs : Continuous jF.symm := IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap
  set B : Set E := Metric.closedBall 0 1 with hB
  have hBo : IsOpen B := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsClosed B := Metric.isClosed_closedBall
  have hBk : IsCompact B := isCompact_closedBall 0 1
  set V : Set (Fin r → E) := Set.univ.pi fun _ => B with hV
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hBo
  have hVc : IsClosed V := isClosed_set_pi fun _ _ => hBc
  have hVk : IsCompact V := isCompact_univ_pi fun _ => hBk
  have hS : {y : A.L | ∀ i, ‖j y i‖ ≤ 1} = jF ⁻¹' V := by
    ext y
    simp [hV, hB, jF]
  have hS' : jF ⁻¹' V = jF.symm '' V := (jF.toEquiv.image_symm_eq_preimage V).symm
  have hSo : IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := hS ▸ hVo.preimage hc
  have hSc : IsClosed {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := hS ▸ hVc.preimage hc
  have hSk : IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := by
    rw [hS, hS']; exact hVk.image hcs
  exact ⟨hSo, hSk, isLocallyConstant_indicator_one' ⟨hSc, hSo⟩,
    HasCompactSupport.intro' hSk hSc fun x hx => Set.indicator_of_notMem hx _⟩

end GlobalTheory.JR.LatTop
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLattice_isOpen_isCompact_test : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧ IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧ IsTest (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} (1 : A.L → ℂ)) := by
  atlas_forward_decl GlobalTheory.JR.LatTop.lattice_isTest
end

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem Et.kerL_eq_of_isIsom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y' y : A.L, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  intro F E _ _ _ _ _ A ψ x r j hj y' y
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ h2
  haveI : Module.Finite E A.L := Module.Finite.equiv j.symm
  haveI : Module.Free E A.L := Module.Free.of_equiv j.symm
  have hb : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  haveI : Module.Free A.K A.L := Module.Free.of_equiv hb.equiv
  haveI : Module.Finite A.K A.L := Module.Finite.equiv hb.equiv
  rw [hj y' y]
  unfold Et.kerL Et.psiK
  congr 1
  rw [← Algebra.smul_def, smul_mul_assoc, Algebra.trace_trace (R := F) (S := E), ← smul_eq_mul,
    ← LinearMap.map_smul, Algebra.trace_trace]
end GlobalTheory.JR
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kerL_eq_trace_dotProduct_of_isIsom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y' y : A.L, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  atlas_forward_decl GlobalTheory.JR.Et.kerL_eq_of_isIsom
end

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.NormInt

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem traceE [U : Unram F E] (z : E) : algebraMap F E (Algebra.trace F E z) = z + star z := by
  have := U.charZero
  obtain ⟨b, d, hb0, hs, hd, hd0⟩ := Unram.exists_basis_antifixed F E
  have h2 := (IsUnit.mk0 (2 : F) two_ne_zero)
  exact (quadratic_star_structure b d hb0 hs hd U.star_fix (IsUnit.mk0 d hd0) h2).2.2.1 z

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y : A.L, (∀ i, ‖j y i‖ ≤ 1) → A.psiK ψ (x * A.NL y) = 1 := by
  intro F E _ _ _ _ U A ψ hψ x r j hj y hy
  have := U.charZero
  have := U.ultraE
  have hE2 : Module.Finite F E := Module.finite_of_finrank_pos (by rw [U.finrank_eq]; norm_num)
  obtain ⟨⟨c⟩, hinj, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have : Module.Free A.K A.L := Module.Free.of_basis c
  have : Module.Finite A.K A.L := Module.Finite.of_basis c
  have : Module.Free E A.L := Module.Free.of_basis (A.push.out.basis (Module.Free.chooseBasis F A.K))
  have : Module.Finite E A.L := Module.Finite.of_basis (A.push.out.basis (Module.Free.chooseBasis F A.K))
  set s : E := star (j y) ⬝ᵥ j y with hs_def

  have hs1 : ‖s‖ ≤ 1 := by
    rw [hs_def, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [Pi.star_apply, norm_mul, U.norm_star]
    exact mul_le_one₀ (hy i) (norm_nonneg _) (hy i)

  have hss : star s = s := by
    rw [hs_def, dotProduct, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, star_mul', star_star, mul_comm]
  have hsL : s = Algebra.trace E A.L (algebraMap A.K A.L x * star y * y) := hj y y
  set T : F := Algebra.trace F A.K (x * A.NL y) with hT
  have hz : algebraMap A.K A.L (x * A.NL y) = algebraMap A.K A.L x * star y * y := by
    rw [map_mul, hN, mul_assoc, mul_comm y]
  have htK : ∀ k : A.K, Algebra.trace A.K A.L (algebraMap A.K A.L k) = 2 • k := by
    intro k
    apply hinj
    rw [htr, A.star_K, map_nsmul, two_nsmul]
  have h1 : Algebra.trace F A.L (algebraMap A.K A.L (x * A.NL y)) = 2 • T := by
    rw [← Algebra.trace_trace (S := A.K), htK, map_nsmul]
  have h2 : Algebra.trace F A.L (algebraMap A.K A.L (x * A.NL y)) = Algebra.trace F E s := by
    rw [← Algebra.trace_trace (S := E), hz, hsL]
  have h3 : algebraMap F E T = s := by
    have e := congrArg (algebraMap F E) (h1.symm.trans h2)
    rw [traceE, hss, map_nsmul, two_nsmul, ← two_mul, ← two_mul] at e
    have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
    have h20 : (2 : E) ≠ 0 := two_ne_zero
    exact mul_left_cancel₀ h20 e
  have hT1 : ‖T‖ ≤ 1 := by rw [← norm_algebraMap' E T, h3]; exact hs1
  exact hψ.1 T hT1

end GlobalTheory.JR.NormInt
end
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiK_mul_NL_eq_one_on_integral_lattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y : A.L, (∀ i, ‖j y i‖ ≤ 1) → A.psiK ψ (x * A.NL y) = 1 := by
  atlas_forward_decl GlobalTheory.JR.NormInt.main
end

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourB_indicator_intLattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) (B : A.L → A.L → ℂ), (∀ y' y, B y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) → IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → ∀ μ : Measure A.L, μ.IsAddHaarMeasure → ∀ y, fourB μ B (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1) y = ((μ {y : A.L | ∀ i, ‖j y i‖ ≤ 1}).toReal : ℂ) * Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1 y := by
  intro F E _ _ _ _ hU A ψ hψ r j B hB hO _hC μ hμ y
  haveI := hU.ultraE
  set Λ : Set A.L := {y : A.L | ∀ i, ‖j y i‖ ≤ 1} with hΛ
  have key : ∀ z : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * z)) = 1) ↔ ‖z‖ ≤ 1 :=
    ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2
  have hmem_add : ∀ a x, a ∈ Λ → (a + x ∈ Λ ↔ x ∈ Λ) := by
    intro a x ha
    constructor
    · intro h i
      have e1 : j x i = j (a + x) i + -(j a i) := by simp
      rw [e1]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h i) (by rw [norm_neg]; exact ha i))
    · intro h i
      rw [map_add, Pi.add_apply]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (h i))
  have hBadd : ∀ a x, B (a + x) y = B a y * B x y := by
    intro a x
    rw [hB, hB, hB, map_add, star_add, add_dotProduct, map_add, AddChar.map_add_eq_mul]
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  unfold fourB
  by_cases hy : y ∈ Λ
  · have h1 : ∀ x, Set.indicator Λ 1 x * B x y = Set.indicator Λ (fun _ => (1:ℂ)) x := by
      intro x
      by_cases hx : x ∈ Λ
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul, hB]
        simp only [dotProduct, Pi.star_apply, map_sum]
        refine Finset.sum_induction _ (fun t => ψ t = 1) (fun u v hu hv => by
          rw [AddChar.map_add_eq_mul, hu, hv, one_mul]) (AddChar.map_zero_eq_one ψ) fun i _ => ?_
        exact (key (j y i)).2 (hy i) _ (by rw [hU.norm_star]; exact hx i)
      · simp [hx]
    simp_rw [h1]
    rw [integral_indicator_const _ hO.measurableSet, Set.indicator_of_mem hy, Pi.one_apply, mul_one]
    simp [Measure.real]
  · obtain ⟨i, hi⟩ : ∃ i, ¬ ‖j y i‖ ≤ 1 := by
      by_contra h
      push_neg at h
      exact hy h
    obtain ⟨e, he, hne⟩ : ∃ e : E, ‖e‖ ≤ 1 ∧ ψ (Algebra.trace F E (e * j y i)) ≠ 1 := by
      by_contra h
      push_neg at h
      exact hi ((key _).1 h)
    set a := j.symm (Pi.single i (star e)) with ha_def
    have hja : j a = Pi.single i (star e) := by simp [ha_def]
    have ha : a ∈ Λ := by
      intro k
      rw [hja]
      by_cases hk : k = i
      · subst hk; simp [hU.norm_star, he]
      · simp [Pi.single_eq_of_ne hk]
    have hst : star (Pi.single i (star e) : Fin r → E) = Pi.single i e := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    have hBa : B a y = ψ (Algebra.trace F E (e * j y i)) := by
      rw [hB, hja, hst, single_dotProduct]
    have hint : ∫ x, Set.indicator Λ 1 x * B x y ∂μ = B a y * ∫ x, Set.indicator Λ 1 x * B x y ∂μ := by
      rw [← integral_const_mul]
      calc ∫ x, Set.indicator Λ 1 x * B x y ∂μ
          = ∫ x, Set.indicator Λ 1 (a + x) * B (a + x) y ∂μ :=
            (integral_add_left_eq_self (fun x => Set.indicator Λ 1 x * B x y) a).symm
        _ = ∫ x, B a y * (Set.indicator Λ 1 x * B x y) ∂μ := by
            congr 1; ext x
            rw [hBadd]
            by_cases hx : x ∈ Λ
            · rw [Set.indicator_of_mem ((hmem_add a x ha).2 hx), Set.indicator_of_mem hx, Pi.one_apply, Pi.one_apply]; ring
            · have hx' : a + x ∉ Λ := fun h => hx ((hmem_add a x ha).1 h)
              simp [hx, hx']
    have h0 : ∫ x, Set.indicator Λ 1 x * B x y ∂μ = 0 := by
      have : (1 - B a y) * ∫ x, Set.indicator Λ 1 x * B x y ∂μ = 0 := by
        rw [sub_mul, one_mul, ← hint, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by rw [hBa] at h; exact (sub_eq_zero.1 h).symm) hne
      · exact h
    rw [h0]
    simp [hy]

end GlobalTheory.JR
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_indicator_hermitianIntegralLattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) (B : A.L → A.L → ℂ), (∀ y' y, B y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) → IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → ∀ μ : Measure A.L, μ.IsAddHaarMeasure → ∀ y, fourB μ B (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1) y = ((μ {y : A.L | ∀ i, ‖j y i‖ ≤ 1}).toReal : ℂ) * Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1 y := by
  atlas_forward_decl GlobalTheory.JR.fourB_indicator_intLattice
end

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.GammaOneProof

theorem wS_pow_four (k : Type) [CommRing k] : wS k ^ 4 = 1 := by
  have h : ((wS k : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_fin_two]

theorem wn_pow_three (k : Type) [CommRing k] : (wS k * nS 1) ^ 3 = 1 := by
  have h : ((wS k * nS 1 : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![0, 1; -1, 0] * !![1, 1; 0, 1] := rfl
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_fin_two]

theorem rep_smul {G X : Type} [Group G] [TopologicalSpace X] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W)
    (g : G) (c : ℂ) {f : X → ℂ} (hf : IsTest f) : W g (c • f) = c • W g f := by
  have h0 : IsTest (0 : X → ℂ) := ⟨IsLocallyConstant.const (0 : ℂ), HasCompactSupport.zero⟩
  have hz : W g 0 = 0 := by
    have := hW.2.2.2 g 1 0 0 h0 h0
    simpa using this
  have := hW.2.2.2 g c f 0 hf h0
  simpa [hz] using this

end GlobalTheory.GammaOneProof

open GlobalTheory.GammaOneProof in

theorem GlobalTheory.JR.gammaOne_holds : GammaOne := by
  intro F E _ _ _ _ _ A ψ hψ x μ hsd ω γ W hW r j hj
  obtain ⟨hΛo, hΛc, hT⟩ := GlobalTheory.T.hermitianLattice_isOpen_isCompact_test F E A r j
  have hN := GlobalTheory.T.psiK_mul_NL_eq_one_on_integral_lattice F E A ψ hψ (x : A.K) r j hj
  have hFour := GlobalTheory.T.fourier_indicator_hermitianIntegralLattice F E A ψ hψ r j (A.kerL ψ x) (GlobalTheory.T.kerL_eq_trace_dotProduct_of_isIsom F E A ψ (x : A.K) r j hj) hΛo hΛc μ hsd.1
  set Λ : Set A.L := {y : A.L | ∀ i, ‖j y i‖ ≤ 1} with hΛ
  set φ0 : A.L → ℂ := Set.indicator Λ 1 with hφ0
  have h0 : (0 : A.L) ∈ Λ := by simp [hΛ]
  have hφ00 : φ0 0 = 1 := by simp [hφ0, Set.indicator_of_mem h0]
  have hc : (((μ Λ).toReal : ℝ) : ℂ) = 1 := by
    have h2 := hsd.2 φ0 hT 0
    have hfe : fourB μ (A.kerL ψ x) φ0 = fun y => (((μ Λ).toReal : ℝ) : ℂ) * φ0 y := funext hFour
    rw [hfe] at h2
    have hl : fourB μ (A.kerL ψ x) (fun y => (((μ Λ).toReal : ℝ) : ℂ) * φ0 y) 0
        = (((μ Λ).toReal : ℝ) : ℂ) * fourB μ (A.kerL ψ x) φ0 0 := by
      simp only [fourB, mul_assoc]; exact integral_const_mul _ _
    rw [hl, hFour, neg_zero, hφ00, mul_one] at h2
    have hr : (μ Λ).toReal * (μ Λ).toReal = 1 := by exact_mod_cast h2
    have hnn : 0 ≤ (μ Λ).toReal := ENNReal.toReal_nonneg
    have : (μ Λ).toReal = 1 := by nlinarith
    rw [this]; simp
  obtain ⟨hrep, hrel⟩ := hW
  obtain ⟨hn, -, hw⟩ := hrel φ0 hT
  have hWw : W (wS A.K) φ0 = γ • φ0 := by
    funext y; rw [hw y, hFour y, hc]; simp
  have hWn : W (nS 1) φ0 = φ0 := by
    funext y; rw [hn 1 y]
    by_cases hy : y ∈ Λ
    · rw [one_mul, hN y hy, one_mul]
    · simp [hφ0, Set.indicator_of_notMem hy]
  have hWwn : W (wS A.K * nS 1) φ0 = γ • φ0 := by rw [hrep.2.2.1 _ _ _ hT, hWn, hWw]
  have hpow : ∀ (g : SpecialLinearGroup (Fin 2) A.K) (c : ℂ), W g φ0 = c • φ0 → ∀ k : ℕ, W (g ^ k) φ0 = c ^ k • φ0 := by
    intro g c hg k
    induction k with
    | zero => simp [hrep.2.1 φ0 hT]
    | succ k ih => rw [pow_succ', hrep.2.2.1 _ _ _ hT, ih, rep_smul hrep _ _ hT, hg, smul_smul, pow_succ]
  have e4 := congrFun (hpow _ _ hWw 4) 0
  rw [wS_pow_four, hrep.2.1 φ0 hT] at e4
  have e3 := congrFun (hpow _ _ hWwn 3) 0
  rw [wn_pow_three, hrep.2.1 φ0 hT] at e3
  simp only [Pi.smul_apply, smul_eq_mul, hφ00, mul_one] at e4 e3
  have : γ ^ 4 = γ ^ 3 * γ := pow_succ _ _
  rw [← e4, ← e3, one_mul] at this
  exact this.symm
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilConstantStandardHermitian_eq_one : GammaOne := by
  atlas_forward_decl GlobalTheory.JR.gammaOne_holds
end

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourierMatch_of_weilField : WeilField → ∀ r, FourierMatch r := fun h =>
  GlobalTheory.T.jacquetRallisFourierMatch_of_weilRepresentation (GlobalTheory.T.weilRepresentationEtale_of_quadraticField h) GlobalTheory.T.etaleOrbitalFourier_rankOne_transfer GlobalTheory.T.weilConstantStandardHermitian_eq_one

end GlobalTheory.JR
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_fourier_matching_of_weil_field : WeilField → ∀ r, FourierMatch r := by
  atlas_forward_decl GlobalTheory.JR.fourierMatch_of_weilField
end

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.SizeOne

theorem eta_one' {F : Type} [NormedField F] : eta (1 : F) = 1 := by
  unfold eta
  rw [if_pos ⟨1, by simp⟩]

theorem unitMatch_zero : UnitMatch 0 := by
  intro F E _ _ _ _ _ M a _
  letI := M.mG; letI := M.mU
  have hG : M.μG Set.univ = 1 := by
    rw [← M.volG]; congr 1; ext g; simp [glO]
  have hU : M.μU Set.univ = 1 := by
    rw [← M.volU]; congr 1; ext g; simp [uO]
  have hw : ∀ Y : Gl 0 F, omega Y = 1 := by
    intro Y
    have : lastDet Y = 1 := by simp [lastDet, Fin.last]
    rw [omega, this, eta_one']
  refine ⟨fun X hX => ?_, fun hn => (hn ⟨(0, 0, a.2.2), ?_⟩).elim⟩
  · have hl : X.2.2 = a.2.2 := (algebraMap F E).injective (congrArg (fun t => t.2.2) hX)
    by_cases hb : ‖a.2.2‖ ≤ 1 <;>
      simp [orbG, orbU, hw, unitG, unitU, act, actU, sec, Set.indicator, hl, hb, Measure.real, hG, hU]
  · exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)

end GlobalTheory.JR.SizeOne
end
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_sizeOne : UnitMatch 0 := by
  atlas_forward_decl GlobalTheory.JR.SizeOne.unitMatch_zero
end

section
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_of_weilField : WeilField → ∀ r, UnitMatch r := by
  intro hW r
  induction r with
  | zero => exact GlobalTheory.T.jacquetRallisUnitMatch_sizeOne
  | succ r ih => exact GlobalTheory.T.jacquetRallisUnitMatch_succ (GlobalTheory.T.weilRepresentationEtale_of_quadraticField hW) GlobalTheory.T.weilConstantStandardHermitian_eq_one r (GlobalTheory.T.jacquetRallis_fourier_matching_of_weil_field hW (r + 1)) ih

end GlobalTheory.JR
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic : WeilField → ∀ r, UnitMatch r := by
  atlas_forward_decl GlobalTheory.JR.unitMatch_of_weilField
end
