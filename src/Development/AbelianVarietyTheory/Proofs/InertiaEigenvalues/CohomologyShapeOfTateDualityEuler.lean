import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1H2Local
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteResidueFieldOfCompactIsAdicDvr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotKilledByPowUniformizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotDivisibleByUniformizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCardTorsionLevelFractionRingQuotStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH0LevelRepEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCardH0H1Eq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContActionTorsionLevelZModOfIsLocallyConstant
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPowMovesPadicRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPowNeOneOfMovesRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCardTorsionLevelFractionRingQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2BoundedTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LevelRepOneLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivFractionRingQuotPiProdFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HcLCExistsPowSmulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LevelRepFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionShapeOfTorsionCounts

section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_residueField_of_compact_isAdic_dvr : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) →
    Finite (IsLocalRing.ResidueField O) := by
  first | exact @GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic | exact GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic | (intros; apply GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic <;> assumption)
end

section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRingQuot_killed_by_pow_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  first | exact @GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer | exact GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer | (intros; apply GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer <;> assumption)
end

section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRingQuot_divisible_by_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ y : Formalism.NG.KO O, ϖ • y = x := by
  first | exact @GlobalTheory.KO_divisible_by_uniformiser | exact GlobalTheory.KO_divisible_by_uniformiser | (intros; apply GlobalTheory.KO_divisible_by_uniformiser <;> assumption)
end

section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transfer_card_H0_H1_eq : ∀ {O : Type} [CommRing O] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (i : G ≃ₜ* G') {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M)
    (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) ∧
      Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  first | exact @GlobalTheory.ShapeNeg.transfer_card_H0_H1 | exact GlobalTheory.ShapeNeg.transfer_card_H0_H1 | (intros; apply GlobalTheory.ShapeNeg.transfer_card_H0_H1 <;> assumption)
end

section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contAction_torsionLevelZMod_of_isLocallyConstant : ∀ {G : Type} [Group G] [TopologicalSpace G] {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    (∀ m : M, c • m = 0 → IsLocallyConstant (fun g => ρ g m)) →
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p r h ρ) := by
  first | exact @GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant | exact GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant | (intros; apply GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant <;> assumption)
end

section
section
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem cyclotomic_isLocallyConstant_mod {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O]
    (ε : Formalism.GaloisCohomology.GK p K →* Oˣ) (hε : ∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) (N : ℕ) :
    IsLocallyConstant (fun σ : Formalism.GaloisCohomology.GK p K => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O)) := by
  have hp : p.Prime := Fact.out
  have hne : ((p ^ N : ℕ) : PadicAlgCl p) ≠ 0 := by exact_mod_cast pow_ne_zero N hp.ne_zero
  haveI : NeZero ((p ^ N : ℕ) : PadicAlgCl p) := ⟨hne⟩
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ N)
  have hint : IsIntegral K ζ := (hζ.isIntegral (pow_pos hp.pos N)).tower_top
  haveI : FiniteDimensional K (IntermediateField.adjoin K {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hU : IsOpen ((IntermediateField.adjoin K {ζ}).fixingSubgroup : Set (Formalism.GaloisCohomology.GK p K)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have key : ∀ σ τ : Formalism.GaloisCohomology.GK p K, σ ζ = τ ζ →
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O) =
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε τ : Oˣ) : O) := by
    intro σ τ h
    obtain ⟨a, ha, ha'⟩ := hε σ N ζ hζ.pow_eq_one
    obtain ⟨b, hb, hb'⟩ := hε τ N ζ hζ.pow_eq_one
    have hab : ζ ^ a = ζ ^ b := by rw [← ha, ← hb, h]
    have hmod : a ≡ b [MOD p ^ N] := by
      rw [hζ.eq_orderOf]
      exact (hζ.isOfFinOrder (pow_ne_zero N hp.ne_zero)).pow_eq_pow_iff_modEq.1 hab
    obtain ⟨c, hc⟩ := hmod.dvd
    have hc' : (b : O) - (a : O) = (p : O) ^ N * (c : O) := by
      have := congrArg (Int.cast : ℤ → O) hc
      push_cast at this
      exact this
    rw [Ideal.Quotient.eq]
    have e : ((ε σ : Oˣ) : O) - ((ε τ : Oˣ) : O) =
        (((ε σ : Oˣ) : O) - a) - (((ε τ : Oˣ) : O) - b) - ((b : O) - a) := by ring
    rw [e, hc']
    exact Ideal.sub_mem _ (Ideal.sub_mem _ ha' hb')
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  rw [IsLocallyConstant.iff_exists_open]
  intro σ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' ((IntermediateField.adjoin K {ζ}).fixingSubgroup : Set (Formalism.GaloisCohomology.GK p K)),
    hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro τ hτ
    apply key
    have h1 : (σ⁻¹ * τ) ζ = ζ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ ζ (IntermediateField.mem_adjoin_simple_self K ζ)
    have h2 := congrArg σ h1
    simpa using h2

end GlobalTheory.ShapeNeg
end

open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_character_isLocallyConstant_mod_pow : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O]
    (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ N : ℕ,
    IsLocallyConstant (fun σ : Formalism.GaloisCohomology.GK p K => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O)) := by
  atlas_forward_decl GlobalTheory.ShapeNeg.cyclotomic_isLocallyConstant_mod
end

section
section
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem isLocallyConstant_orbit_of_inv_pow_character :
    ∀ {p : ℕ} {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ),
    (∀ N : ℕ, IsLocallyConstant (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O))) →
    ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ (m : M) (N : ℕ), (p : O) ^ N • m = 0 →
    IsLocallyConstant (fun g => ρ g m) := by
  intro p O _ G _ _ ε hε e M _ _ ρ hρ m N hm
  have key : ∀ g g' : G,
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O) =
        Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g' : Oˣ) : O) → ρ g m = ρ g' m := by
    intro g g' h
    have h1 : Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) (((ε g) ^ e : Oˣ) : O) =
        Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) (((ε g') ^ e : Oˣ) : O) := by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow, h]
    rw [hρ, hρ]
    generalize (ε g) ^ e = u at h1 ⊢
    generalize (ε g') ^ e = v at h1 ⊢
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
    have h2 : ((v⁻¹ : Oˣ) : O) - ((u⁻¹ : Oˣ) : O) =
        (((u⁻¹ : Oˣ) : O) * ((v⁻¹ : Oˣ) : O) * b) * (p : O) ^ N := by
      rw [mul_assoc, hb]
      have hu : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := u.inv_mul
      have hv : ((v⁻¹ : Oˣ) : O) * (v : O) = 1 := v.inv_mul
      linear_combination (-((v⁻¹ : Oˣ) : O)) * hu + ((u⁻¹ : Oˣ) : O) * hv
    symm
    rw [← sub_eq_zero, ← sub_smul, h2, mul_smul, hm, smul_zero]
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  obtain ⟨U, hU, hg, hc⟩ := ((IsLocallyConstant.iff_exists_open _).1 (hε N)) g₀
  exact ⟨U, hU, hg, fun g hgU => key g g₀ (hc g hgU)⟩

end GlobalTheory.ShapeNeg
end

open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_orbit_of_inv_pow_character' : ∀ {p : ℕ} {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ),
    (∀ N : ℕ, IsLocallyConstant (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O))) →
    ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ (m : M) (N : ℕ), (p : O) ^ N • m = 0 →
    IsLocallyConstant (fun g => ρ g m) := by
  atlas_forward_decl GlobalTheory.ShapeNeg.isLocallyConstant_orbit_of_inv_pow_character
end

section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K →
    ∀ k : ℕ, 0 < k → ∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ := by
  first | exact @GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity | exact GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity | (intros; apply GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity <;> assumption)
end

section
section
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem finite_invariants_of_smul_ne_one : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ {G : Type} [Group G]
    (ρ : Representation O G M) (g : G) (a : O), a ≠ 1 → (∀ m, ρ g m = a • m) → Finite ρ.invariants := by
  intro O _ _ _ _ M _ _ e G _ ρ g a ha hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hb : a - 1 ≠ 0 := sub_ne_zero.2 ha
  obtain ⟨c, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  have hkill : ∀ m : ρ.invariants, ϖ ^ c • (m : M) = 0 := by
    intro m
    have hm : ρ g (m : M) = m := (Representation.mem_invariants ρ (m : M)).1 m.2 g
    have h1 : (a - 1) • (m : M) = 0 := by
      rw [sub_smul, one_smul, ← hg, hm, sub_self]
    rw [hu, mul_smul] at h1
    have h2 := congrArg (fun x : M => ((u⁻¹ : Oˣ) : O) • x) h1
    simp only [smul_zero, smul_smul] at h2
    rwa [← mul_assoc, Units.inv_mul, one_mul] at h2
  haveI := (lev_pow_card hϖ e c).1
  refine Finite.of_injective (fun m : ρ.invariants => (Lev.mk (m : M) (hkill m) : Lev M (ϖ ^ c))) ?_
  intro x y hxy
  have := congrArg Lev.val hxy
  simp only [Lev.val_mk] at this
  exact Subtype.ext this

end GlobalTheory.ShapeNeg
end

open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_invariants_of_scalar_ne_one_twist : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ {G : Type} [Group G]
    (ρ : Representation O G M) (g : G) (a : O), a ≠ 1 → (∀ m, ρ g m = a • m) → Finite ρ.invariants := by
  atlas_forward_decl GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one
end

section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h2_bounded_twist : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ σ₀ : Formalism.GaloisCohomology.GK p K, ε σ₀ ^ (e + 1) ≠ 1 →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  first | exact @GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic | exact GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic | (intros; apply GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic <;> assumption)
end

section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_H2_level_rep_one_le : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M)
    (h : ((p : O) ^ 1) ∈ Ideal.span {ϖ ^ 1}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p 1 h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ) →
    Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ)) ≤ Nat.card (IsLocalRing.ResidueField O) := by
  first | exact @GlobalTheory.ShapeNeg.card_H2_level_rep_le | exact GlobalTheory.ShapeNeg.card_H2_level_rep_le | (intros; apply GlobalTheory.ShapeNeg.card_H2_level_rep_le <;> assumption)
end

section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_fractionRingQuot_pi_prod_finite : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ {Y : Type} [AddCommGroup Y] [Module O Y], (∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) →
    Finite (LinearMap.ker (ϖ • LinearMap.id : Y →ₗ[O] Y)) →
    ∃ (a : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Module O F), Finite F ∧ Nonempty (Y ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) := by
  first | exact @GlobalTheory.CofinGen.exists_equiv_pi_prod_finite | exact GlobalTheory.CofinGen.exists_equiv_pi_prod_finite | (intros; apply GlobalTheory.CofinGen.exists_equiv_pi_prod_finite <;> assumption)
end

section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_zero_of_mem_HcLC_of_torsion : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O),
    (∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0) → ∀ x ∈ ReciprocityTheory.ChartRestriction.T2.HcLC ρ, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  first | exact @GlobalTheory.hcLC_exists_pow_smul_eq_zero | exact GlobalTheory.hcLC_exists_pow_smul_eq_zero | (intros; apply GlobalTheory.hcLC_exists_pow_smul_eq_zero <;> assumption)
end

section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_H1_level_rep_formula : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O) (n : ℕ),
    (∀ m : M, ∃ m' : M, ϖ • m' = m) → (∀ m : M, IsLocallyConstant (fun g => ρ g m)) →
    Finite (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) →
    Finite (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) ∧
    Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) =
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) *
      Nat.card (ρ.invariants ⧸ LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  first | exact @GlobalTheory.ShapeNeg.SeqCount.card_H1_level_rep_eq | exact GlobalTheory.ShapeNeg.SeqCount.card_H1_level_rep_eq | (intros; apply GlobalTheory.ShapeNeg.SeqCount.card_H1_level_rep_eq <;> assumption)
end

section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_shape_of_torsion_counts : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {ϖ : O}, Irreducible ϖ → ∀ {X : Type} [AddCommGroup X] [Module O X] (Hc : Submodule O X) (d a : ℕ)
    {F : Type} [AddCommGroup F] [Module O F] [Finite F], (Hc ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) →
    (∃ C : ℕ, ∀ n : ℕ, 0 < n →
      Nat.card (IsLocalRing.ResidueField O) ^ (n * d) ≤ Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Hc →ₗ[O] Hc)) ∧
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Hc →ₗ[O] Hc)) ≤ C * Nat.card (IsLocalRing.ResidueField O) ^ (n * d)) →
    Nat.card (LinearMap.ker (ϖ ^ 1 • LinearMap.id : Hc →ₗ[O] Hc)) ≤ Nat.card (IsLocalRing.ResidueField O) ^ (d + 1) →
    Formalism.RepresentationBoundsCohomology.JT.QuotShape Hc ⊥ d := by
  first | exact @GlobalTheory.ShapeNeg.Shape.quotShape_of_counts | exact GlobalTheory.ShapeNeg.Shape.quotShape_of_counts | (intros; apply GlobalTheory.ShapeNeg.Shape.quotShape_of_counts <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.ShapeNeg

open Formalism.NG Formalism.RepresentationBoundsCohomology.JT ReciprocityTheory.Gal

theorem shapeG_of_localDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) :
    ReciprocityTheory.ChartRestriction.T2.ShapeG := by
  intro p _ K O _ _ _ _ _ _ _ G _ _ hK hO hF i ε hcyc e he M _ _ u ρ hρ
  haveI := hO.ring
  haveI := hO.compact
  haveI : CompactSpace G := i.symm.toHomeomorph.compactSpace
  haveI hres : Finite (IsLocalRing.ResidueField O) := GlobalTheory.T.finite_residueField_of_compact_isAdic_dvr hO.adic
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpϖ : (p : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]; exact hO.p_mem
  have hpn : ∀ n : ℕ, ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n} := fun n => by
    rw [← Ideal.span_singleton_pow]; exact Ideal.pow_mem_pow hpϖ n
  set q := Nat.card (IsLocalRing.ResidueField O) with hq
  set d := Module.finrank ℚ_[p] K with hd
  set ε' : Formalism.GaloisCohomology.GK p K →* Oˣ := ε.comp i.symm.toMulEquiv.toMonoidHom with hε'
  have hcyc' : ∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε') g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n} := hcyc
  have hlcε : ∀ N : ℕ, IsLocallyConstant
      (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O)) := by
    intro N
    have h := (GlobalTheory.T.cyclotomic_character_isLocallyConstant_mod_pow ε' hcyc' N).comp_continuous i.continuous
    convert h using 1
    funext g
    simp only [Function.comp_apply, ε', MonoidHom.comp_apply]
    first
      | rfl
      | (congr 3; exact (i.symm_apply_apply g).symm)
      | simp
  have hMt : ∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0 := fun m => by
    obtain ⟨n, hn⟩ := GlobalTheory.T.fractionRingQuot_killed_by_pow_uniformizer hϖ (u m)
    exact ⟨n, u.injective (by rw [map_smul, hn, map_zero])⟩
  have hMp : ∀ m : M, ∃ N : ℕ, (p : O) ^ N • m = 0 := fun m => by
    obtain ⟨n, hn⟩ := hMt m
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hpn n)
    exact ⟨n, by rw [← hb, mul_smul, hn, smul_zero]⟩
  have hdiv : ∀ m : M, ∃ m' : M, ϖ • m' = m := fun m => by
    obtain ⟨y, hy⟩ := GlobalTheory.T.fractionRingQuot_divisible_by_uniformizer hϖ (u m)
    exact ⟨u.symm y, u.injective (by rw [map_smul, LinearEquiv.apply_symm_apply, hy])⟩
  have hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m) := fun m => by
    obtain ⟨N, hN⟩ := hMp m
    exact GlobalTheory.T.isLocallyConstant_orbit_of_inv_pow_character' ε hlcε e ρ hρ m N hN
  set ρ' : Representation O (Formalism.GaloisCohomology.GK p K) M := ρ.comp i.symm.toMulEquiv.toMonoidHom with hρ'def
  have hρ' : ∀ g m, ρ' g m = ((((ε' g) ^ e)⁻¹ : Oˣ) : O) • m := fun g m => hρ _ m
  have hcont : ∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ') := fun n h =>
    GlobalTheory.T.contAction_torsionLevelZMod_of_isLocallyConstant ρ' p n (ϖ ^ n) h (fun m _ => (hlc m).comp_continuous i.symm.continuous)
  obtain ⟨σ1, hσ1⟩ := GlobalTheory.T.cyclotomic_character_pow_ne_one_of_moves_root hO.p_mem hO.p_ne ε' hcyc' e (GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity hK e he)
  obtain ⟨σ2, hσ2⟩ := GlobalTheory.T.cyclotomic_character_pow_ne_one_of_moves_root hO.p_mem hO.p_ne ε' hcyc' (e + 1) (GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity hK (e + 1) (Nat.succ_pos e))
  have hNfin : Finite ρ.invariants := by
    refine GlobalTheory.T.finite_invariants_of_scalar_ne_one_twist u ρ (i.symm σ1) ((((ε (i.symm σ1)) ^ e)⁻¹ : Oˣ) : O) ?_ (hρ _)
    intro h1
    apply hσ1
    have h2 : ((ε (i.symm σ1)) ^ e)⁻¹ = 1 := Units.ext h1
    exact inv_eq_one.1 h2
  obtain ⟨C, hC⟩ := GlobalTheory.T.h2_bounded_twist hT hK hϖ hpϖ ε' hcyc' e u ρ' hρ' σ2 hσ2 hcont
  have hone2 := GlobalTheory.T.card_H2_level_rep_one_le hT hK hϖ u ρ' (hpn 1) (hcont 1 (hpn 1))
  have key : ∀ n : ℕ, 0 < n →
      Finite (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) ∧
      (letI := GlobalTheory.ShapeNeg.levZ (M := M) p n (hpn n)
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) =
        Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ')) * q ^ (n * d)) := by
    intro n hn
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p n (hpn n)
    obtain ⟨hLf, hLc⟩ := GlobalTheory.T.finite_card_torsionLevel_fractionRingQuot hϖ u n
    obtain ⟨hH1f, -⟩ := GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK n (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n))
      (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ') hn (hcont n (hpn n))
    have hEu := hE p K hK n (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ') hn
      (hcont n (hpn n))
    obtain ⟨t0, t1⟩ := GlobalTheory.T.transfer_card_H0_H1_eq i ρ p n (ϖ ^ n) (hpn n)
    have hH1O : Finite (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) :=
      Nat.finite_of_card_ne_zero (by rw [t1]; exact Nat.card_pos.ne')
    obtain ⟨hXf, hX⟩ := GlobalTheory.T.card_H1_level_rep_formula ρ ϖ n hdiv hlc hH1O
    have h0c := GlobalTheory.T.card_H0_level_rep_eq ρ (ϖ ^ n) hNfin
    set Nq := Nat.card (ρ.invariants ⧸
      LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) with hNq
    haveI : Finite (ρ.invariants ⧸
        LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) :=
      Finite.of_surjective _ (Submodule.mkQ_surjective _)
    have hpos : 0 < Nq := Nat.card_pos
    refine ⟨hXf, ?_⟩
    have e1 : Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) * Nq =
        (Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ')) * q ^ (n * d)) * Nq := by
      rw [← hX, t1, hEu, ← t0, h0c, hLc, ← pow_mul]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos e1
  have htors := GlobalTheory.T.exists_pow_smul_eq_zero_of_mem_HcLC_of_torsion ρ ϖ hMt
  have hfin1 : Finite (LinearMap.ker (ϖ • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) := by
    have h1 := (key 1 one_pos).1
    simpa only [pow_one] using h1
  obtain ⟨a, F, _, _, hFf, ⟨φ⟩⟩ := GlobalTheory.T.exists_equiv_fractionRingQuot_pi_prod_finite hϖ (Y := ReciprocityTheory.ChartRestriction.T2.HcLC ρ)
    (fun y => (htors y.1 y.2).imp fun n hn => Subtype.ext (by simpa using hn)) hfin1
  haveI := hFf
  refine GlobalTheory.T.torsion_shape_of_torsion_counts hϖ (ReciprocityTheory.ChartRestriction.T2.HcLC ρ) d a φ ⟨C, fun n hn => ?_⟩ ?_
  · obtain ⟨hXf, hX⟩ := key n hn
    try dsimp only at hX
    have hXpos : 0 < Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) :=
      Nat.card_pos
    rw [hX] at hXpos ⊢
    have hb := hC n hn (hpn n)
    try dsimp only at hb
    have h2pos := Nat.pos_of_mul_pos_right hXpos
    constructor
    · exact Nat.le_mul_of_pos_left _ h2pos
    · exact Nat.mul_le_mul_right _ hb
  · obtain ⟨-, hX⟩ := key 1 one_pos
    try dsimp only at hX hone2
    rw [hX]
    calc _ ≤ q * q ^ (1 * d) := Nat.mul_le_mul_right _ hone2
      _ = q ^ (d + 1) := by ring

end GlobalTheory.ShapeNeg
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_shape_of_tate_duality_euler : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ReciprocityTheory.ChartRestriction.T2.ShapeG := by
  atlas_forward_decl GlobalTheory.ShapeNeg.shapeG_of_localDuality
end
