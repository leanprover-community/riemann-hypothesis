import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicityStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import ReciprocityTheory.DualLattices.WedgeNeZeroOfLinearIndependent
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningImageLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionQuotientLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantFrameComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionIntertwining
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTensorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMapsEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankEqFinrankEigenInterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationHerbrandEigenspace

section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix

namespace GlobalTheory.FrameModel

variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]

def embVal (hv : v.Integers O) {Λ : Type} [CommRing Λ] (α : Λ) :
    (Λ →+* O) → v.valuationSubring :=
  fun σ => ⟨algebraMap O C (σ α), (Valuation.mem_valuationSubring_iff _ _).2 (hv.map_le_one _)⟩


def modelLattice {S : Type} {h N : ℕ} (Φ : (Fin h → C) ≃ₗ[C] (S → Fin N → C))
    (L : Submodule O (Fin h → O)) : Submodule v.valuationSubring (S → Fin N → C) :=
  Submodule.span v.valuationSubring ((fun t => Φ (incl C h t)) '' (L : Set (Fin h → O)))

theorem mem_span_valuationSubring_iff (hv : v.Integers O) {W : Type} [AddCommGroup W] [Module C W]
    [Module O W] [IsScalarTower O C W] [Module v.valuationSubring W]
    [IsScalarTower v.valuationSubring C W] (s : Set W) (x : W) :
    x ∈ Submodule.span v.valuationSubring s ↔ x ∈ Submodule.span O s := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      obtain ⟨o, ho⟩ := hv.exists_of_le_one ((Valuation.mem_valuationSubring_iff _ _).1 c.2)
      have : c • x = o • x := by
        rw [← algebraMap_smul C c x, ← algebraMap_smul C o x, ho]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ hx
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul o x _ hx =>
      let c : v.valuationSubring :=
        ⟨algebraMap O C o, (Valuation.mem_valuationSubring_iff _ _).2 (hv.map_le_one _)⟩
      have : o • x = c • x := by
        rw [← algebraMap_smul C c x, ← algebraMap_smul C o x]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ hx

theorem mem_modelLattice (hv : v.Integers O) {S : Type} {h N : ℕ}
    (Φ : (Fin h → C) ≃ₗ[C] (S → Fin N → C)) (L : Submodule O (Fin h → O)) (w : S → Fin N → C) :
    w ∈ modelLattice v Φ L ↔ ∃ t ∈ L, Φ (incl C h t) = w := by
  unfold modelLattice
  rw [mem_span_valuationSubring_iff v hv]
  have : (fun t => Φ (incl C h t)) '' (L : Set (Fin h → O)) =
      (L.map ((Φ.toLinearMap.restrictScalars O) ∘ₗ incl C h) : Set (S → Fin N → C)) := by
    rw [Submodule.map_coe]; rfl
  rw [this, Submodule.span_eq, Submodule.mem_map]
  rfl

theorem mem_eig_iff {Λ : Type} [CommRing Λ] {h : ℕ} (ρ : Λ → Matrix (Fin h) (Fin h) O)
    (τ : Λ →+* O) (x : Fin h → C) :
    x ∈ eig C ρ τ ↔ ∀ l, (ρ l).map (algebraMap O C) *ᵥ x = algebraMap O C (τ l) • x := by
  simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

theorem mem_eig_iff_support (hv : v.Integers O) {Λ : Type} [CommRing Λ] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (x : Fin h → C) : x ∈ eig C ρ τ ↔ ∀ σ, σ ≠ τ → Φ x σ = 0 := by
  rw [mem_eig_iff]
  constructor
  · intro hx σ hσ
    obtain ⟨l, hl⟩ : ∃ l, σ l ≠ τ l := by
      by_contra hc
      push Not at hc
      exact hσ (RingHom.ext hc)
    have e := hΦ l x σ
    rw [hx l, map_smul, Pi.smul_apply, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at e
    rcases e with e | e
    · exact absurd (hv.hom_inj (sub_eq_zero.1 e)).symm hl
    · exact e
  · intro hx l
    apply Φ.injective
    funext σ
    rw [hΦ, map_smul, Pi.smul_apply]
    by_cases hσ : σ = τ
    · rw [hσ]
    · rw [hx σ hσ, smul_zero, smul_zero]

theorem mem_freeLattice_iff (hv : v.Integers O) {Λ : Type} [CommRing Λ] (α : Λ) {h N : ℕ}
    (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔
      ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α)))
    (w : (Λ →+* O) → Fin N → C) :
    w ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice (embVal v hv α) N ↔
      ∃ t : Fin h → O, Φ (incl C h t) = w := by
  let j : O →+* v.valuationSubring := (algebraMap O C).codRestrict v.valuationSubring
    fun o => (Valuation.mem_valuationSubring_iff _ _).2 (hv.map_le_one _)
  have hj : Function.Surjective j := fun c => by
    obtain ⟨o, ho⟩ := hv.exists_of_le_one ((Valuation.mem_valuationSubring_iff _ _).1 c.2)
    exact ⟨o, Subtype.ext ho⟩
  have key : ∀ (f : Polynomial O) (σ : Λ →+* O),
      (((f.map j).eval (embVal v hv α σ) : v.valuationSubring) : C) =
        algebraMap O C (f.eval (σ α)) := by
    intro f σ
    have : embVal v hv α σ = j (σ α) := rfl
    rw [this, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rfl
  constructor
  · intro hw
    have : ∀ i, Φ.symm w i ∈ (algebraMap O C).range := by
      rw [hΦ]
      intro i
      obtain ⟨f, hf⟩ := hw i
      obtain ⟨g, rfl⟩ := Polynomial.map_surjective j hj f
      exact ⟨g, fun σ => by rw [Φ.apply_symm_apply, hf, key]⟩
    choose t ht using this
    refine ⟨t, ?_⟩
    have : incl C h t = Φ.symm w := funext ht
    rw [this, Φ.apply_symm_apply]
  · rintro ⟨t, rfl⟩ i
    obtain ⟨f, hf⟩ := (hΦ (incl C h t)).1 (fun i => ⟨t i, rfl⟩) i
    exact ⟨f.map j, fun σ => by rw [hf, key]⟩

theorem mulVec_incl {h k : ℕ} (X : Matrix (Fin k) (Fin h) O) (t : Fin h → O) :
    X.map (algebraMap O C) *ᵥ incl C h t = incl C k (X *ᵥ t) := by
  funext i
  show _ = algebraMap O C ((X *ᵥ t) i)
  rw [RingHom.map_mulVec]
  rfl

theorem incl_injective (hv : v.Integers O) (h : ℕ) :
    Function.Injective (incl C h : (Fin h → O) → (Fin h → C)) := by
  intro u u' e
  funext i
  exact hv.hom_inj (congrFun e i)

theorem exists_smul_eq_incl (hv : v.Integers O) {h : ℕ} (y : Fin h → C) :
    ∃ (o : O) (t : Fin h → O), algebraMap O C o ≠ 0 ∧ incl C h t = algebraMap O C o • y := by
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : IsFractionRing O C := hv.isFractionRing
  obtain ⟨o, ho⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) y
  choose t ht using ho
  refine ⟨o, t, fun e => nonZeroDivisors.coe_ne_zero o (hv.hom_inj (by rw [e, map_zero])), ?_⟩
  funext i
  show algebraMap O C (t i) = _
  rw [ht i, Pi.smul_apply, algebraMap_smul]

theorem mem_iSup_eig_iff (hv : v.Integers O) {Λ : Type} [CommRing Λ] [Finite (Λ →+* O)] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (x : Fin h → C) :
    x ∈ (⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1) ↔ Φ x τ = 0 := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.iSup_induction' with
    | mem σ x hx => exact (mem_eig_iff_support v hv ρ Φ hΦ σ.1 x).1 hx τ σ.2.symm
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, Pi.add_apply, hx, hy, add_zero]
  · intro hx
    letI := Fintype.ofFinite (Λ →+* O)
    have e : x = ∑ σ, Φ.symm (Pi.single σ (Φ x σ)) := by
      rw [← map_sum, Finset.univ_sum_single, Φ.symm_apply_apply]
    rw [e]
    refine sum_mem fun σ _ => ?_
    by_cases hσ : σ = τ
    · rw [hσ, hx, Pi.single_zero, map_zero]
      exact zero_mem _
    · refine Submodule.mem_iSup_of_mem (⟨σ, hσ⟩ : {σ : Λ →+* O // σ ≠ τ}) ?_
      rw [mem_eig_iff_support v hv ρ Φ hΦ]
      intro s hs
      rw [Φ.apply_symm_apply, Pi.single_eq_of_ne hs]

theorem exists_eig_apply_eq (hv : v.Integers O) {Λ : Type} [CommRing Λ] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (w : Fin N → C) : ∃ x ∈ eig C ρ τ, Φ x τ = w := by
  classical
  refine ⟨Φ.symm (Pi.single τ w), ?_, by rw [Φ.apply_symm_apply, Pi.single_eq_same]⟩
  rw [mem_eig_iff_support v hv ρ Φ hΦ]
  intro s hs
  rw [Φ.apply_symm_apply, Pi.single_eq_of_ne hs]

theorem eq_zero_of_apply_eq_zero (hv : v.Integers O) {Λ : Type} [CommRing Λ] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (x : Fin h → C) (hx : x ∈ eig C ρ τ) (h0 : Φ x τ = 0) : x = 0 := by
  apply Φ.injective
  funext σ
  rw [map_zero, Pi.zero_apply]
  by_cases hσ : σ = τ
  · rw [hσ, h0]
  · exact (mem_eig_iff_support v hv ρ Φ hΦ τ x).1 hx σ hσ

theorem mem_eigPart_iff (hv : v.Integers O) {Λ : Type} [CommRing Λ] [Finite (Λ →+* O)] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (L : Submodule O (Fin h → O)) (x : Fin h → C) :
    x ∈ eigPart C ρ τ L ↔ x ∈ eig C ρ τ ∧ ∃ t ∈ L, Φ (incl C h t) τ = Φ x τ := by
  unfold eigPart
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_sup]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, r, hr, rfl⟩
    rw [Submodule.restrictScalars_mem, mem_iSup_eig_iff v hv ρ Φ hΦ] at hr
    exact ⟨t, ht, by rw [map_add, Pi.add_apply, hr, add_zero]⟩
  · rintro ⟨t, ht, e⟩
    refine ⟨_, ⟨t, ht, rfl⟩, x - incl C h t, ?_, by abel⟩
    rw [Submodule.restrictScalars_mem, mem_iSup_eig_iff v hv ρ Φ hΦ, map_sub, Pi.sub_apply, e,
      sub_self]

end GlobalTheory.FrameModel
end
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem span_wedge_of_span_basis : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (N : ℕ) (b : Module.Basis (Fin N) C V), Module.finrank C (⋀[C]^N V) = 1 ∧ exteriorPower.ιMulti C N b ≠ 0 ∧ Submodule.span O {w : ⋀[C]^N V | ∃ x : Fin N → V, (∀ i, x i ∈ (Submodule.span O (Set.range b) : Set V)) ∧ w = exteriorPower.ιMulti C N x} = Submodule.span O {exteriorPower.ιMulti C N b} := by
  intro C _ O _ _ V _ _ _ _ N b
  haveI : Module.Finite C V := Module.Finite.of_basis b
  refine ⟨?_, ?_, ?_⟩
  · rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b, Fintype.card_fin, Nat.choose_self]
  · intro h
    apply ReciprocityTheory.PGsh.wedge_ne_zero_of_linearIndependent b.linearIndependent
    have := congrArg Subtype.val h
    simpa using this
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro w ⟨x, hx, rfl⟩
      obtain ⟨r, hr⟩ := ReciprocityTheory.PGsh.exists_wedge_eq_integral_smul (R := O) b.linearIndependent hx
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨r, ?_⟩
      apply Subtype.ext
      rw [Submodule.coe_smul_of_tower, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, hr,
        algebraMap_smul]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      apply Submodule.subset_span
      exact ⟨b, fun i => Submodule.subset_span ⟨i, rfl⟩, rfl⟩

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorPower_basis_lattice_principal : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (N : ℕ) (b : Module.Basis (Fin N) C V), Module.finrank C (⋀[C]^N V) = 1 ∧ exteriorPower.ιMulti C N b ≠ 0 ∧ Submodule.span O {w : ⋀[C]^N V | ∃ x : Fin N → V, (∀ i, x i ∈ (Submodule.span O (Set.range b) : Set V)) ∧ w = exteriorPower.ιMulti C N x} = Submodule.span O {exteriorPower.ιMulti C N b} := by
  atlas_forward_decl GlobalTheory.span_wedge_of_span_basis
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem exists_basis_span_eq_span_of_valuation : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (h N : ℕ) (g : Fin h → V), v.Integers O → Submodule.span C (Set.range g) = ⊤ → Module.finrank C V = N → ∃ b : Module.Basis (Fin N) C V, Submodule.span O (Set.range g) = Submodule.span O (Set.range b) := by
  intro C _ v O _ _ V _ _ _ _ h N g hv hsp hN
  classical
  have := hv.hom_inj.isDomain
  have := ValuationRing.of_integers v hv
  have := hv.isFractionRing
  set A : Submodule O V := Submodule.span O (Set.range g) with hA
  have : Module.Finite O A := Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_range g))
  have : Module.Flat O A := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro ⟨x, hxA⟩ hx
    rw [Submodule.mem_bot]
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hx
    have h' : ((a : O) • x : V) = 0 := congrArg Subtype.val ha
    rw [← algebraMap_smul C (a : O) x] at h'
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2))
  have : Module.Free O A := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O A
  let w : Module.Free.ChooseBasisIndex O A → V := fun i => (b i : V)
  have hR : LinearIndependent O w := b.linearIndependent.map' A.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent C w := (LinearIndependent.iff_fractionRing O C).1 hR
  have hspR : Submodule.span O (Set.range w) = A := by
    have : Set.range w = A.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspC : Submodule.span C (Set.range w) = ⊤ := by
    rw [← Submodule.span_span_of_tower O, hspR, hA, Submodule.span_span_of_tower, hsp]
  let bC := Module.Basis.mk hC (by rw [hspC])
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O A) = N := by
    rw [← hN, Module.finrank_eq_card_basis bC]
  refine ⟨bC.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.coe_mk, hspR]

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_of_lattice_span : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (h N : ℕ) (g : Fin h → V), v.Integers O → Submodule.span C (Set.range g) = ⊤ → Module.finrank C V = N → ∃ b : Module.Basis (Fin N) C V, Submodule.span O (Set.range g) = Submodule.span O (Set.range b) := by
  atlas_forward_decl GlobalTheory.exists_basis_span_eq_span_of_valuation
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem eigenQuotient_basis_detLattice_eq_span_wedge : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ), v.Integers O → ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → Module.finrank C (eig C ρ τ) = N → ∃ b : Module.Basis (Fin N) C (eig C ρ τ), quotLattice C ρ τ = (Submodule.span O (Set.range b) : Set (eig C ρ τ)) ∧ Module.finrank C (detLine C ρ τ N) = 1 ∧ exteriorPower.ιMulti C N b ≠ 0 ∧ detLattice C ρ τ N = Submodule.span O {exteriorPower.ιMulti C N b} := by
  intro C _ v O _ _ Λ _ h N hv ρ τ hind hsup hrank
  obtain ⟨π, hπ1, -, hq⟩ := GlobalTheory.T.eigen_projection_quotient_lattice C O Λ h ρ τ hind hsup
  have hsurj : Function.Surjective π := fun x => ⟨(x : Fin h → C), hπ1 x⟩
  obtain ⟨g, hgC, hgO⟩ := GlobalTheory.T.exists_spanning_image_lattice C O (eig C ρ τ) h π hsurj
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_basis_of_lattice_span C v O (eig C ρ τ) h N g hv hgC hrank
  have hQ : quotLattice C ρ τ = (Submodule.span O (Set.range b) : Set (eig C ρ τ)) := by
    rw [hq, hgO, hb]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.exteriorPower_basis_lattice_principal C O (eig C ρ τ) N b
  refine ⟨b, hQ, h1, h2, ?_⟩
  unfold detLattice
  rw [hQ]
  exact h3

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_quotient_lattice_eigen : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ), v.Integers O → ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → Module.finrank C (eig C ρ τ) = N → ∃ b : Module.Basis (Fin N) C (eig C ρ τ), quotLattice C ρ τ = (Submodule.span O (Set.range b) : Set (eig C ρ τ)) ∧ Module.finrank C (detLine C ρ τ N) = 1 ∧ exteriorPower.ιMulti C N b ≠ 0 ∧ detLattice C ρ τ N = Submodule.span O {exteriorPower.ιMulti C N b} := by
  atlas_forward_decl GlobalTheory.eigenQuotient_basis_detLattice_eq_span_wedge
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

section Frame

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

theorem sigma_algebraMap_of_isTheta {σ : Λ →+* O} {f : RL p O Λ →+* O} (hf : IsTheta σ f)
    (c : ℤ_[p]) : σ (algebraMap ℤ_[p] Λ c) = padicToO p O c := by
  have key : ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] (algebraMap ℤ_[p] Λ c)) =
      (algebraMap ℤ_[p] (Ainf p O) c) ⊗ₜ[ℤ_[p]] (1 : Λ) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have h1 := hf 1 (algebraMap ℤ_[p] Λ c)
  rw [key, hf, map_one, map_one, one_mul, mul_one] at h1
  exact h1.symm

theorem exists_poly_of_adjoin (α : Λ) (hα : Algebra.adjoin ℤ_[p] {α} = ⊤) (l : Λ) :
    ∃ g : Polynomial O, ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → σ l = g.eval (σ α) := by
  have hl : l ∈ Algebra.adjoin ℤ_[p] {α} := hα ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hl
  obtain ⟨g, rfl⟩ := (AlgHom.mem_range _).mp hl
  refine ⟨g.map (padicToO p O), fun σ f hf => ?_⟩
  rw [Polynomial.eval_map, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  ext c
  exact sigma_algebraMap_of_isTheta hf c

theorem exists_poly_of_elt (α : Λ) (hα : Algebra.adjoin ℤ_[p] {α} = ⊤) (r : RL p O Λ) :
    ∃ P : Polynomial O, ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → f r = P.eval (σ α) := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, fun σ f _ => by simp⟩
  | tmul a l =>
    obtain ⟨g, hg⟩ := exists_poly_of_adjoin (O := O) α hα l
    exact ⟨Polynomial.C (WittVector.fontaineTheta O p a) * g, fun σ f hf => by
      rw [hf, hg σ f hf]; simp⟩
  | add x y hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨P + Q, fun σ f hf => by rw [map_add, hP σ f hf, hQ σ f hf, Polynomial.eval_add]⟩

theorem exists_elt_of_poly (hθ : Function.Surjective (WittVector.fontaineTheta O p)) (α : Λ)
    (P : Polynomial O) : ∃ r : RL p O Λ, ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → f r = P.eval (σ α) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨r, hr⟩ := hP
    obtain ⟨s, hs⟩ := hQ
    exact ⟨r + s, fun σ f hf => by rw [map_add, hr σ f hf, hs σ f hf, Polynomial.eval_add]⟩
  | monomial n c =>
    obtain ⟨a, ha⟩ := hθ c
    exact ⟨a ⊗ₜ[ℤ_[p]] (α ^ n), fun σ f hf => by rw [hf, ha, map_pow, Polynomial.eval_monomial]⟩

end Frame

end GlobalTheory.DetInv

namespace GlobalTheory.DetInv

theorem surjective_of_pow_mem_range {C V ι : Type} [Field C] [AddCommGroup V] [Module C V]
    [Finite ι] {N : ℕ} (Φ : V →ₗ[C] (ι → Fin N → C)) (x : ι → C) (hx : Function.Injective x)
    (h : ∀ (i : Fin N) (k : ℕ),
      (fun σ => (Pi.single i (x σ ^ k) : Fin N → C)) ∈ LinearMap.range Φ) :
    Function.Surjective Φ := by
  classical
  haveI := Fintype.ofFinite ι
  have h1 : ∀ (i : Fin N) (c : ι → C),
      (fun σ => (Pi.single i (c σ) : Fin N → C)) ∈ LinearMap.range Φ := by
    intro i c
    set Q := Lagrange.interpolate Finset.univ x c with hQ
    have e : (fun σ => (Pi.single i (c σ) : Fin N → C)) =
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          Q.coeff k • fun σ => (Pi.single i (x σ ^ k) : Fin N → C) := by
      funext σ j
      have hc : c σ = ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * x σ ^ k := by
        rw [← Polynomial.eval_eq_sum_range, hQ,
          Lagrange.eval_interpolate_at_node c hx.injOn (Finset.mem_univ σ)]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs
      · exact hc
      · simp
    rw [e]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h i k)
  intro y
  have e : y = ∑ i : Fin N, fun σ => (Pi.single i (y σ i) : Fin N → C) := by
    funext σ j
    simp [Finset.sum_apply, Pi.single_apply]
  have : y ∈ LinearMap.range Φ := by
    rw [e]
    exact Submodule.sum_mem _ fun i _ => h1 i _
  exact this

theorem exists_frame_model : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ D : Datum ε h Λ, ∃ Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C), (∀ l z σ, Φ ((actH D l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) ∧ ∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔ ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ α hα N h hh D
  obtain ⟨-, -, -, hθ, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  obtain ⟨-, eM, -, hM, -⟩ := GlobalTheory.T.determinant_frame_comparison p C v O hv ε hε Λ N h hh D
  have hf : ∀ σ : Λ →+* O, ∃ f : RL p O Λ →+* O, IsTheta σ f := fun σ =>
    (theta_tensor_exists p C v O hv ε hε Λ σ).imp fun f hf => hf.1
  choose f hf using hf
  have hπ : ∀ σ : Λ →+* O, ∃ π, IsProj C eM (f σ) π := fun σ =>
    GlobalTheory.T.exists_theta_projection p O C Λ N h σ (f σ) eM (hf σ)
  choose π hπ using hπ
  obtain ⟨hfin, hcard⟩ := GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ
  have hinj : Function.Injective fun σ : Λ →+* O => algebraMap O C (σ α) := by
    intro σ τ hστ
    have h1 : σ α = τ α := hv.hom_inj hστ
    ext l
    obtain ⟨g, hg⟩ := exists_poly_of_adjoin (O := O) α hα l
    rw [hg σ _ (hf σ), hg τ _ (hf τ), h1]
  have hsurj : Function.Surjective (LinearMap.pi π) := by
    refine surjective_of_pow_mem_range _ _ hinj fun i k => ?_
    refine ⟨fun j => algebraMap O C (WittVector.fontaineTheta O p
      (eM (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] (α ^ k))) j)), ?_⟩
    funext σ
    rw [LinearMap.pi_apply, hπ σ]
    funext j
    simp only [Pi.single_apply]
    split_ifs
    · rw [hf σ]; simp
    · simp
  have hrk : Module.finrank C (Fin h → C) = Module.finrank C ((Λ →+* O) → Fin N → C) := by
    haveI := Fintype.ofFinite (Λ →+* O)
    rw [Module.finrank_pi_fintype C (M := fun _ : Λ →+* O => Fin N → C)]
    rw [Nat.card_eq_fintype_card] at hcard
    simp [hcard, hh]
  have hi : Function.Injective (LinearMap.pi π) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).mpr hsurj
  have hb : Function.Bijective (LinearMap.pi π) := ⟨hi, hsurj⟩
  refine ⟨LinearEquiv.ofBijective (LinearMap.pi π) hb, ?_, ?_⟩
  · intro l z σ
    have hmat : IsMat eM eM (D.ρM l)
        (Matrix.diagonal fun _ : Fin N => ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l : RL p O Λ)) := by
      intro w
      rw [← hM l w]
      congr 1
      funext j
      simp [Matrix.mulVec_diagonal]
    have key := GlobalTheory.T.theta_projection_intertwining p O C Λ N h (f σ) eM eM (π σ) (π σ) _ _ (hπ σ) (hπ σ) hmat z
    simp only [LinearEquiv.ofBijective_apply, LinearMap.pi_apply]
    have e1 : (actH D l).map (algebraMap O C) *ᵥ z = redC C (D.ρM l) z := by
      simp only [actH, redC, Matrix.map_map, Matrix.toLin'_apply, RingHom.coe_comp]
    rw [e1, key, Matrix.diagonal_map (map_zero _)]
    funext j
    rw [Matrix.mulVec_diagonal, RingHom.comp_apply, hf σ]
    simp
  · intro z
    simp only [LinearEquiv.ofBijective_apply, LinearMap.pi_apply]
    constructor
    · intro hz i
      choose t ht using hz
      choose a ha using fun j => hθ (t j)
      have e : z = fun j => algebraMap O C (WittVector.fontaineTheta O p (eM (eM.symm a) j)) := by
        funext j
        rw [eM.apply_symm_apply, ha, ht]
      obtain ⟨P, hP⟩ := exists_poly_of_elt α hα (eM.symm a i)
      refine ⟨P, fun σ => ?_⟩
      rw [e, hπ σ, ← hP σ _ (hf σ)]
    · intro hz
      choose P hP using hz
      choose r hr using fun i => exists_elt_of_poly hθ α (P i)
      have e : z = fun j => algebraMap O C (WittVector.fontaineTheta O p (eM r j)) := by
        apply hi
        funext σ
        rw [LinearMap.pi_apply, LinearMap.pi_apply, hπ σ]
        funext i
        rw [hP, hr i σ _ (hf σ)]
      intro j
      rw [e]
      exact ⟨_, rfl⟩

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_alpha_determinant_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ D : Datum ε h Λ, ∃ Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C), (∀ l z σ, Φ ((actH D l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) ∧ ∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔ ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α)) := by
  atlas_forward_decl GlobalTheory.DetInv.exists_frame_model
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_homs_dvr_card_eq_finrank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], Finite (Λ →+* O) ∧ Nat.card (Λ →+* O) = Module.finrank ℤ_[p] Λ := by
  first | exact @GlobalTheory.card_ringHom_to_integers_eq_finrank | exact GlobalTheory.card_ringHom_to_integers_eq_finrank | (intros; apply GlobalTheory.card_ringHom_to_integers_eq_finrank <;> assumption)
end

section
section
open scoped NNReal

namespace GlobalTheory.EigenSubFree

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference Polynomial

theorem prod_X_sub_C_dvd {O ι : Type} [CommRing O] [IsDomain O] (T : Finset ι)
    (c : ι → O) (hc : Set.InjOn c (↑T : Set ι)) (f : Polynomial O)
    (hf : ∀ j ∈ T, f.eval (c j) = 0) :
    (∏ i ∈ T, (X - C (c i))) ∣ f := by
  by_cases h0 : f = 0
  · simp [h0]
  have hnd : (T.val.map c).Nodup :=
    Multiset.Nodup.map_on (fun x hx y hy h => hc hx hy h) T.nodup
  have hle : T.val.map c ≤ f.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro b hb
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hb
    exact (Polynomial.mem_roots h0).2 (hf j hj)
  have := (Multiset.prod_X_sub_C_dvd_iff_le_roots h0 _).2 hle
  rwa [Multiset.map_map] at this

variable {C : Type} [Field C] {w : Valuation C ℝ≥0} {S : Type}

theorem mem_eigenQuot_freeLattice (a : S → w.valuationSubring) (r : ℕ) (τ : S) (u : Fin r → C) :
    u ∈ eigenQuot (W := fun _ => Fin r → C) (freeLattice a r) τ ↔
      ∀ i, u i ∈ w.valuationSubring := by
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    obtain ⟨f, hf⟩ := hx i
    simp only [LinearMap.proj_apply]
    rw [hf τ]
    exact Subtype.prop _
  · intro hu
    exact ⟨fun _ => u, fun i => ⟨Polynomial.C ⟨u i, hu i⟩, fun s => by simp⟩, rfl⟩

theorem mem_eigenSub_freeLattice [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ) (τ : S)
    (v : Fin r → C) :
    v ∈ eigenSub (W := fun _ => Fin r → C) (freeLattice a r) τ ↔
      ∀ i, ∃ f : Polynomial w.valuationSubring,
        (∀ s, s ≠ τ → f.eval (a s) = 0) ∧ ((f.eval (a τ) : w.valuationSubring) : C) = v i := by
  show (LinearMap.single w.valuationSubring (fun _ : S => Fin r → C) τ v) ∈ freeLattice a r ↔ _
  constructor
  · intro h i
    obtain ⟨f, hf⟩ := h i
    refine ⟨f, fun s hs => ?_, ?_⟩
    · have := hf s
      simp [hs] at this
      exact_mod_cast this.symm
    · have := hf τ
      simp at this
      exact this.symm
  · intro h i
    obtain ⟨f, h0, h1⟩ := h i
    refine ⟨f, fun s => ?_⟩
    by_cases hs : s = τ
    · subst hs; simp [h1]
    · simp [hs, h0 s hs]

theorem eigenSub_freeLattice [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ)
    (τ : S) (ha : Function.Injective a) :
    eigenSub (W := fun _ => Fin r → C) (freeLattice a r) τ =
      flatLattice (r := r) a τ (diffGen a τ) := by
  ext v
  rw [mem_eigenSub_freeLattice]
  unfold flatLattice
  rw [Submodule.mem_map]
  constructor
  · intro h
    have key : ∀ i, ∃ g : w.valuationSubring, (diffGen a τ : C) * g = v i := by
      intro i
      obtain ⟨f, h0, h1⟩ := h i
      obtain ⟨q, hq⟩ := prod_X_sub_C_dvd (Finset.univ.erase τ) a
        (fun x _ y _ e => ha e) f (fun j hj => h0 j (Finset.ne_of_mem_erase hj))
      refine ⟨q.eval (a τ), ?_⟩
      rw [← h1, hq, eval_mul, eval_prod]
      simp [diffGen]
    choose g hg using key
    refine ⟨fun i => (g i : C), (mem_eigenQuot_freeLattice a r τ _).2 fun i => (g i).2, ?_⟩
    funext i
    simp [Algebra.smul_def, hg i]
  · rintro ⟨u, hu, rfl⟩ i
    have hu' := (mem_eigenQuot_freeLattice a r τ u).1 hu
    refine ⟨Polynomial.C (⟨u i, hu' i⟩ : w.valuationSubring) *
      ∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s)), fun s hs => ?_, ?_⟩
    · rw [eval_mul, eval_prod]
      rw [Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩) (by simp)]
      simp
    · rw [eval_mul, eval_prod]
      simp [diffGen, Algebra.smul_def, mul_comm]

theorem main : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (r : ℕ) (τ : S), Function.Injective a →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a r) τ =
      GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.flatLattice (r := r) a τ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ) :=
  fun _ _ _ _ _ _ a r τ ha => eigenSub_freeLattice a r τ ha

end GlobalTheory.EigenSubFree
end

open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piEigenSublattice_free_eq_differentScaled : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a r) τ = GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.flatLattice (r := r) a τ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ) := by
  atlas_forward_decl GlobalTheory.EigenSubFree.main
end

section
section
open scoped NNReal

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

theorem addVal_inv_pow_mul {C : Type} [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) {d c : C} (hd : d ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    addVal w ℓ (d⁻¹ ^ n * c) = addVal w ℓ c - (n : ℝ) * addVal w ℓ d := by
  have hwd : ((w d : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hd)
  have hwc : ((w c : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hc)
  have hl : Real.log ((w ℓ : ℝ≥0) : ℝ) ≠ 0 := by
    refine (Real.log_neg ?_ ?_).ne
    · exact_mod_cast h0
    · exact_mod_cast h1
  unfold addVal
  rw [map_mul, map_pow, map_inv₀]
  push_cast
  rw [Real.log_mul (pow_ne_zero _ (inv_ne_zero hwd)) hwc, Real.log_pow, Real.log_inv]
  field_simp
  ring

theorem detRel_of_detRel_lsmul (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (p q : ℕ) (F : Submodule C (Fin (p + q) → C))
    (X0 : Submodule w.valuationSubring (Fin (p + q) → C))
    (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F))
    (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring)
    (hd : d ≠ 0)
    (h : DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y) :
    DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * addVal w ℓ (d : C)) := by
  obtain ⟨x, u, m, c, hx, hu, hm, hmF, ⟨hc0, hcy⟩, hdet⟩ := h
  have hdC : (d : C) ≠ 0 := fun e => hd (Subtype.ext e)
  have hsm : ∀ v : Fin (p + q) → C, d • v = (d : C) • v := fun v => rfl
  have hinj : Function.Injective (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d) := by
    intro a b hab
    simp only [LinearMap.lsmul_apply, hsm] at hab
    exact smul_right_injective _ hdC hab
  refine ⟨fun i => (d : C)⁻¹ • x i, u, m, (d : C)⁻¹ ^ (p + q) * c, ⟨?_, ?_⟩, hu, hm, hmF,
    ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hdC)) hc0, ?_⟩, ?_⟩
  · exact hx.1.units_smul (fun _ => Units.mk0 _ (inv_ne_zero hdC))
  · apply Submodule.map_injective_of_injective hinj
    rw [← hx.2, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [hsm, smul_smul, hdC]
  · rw [addVal_inv_pow_mul w ℓ h0 h1 hdC hc0, hcy]
  · have : Matrix.of (fun i => (d : C)⁻¹ • x i) = (d : C)⁻¹ • Matrix.of x := by
      ext i j; simp
    rw [this, Matrix.det_smul, Fintype.card_fin, hdet, mul_assoc]

end GlobalTheory
end

open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeDetRelation_of_lsmul_shift : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (p q : ℕ) (F : Submodule C (Fin (p + q) → C)) (X0 : Submodule w.valuationSubring (Fin (p + q) → C)) (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F)) (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring), d ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ (d : C)) := by
  atlas_forward_decl GlobalTheory.detRel_of_detRel_lsmul
end

section
open scoped NNReal

namespace GlobalTheory.DetRelCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

section Core

variable {C : Type} [Field C]

theorem eq_sum_rows {n : ℕ} (U : Fin n → Fin n → C) (h : (Matrix.of U).det ≠ 0)
    (f : Fin n → C) : ∃ γ : Fin n → C, f = ∑ s, γ s • U s := by
  refine ⟨Matrix.vecMul f (Matrix.of U)⁻¹, ?_⟩
  have hu : IsUnit (Matrix.of U).det := isUnit_iff_ne_zero.mpr h
  have key : Matrix.vecMul (Matrix.vecMul f (Matrix.of U)⁻¹) (Matrix.of U) = f := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  funext j
  conv_lhs => rw [← key]
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

theorem exists_eq_sum_of_mem {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (u0 : Fin p → Fin (p + q) → C) (m0 : Fin q → Fin (p + q) → C)
    (hli : LinearIndependent C fun i => F.mkQ (u0 i)) (hm0 : ∀ k, m0 k ∈ F)
    (hN : (Matrix.of (Fin.append u0 m0)).det ≠ 0) (f : Fin (p + q) → C) (hf : f ∈ F) :
    ∃ β : Fin q → C, f = ∑ k, β k • m0 k := by
  obtain ⟨γ, hγ⟩ := eq_sum_rows _ hN f
  rw [Fin.sum_univ_add] at hγ
  simp only [Fin.append_left, Fin.append_right] at hγ
  have hz : ∑ i, γ (Fin.castAdd q i) • F.mkQ (u0 i) = 0 := by
    have h1 := congrArg F.mkQ hγ
    have hf0 : F.mkQ f = 0 := by simpa using hf
    have hm : ∑ k, γ (Fin.natAdd p k) • F.mkQ (m0 k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hm0 k]
    rw [hf0, map_add, map_sum, map_sum] at h1
    simp only [map_smul] at h1
    rw [hm, add_zero] at h1
    exact h1.symm
  have h0 := Fintype.linearIndependent_iff.1 hli _ hz
  exact ⟨fun k => γ (Fin.natAdd p k), by rw [hγ]; simp [h0]⟩

theorem det_append_eq {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (u u0 : Fin p → Fin (p + q) → C) (m m0 : Fin q → Fin (p + q) → C)
    (A : Matrix (Fin p) (Fin p) C) (B : Matrix (Fin q) (Fin q) C)
    (hu : ∀ i, F.mkQ (u i) = ∑ j, A i j • F.mkQ (u0 j))
    (hm : ∀ i, m i = ∑ j, B i j • m0 j)
    (hli : LinearIndependent C fun i => F.mkQ (u0 i))
    (hm0 : ∀ k, m0 k ∈ F) (hN : (Matrix.of (Fin.append u0 m0)).det ≠ 0) :
    (Matrix.of (Fin.append u m)).det = A.det * B.det * (Matrix.of (Fin.append u0 m0)).det := by
  have hmem : ∀ i, u i - ∑ j, A i j • u0 j ∈ F := by
    intro i
    have : F.mkQ (u i - ∑ j, A i j • u0 j) = 0 := by
      rw [map_sub, map_sum, hu i]; simp only [map_smul]; exact sub_self _
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  choose β hβ using fun i => exists_eq_sum_of_mem F u0 m0 hli hm0 hN _ (hmem i)
  have key : (Matrix.of (Fin.append u m)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks A (Matrix.of β) 0 B *
        (Matrix.of (Fin.append u0 m0)).submatrix finSumFinEquiv finSumFinEquiv := by
    ext r c
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with i | k
    · have hi : u i = ∑ j, A i j • u0 j + ∑ k, β i k • m0 k := by rw [← hβ i]; abel
      simp [Matrix.fromBlocks, hi, Finset.sum_apply]
    · simp [Matrix.fromBlocks, hm k, Finset.sum_apply]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_submatrix_equiv_self]

theorem comp_sum {W : Type} [AddCommGroup W] [Module C W] {n k l : ℕ} (a : Fin n → W)
    (b : Fin k → W) (c : Fin l → W) (P : Matrix (Fin k) (Fin n) C)
    (Q : Matrix (Fin l) (Fin k) C) (hb : ∀ i, b i = ∑ j, P i j • a j)
    (hc : ∀ i, c i = ∑ j, Q i j • b j) : ∀ i, c i = ∑ j, (Q * P) i j • a j := by
  intro i
  simp only [hc i, hb, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

end Core

section Lattice

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem coeffs {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n k : ℕ} (a : Fin n → W) (b : Fin k → W)
    (h : ∀ i, b i ∈ Submodule.span w.valuationSubring (Set.range a)) :
    ∃ P : Matrix (Fin k) (Fin n) w.valuationSubring,
      ∀ i, b i = ∑ j, algebraMap w.valuationSubring C (P i j) • a j := by
  choose P hP using fun i =>
    (Submodule.mem_span_range_iff_exists_fun w.valuationSubring).1 (h i)
  exact ⟨Matrix.of P, fun i => by
    rw [← hP i]; exact Finset.sum_congr rfl fun j _ => (algebraMap_smul C (P i j) (a j)).symm⟩

theorem mem_span_of_isLatticeBasis {W : Type} [AddCommGroup W] [Module C W]
    [Module w.valuationSubring W] [IsScalarTower w.valuationSubring C W] {n k : ℕ}
    {a : Fin n → W} {b : Fin k → W} {Y : Submodule w.valuationSubring W}
    (ha : IsLatticeBasis w a Y) (hb : IsLatticeBasis w b Y) (i : Fin k) :
    b i ∈ Submodule.span w.valuationSubring (Set.range a) := by
  rw [ha.2, ← hb.2]; exact Submodule.subset_span ⟨i, rfl⟩

theorem transition {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n : ℕ} (a b : Fin n → W)
    (Y : Submodule w.valuationSubring W) (ha : IsLatticeBasis w a Y)
    (hb : IsLatticeBasis w b Y) :
    ∃ P : Matrix (Fin n) (Fin n) C, (∀ i, b i = ∑ j, P i j • a j) ∧ w P.det = 1 := by
  obtain ⟨P, hP⟩ := coeffs a b (mem_span_of_isLatticeBasis ha hb)
  obtain ⟨Q, hQ⟩ := coeffs b a (mem_span_of_isLatticeBasis hb ha)
  have hQP := comp_sum a b a (P.map (algebraMap w.valuationSubring C))
    (Q.map (algebraMap w.valuationSubring C)) hP hQ
  have hone : (Q.map (algebraMap w.valuationSubring C)) * (P.map (algebraMap w.valuationSubring C))
      = 1 := by
    ext i j
    have h := Fintype.linearIndependent_iff.1 ha.1
      (fun j => ((Q.map (algebraMap w.valuationSubring C)) *
        (P.map (algebraMap w.valuationSubring C))) i j - (1 : Matrix (Fin n) (Fin n) C) i j)
      (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hQP i]
        simp [Matrix.one_apply])
      j
    exact sub_eq_zero.1 h
  have hdet := congrArg Matrix.det hone
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have hle : ∀ R : Matrix (Fin n) (Fin n) w.valuationSubring,
      w (R.map (algebraMap w.valuationSubring C)).det ≤ 1 := by
    intro R
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ValuationSubring.algebraMap_apply]
    exact (w.mem_valuationSubring_iff _).1 R.det.2
  refine ⟨P.map (algebraMap w.valuationSubring C), fun i => hP i, le_antisymm (hle P) ?_⟩
  calc (1 : ℝ≥0) = w (Q.map (algebraMap w.valuationSubring C)).det *
        w (P.map (algebraMap w.valuationSubring C)).det := by rw [← map_mul, hdet, map_one]
    _ ≤ w (P.map (algebraMap w.valuationSubring C)).det :=
        mul_le_of_le_one_left (by positivity) (hle Q)

end Lattice

end GlobalTheory.DetRelCompare

namespace GlobalTheory.DetRelCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

end GlobalTheory.DetRelCompare
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.FrameModel Matrix TensorProduct

namespace GlobalTheory.FrameModel

theorem isFiltration_modelLattice_ker : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (Λ : Type) [CommRing Λ] [Finite (Λ →+* O)] (α : Λ) (h N : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) O) (X : Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C)), (∀ l, X * ρ l = ρ' l * X) → (∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) → (∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔ ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α))) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration (embVal v hv α) (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X))) := by
  intro C _ v O _ _ hv Λ _ _ α h N ρ ρ' X Φ hX hΦ1 hΦ2
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw c hc hcw => ?_⟩
  · obtain ⟨t, -, rfl⟩ := (mem_modelLattice v hv Φ _ _).1 hw
    exact (mem_freeLattice_iff v hv α Φ hΦ2 _).2 ⟨t, rfl⟩
  · obtain ⟨t, ht, rfl⟩ := (mem_modelLattice v hv Φ _ _).1 hw
    refine (mem_modelLattice v hv Φ _ _).2 ⟨ρ α *ᵥ t, ?_, ?_⟩
    · rw [LinearMap.mem_ker, Matrix.toLin'_apply] at ht ⊢
      rw [Matrix.mulVec_mulVec, hX, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_zero]
    · funext s
      rw [← mulVec_incl, hΦ1]
      rfl
  · obtain ⟨t, rfl⟩ := (mem_freeLattice_iff v hv α Φ hΦ2 _).1 hw
    obtain ⟨t', ht', e⟩ := (mem_modelLattice v hv Φ _ _).1 hcw
    refine (mem_modelLattice v hv Φ _ _).2 ⟨t, ?_, rfl⟩
    have hc' : (c : C) ≠ 0 := fun e => hc (Subtype.ext e)
    have e1 : incl C h t' = (c : C) • incl C h t := by
      apply Φ.injective
      rw [e, map_smul]
      rfl
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at ht' ⊢
    have e2 := congrArg (fun y => X.map (algebraMap O C) *ᵥ y) e1
    simp only [Matrix.mulVec_smul, mulVec_incl, ht', map_zero] at e2
    apply incl_injective v hv
    rw [map_zero]
    exact (smul_eq_zero.1 e2.symm).resolve_left hc'

theorem mulVec_eq_zero_iff_mem_filSpace : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (Λ : Type) [CommRing Λ] [Finite (Λ →+* O)] (α : Λ) (h N : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) O) (X : Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C)), (∀ l, X * ρ l = ρ' l * X) → (∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) → (∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔ ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α))) → Function.Injective (embVal v hv α) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration (embVal v hv α) (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X))) → ∀ y : Fin h → C, (Matrix.toLin' (X.map (algebraMap O C))) y = 0 ↔ ∀ s, Φ y s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X))) s := by
  intro C _ v O _ _ hv Λ _ _ α h N ρ ρ' X Φ hX hΦ1 hΦ2 hinj hfilt y
  classical
  letI : Fintype (Λ →+* O) := Fintype.ofFinite _
  obtain ⟨o, t, ho, ht⟩ := exists_smul_eq_incl v hv y
  have hb : X.map (algebraMap O C) *ᵥ y = 0 ↔ t ∈ LinearMap.ker (Matrix.toLin' X) := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, ← (incl_injective v hv h).eq_iff, ← mulVec_incl, ht,
      map_zero, Matrix.mulVec_smul, smul_eq_zero]
    exact ⟨Or.inr, fun e => e.resolve_left ho⟩
  have hs : ∀ s, Φ (incl C h t) s = algebraMap O C o • Φ y s := fun s => by
    rw [ht, map_smul, Pi.smul_apply]
  rw [Matrix.toLin'_apply, hb]
  constructor
  · intro htk s
    rw [← Submodule.smul_mem_iff _ ho, ← hs]
    exact Submodule.subset_span ⟨_, (mem_modelLattice v hv Φ _ _).2 ⟨t, htk, rfl⟩, rfl⟩
  · intro hy
    have := GlobalTheory.T.mem_filtration_of_components_mem_eigenSpan C v (Λ →+* O) (embVal v hv α) N _ hinj hfilt (Φ (incl C h t))
      ((mem_freeLattice_iff v hv α Φ hΦ2 _).2 ⟨t, rfl⟩)
      (fun s => by rw [hs]; exact Submodule.smul_mem _ _ (hy s))
    obtain ⟨t', ht', e⟩ := (mem_modelLattice v hv Φ _ _).1 this
    rwa [← incl_injective v hv h (Φ.injective e)]

theorem finrank_add_finrank_map_eig : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (Λ : Type) [CommRing Λ] (h N : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C)) (b : (Fin h → C) →ₗ[C] (Fin h → C)) (F : (Λ →+* O) → Submodule C (Fin N → C)), (∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) → (∀ y, b y = 0 ↔ ∀ s, Φ y s ∈ F s) → ∀ s, Module.finrank C (F s) + Module.finrank C ((eig C ρ s).map b) = N := by
  intro C _ v O _ _ hv Λ _ h N ρ Φ b F hΦ hb s
  let π : eig C ρ s →ₗ[C] (Fin N → C) :=
    ((LinearMap.proj s : ((Λ →+* O) → Fin N → C) →ₗ[C] _) ∘ₗ Φ.toLinearMap) ∘ₗ (eig C ρ s).subtype
  have hπ : Function.Bijective π := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      exact Subtype.ext (eq_zero_of_apply_eq_zero v hv ρ Φ hΦ s x x.2 hx)
    · intro w
      obtain ⟨x, hx, e⟩ := exists_eig_apply_eq v hv ρ Φ hΦ s w
      exact ⟨⟨x, hx⟩, e⟩
  let e := LinearEquiv.ofBijective π hπ
  have h1 := LinearMap.finrank_range_add_finrank_ker (b ∘ₗ (eig C ρ s).subtype)
  have h2 : Module.finrank C (eig C ρ s) = N := by
    rw [e.finrank_eq, Module.finrank_fin_fun]
  have h3 : LinearMap.range (b ∘ₗ (eig C ρ s).subtype) = (eig C ρ s).map b := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have h4 : LinearMap.ker (b ∘ₗ (eig C ρ s).subtype) = (F s).comap e.toLinearMap := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    show b x = 0 ↔ Φ x s ∈ F s
    rw [hb]
    refine ⟨fun H => H s, fun H σ => ?_⟩
    by_cases hσ : σ = s
    · rwa [hσ]
    · rw [(mem_eig_iff_support v hv ρ Φ hΦ s x).1 x.2 σ hσ]
      exact zero_mem _
  have h5 : Module.finrank C ((F s).comap e.toLinearMap) = Module.finrank C (F s) := by
    rw [Submodule.comap_equiv_eq_map_symm]
    exact LinearEquiv.finrank_map_eq _ _
  rw [h2, h3, h4, h5] at h1
  omega

theorem isLatticeBasis_lie : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (Λ : Type) [CommRing Λ] [Finite (Λ →+* O)] (α : Λ) (h N : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) O) (X : Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C)), (∀ l, X * ρ l = ρ' l * X) → (∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) → (∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔ ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α))) → (∀ y : Fin h → C, (Matrix.toLin' (X.map (algebraMap O C))) y = 0 ↔ ∀ s, Φ y s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X))) s) → ∀ [DecidableEq (Λ →+* O)] (τ : Λ →+* O) (n : ℕ) (y : Fin n → eig C ρ τ), IsBasisOf C ((LinearMap.range (Matrix.toLin' X) ⊓ ⨅ l : Λ, Module.End.eigenspace (Matrix.toLin' (ρ' l)) (τ l)).map (incl C h)) (fun i => (Matrix.toLin' (X.map (algebraMap O C))) (y i)) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis v (fun i => (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X))) τ).mkQ (Φ (y i) τ)) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice (embVal v hv α) N) (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X)))) τ) := by
  intro C _ v O _ _ hv Λ _ _ α h N ρ ρ' X Φ hX hΦ1 hΦ2 hker _ τ n y hy
  set F := GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X))) with hF
  set b := Matrix.toLin' (X.map (algebraMap O C)) with hb
  have hsup := mem_eig_iff_support v hv ρ Φ hΦ1 τ
  let π : (Fin h → C) →ₗ[C] ((Fin N → C) ⧸ F τ) :=
    (F τ).mkQ ∘ₗ (LinearMap.proj τ : ((Λ →+* O) → Fin N → C) →ₗ[C] _) ∘ₗ Φ.toLinearMap
  have hπ : ∀ x, π x = (F τ).mkQ (Φ x τ) := fun _ => rfl
  have hk : ∀ x ∈ eig C ρ τ, (b x = 0 ↔ π x = 0) := by
    intro x hx
    rw [hker, hπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨fun H => H τ, fun H σ => ?_⟩
    by_cases hσ : σ = τ
    · rwa [hσ]
    · rw [(hsup x).1 hx σ hσ]
      exact zero_mem _
  have hmem : ∀ x ∈ eig C ρ τ, (π x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice (embVal v hv α) N)
      (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X)))) τ ↔
      ∃ t : Fin h → O, b (incl C h t) = b x) := by
    intro x hx
    have key : ∀ t : Fin h → O, b (incl C h t) = b x ↔
        ∀ s, (F s).mkQ (Φ (incl C h t) s) =
          (Pi.single τ (π x) : ∀ s, (Fin N → C) ⧸ F s) s := by
      intro t
      rw [← sub_eq_zero, ← map_sub, hker]
      refine forall_congr' fun s => ?_
      rw [map_sub, Pi.sub_apply]
      by_cases hs : s = τ
      · subst hs
        rw [Pi.single_eq_same, hπ, Submodule.mkQ_apply, Submodule.mkQ_apply,
          Submodule.Quotient.eq]
      · rw [Pi.single_eq_of_ne hs, (hsup x).1 hx s hs, sub_zero, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie
    rw [Submodule.mem_comap, Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, e⟩
      obtain ⟨t, rfl⟩ := (mem_freeLattice_iff v hv α Φ hΦ2 _).1 hw
      exact ⟨t, (key t).2 fun s => congrFun e s⟩
    · rintro ⟨t, ht⟩
      exact ⟨_, (mem_freeLattice_iff v hv α Φ hΦ2 _).2 ⟨t, rfl⟩, funext ((key t).1 ht)⟩
  have hlie : ∀ x ∈ eig C ρ τ, ((∃ t : Fin h → O, b (incl C h t) = b x) ↔
      b x ∈ Submodule.span O (Set.range fun i => b (y i))) := by
    intro x hx
    rw [hy.2, Submodule.mem_map]
    constructor
    · rintro ⟨t, ht⟩
      have ht' : incl C h (X *ᵥ t) = b x := by rw [← ht, hb, Matrix.toLin'_apply, mulVec_incl]
      refine ⟨X *ᵥ t, ⟨⟨t, rfl⟩, ?_⟩, ht'⟩
      rw [SetLike.mem_coe, Submodule.mem_iInf]
      intro l
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      apply incl_injective v hv
      rw [← mulVec_incl, map_smul, ht', hb, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        ← Matrix.map_mul, ← hX, Matrix.map_mul, ← Matrix.mulVec_mulVec,
        (mem_eig_iff ρ τ x).1 hx l, Matrix.mulVec_smul, algebraMap_smul]
    · rintro ⟨_, ⟨⟨t, rfl⟩, -⟩, ht⟩
      exact ⟨t, by rw [← ht, hb, Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_incl]⟩
  have hsum : ∀ g : Fin n → C, ∑ i, g i • (y i : Fin h → C) ∈ eig C ρ τ := fun g =>
    sum_mem fun i _ => Submodule.smul_mem _ _ (y i).2
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    refine Fintype.linearIndependent_iff.1 hy.1 g ?_
    have := (hk _ (hsum g)).2 (by rw [map_sum]; simp only [map_smul]; exact hg)
    rw [map_sum] at this
    simpa only [map_smul] using this
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (hmem _ (y i).2).2 ((hlie _ (y i).2).2 (Submodule.subset_span ⟨i, rfl⟩))
    · intro q hq
      obtain ⟨w, rfl⟩ := (F τ).mkQ_surjective q
      obtain ⟨x, hx, rfl⟩ := exists_eig_apply_eq v hv ρ Φ hΦ1 τ w
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun O).1
        ((hlie x hx).1 ((hmem x hx).1 hq))
      have h0 := (hk _ (sub_mem hx (hsum fun i => algebraMap O C (g i)))).1 (by
        rw [map_sub, map_sum, ← hg, sub_eq_zero]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul, algebraMap_smul])
      rw [map_sub, map_sum, sub_eq_zero] at h0
      rw [← hπ, h0]
      refine sum_mem fun i _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ (⟨algebraMap O C (g i),
        (Valuation.mem_valuationSubring_iff _ _).2 (hv.map_le_one _)⟩ : v.valuationSubring)
        (Submodule.subset_span ⟨i, rfl⟩)

theorem det_append_eq_mul_det : ∀ (C : Type) [Field C] (w : Valuation C NNReal) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → ∀ (x : Fin (p + q) → Fin (p + q) → C) (u : Fin p → Fin (p + q) → C) (m : Fin q → Fin (p + q) → C), GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w x (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w (fun i => (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ).mkQ (u i)) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w m (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ) → ∃ c : C, w c = ∏ s ∈ Finset.univ.erase τ, w ((a τ : C) - (a s : C)) ^ (p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s)) ∧ (Matrix.of (Fin.append u m)).det = c * (Matrix.of x).det := by
  intro C _ w ℓ hℓ0 hℓ1 S _ _ a p q Fil τ ha hFil x u m hx hu hm
  set F := GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ with hF
  have hfin : Module.finrank C F = q := by
    have hsp : F = Submodule.span C (Set.range m) := by
      rw [hF, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace, ← hm.2, Submodule.span_span_of_tower]
    rw [hsp, finrank_span_eq_card hm.1, Fintype.card_fin]
  have hd0 : GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr ?_
    exact ha.ne (Finset.ne_of_mem_erase hs).symm
  have h1 := GlobalTheory.T.latticeDetRelation_herbrand_eigenspace C w ℓ hℓ0 hℓ1 S a p q Fil τ ha hFil hfin
  rw [GlobalTheory.T.piEigenSublattice_free_eq_differentScaled C w S a (p + q) τ ha] at h1
  have h2 := GlobalTheory.T.latticeDetRelation_of_lsmul_shift C w ℓ hℓ0 hℓ1 p q _ _ _ _ _ _ hd0 h1
  obtain ⟨x', u', m', c, hx', hu', hm', hmF, ⟨hc0, hcv⟩, hdet⟩ := h2
  obtain ⟨P, hP, hPdet⟩ := GlobalTheory.DetRelCompare.transition x' x _ hx' hx
  obtain ⟨A, hA, hAdet⟩ := GlobalTheory.DetRelCompare.transition _ _ _ hu' hu
  obtain ⟨B, hB, hBdet⟩ := GlobalTheory.DetRelCompare.transition m' m _ hm' hm
  have hx'0 : (Matrix.of x').det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hx'.1)).ne_zero
  have happ0 : (Matrix.of (Fin.append u' m')).det ≠ 0 := by
    intro h0
    exact hx'0 (by rw [hdet, h0, mul_zero])
  have hrel := GlobalTheory.DetRelCompare.det_append_eq F u u' m m' A B hA hB hu'.1 hmF happ0
  have hxP : (Matrix.of x).det = P.det * (Matrix.of x').det := by
    have hmat : Matrix.of x = P * Matrix.of x' := by
      ext i k
      simp [Matrix.mul_apply, hP i, Finset.sum_apply]
    rw [hmat, Matrix.det_mul]
  have hP0 : P.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hPdet
    exact zero_ne_one hPdet
  refine ⟨A.det * B.det * (P.det * c)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv₀, map_mul, hAdet, hBdet, hPdet, one_mul, one_mul, one_mul]
    have hlam : Real.log (w ℓ : ℝ) ≠ 0 :=
      (Real.log_neg (NNReal.coe_pos.mpr hℓ0) (NNReal.coe_lt_one.mpr hℓ1)).ne
    have hds : ∀ s ∈ Finset.univ.erase τ, ((w ((a τ : C) - (a s : C)) : NNReal) : ℝ) ≠ 0 := by
      intro s hs
      rw [NNReal.coe_ne_zero, Valuation.ne_zero_iff]
      exact sub_ne_zero.mpr (Subtype.coe_injective.ne (ha.ne (Finset.ne_of_mem_erase hs).symm))
    have hdiff : ((GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ : w.valuationSubring) : C)
        = ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen]
    have hle : ∀ s, Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) ≤ p + q := fun s =>
      (Submodule.finrank_le _).trans_eq (Module.finrank_fin_fun C)
    have hlogc : Real.log (w c : ℝ) = - ∑ s ∈ Finset.univ.erase τ,
        ((p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℕ) : ℝ)
          * Real.log (w ((a τ : C) - (a s : C)) : ℝ) := by
      have e := hcv
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal] at e
      rw [hdiff, map_prod, NNReal.coe_prod, Real.log_prod hds, div_eq_iff hlam] at e
      rw [e, sub_mul, Finset.sum_mul, mul_assoc, div_mul_cancel₀ _ hlam, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Nat.cast_sub (hle s)]
      field_simp
      ring
    have hwc : 0 < ((w c : NNReal) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff w).mpr hc0))
    apply NNReal.coe_injective
    rw [NNReal.coe_inv, NNReal.coe_prod]
    simp only [NNReal.coe_pow]
    have hpos2 : 0 < ∏ s ∈ Finset.univ.erase τ, ((w ((a τ : C) - (a s : C)) : NNReal) : ℝ)
        ^ (p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s)) :=
      Finset.prod_pos fun s hs => pow_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) (hds s hs).symm) _
    rw [← Real.exp_log (inv_pos.mpr hwc), ← Real.exp_log hpos2, Real.log_inv, hlogc, neg_neg,
      Real.log_prod fun s hs => pow_ne_zero _ (hds s hs)]
    simp only [Real.log_pow]
  · rw [hrel, hxP, hdet]
    field_simp

end GlobalTheory.FrameModel

namespace GlobalTheory.FrameModel

section Small

variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]

theorem alternating_apply_eq_det_smul {E W : Type} [AddCommGroup E] [Module C E] [AddCommGroup W]
    [Module C W] {n : ℕ} (f : E [⋀^Fin n]→ₗ[C] W) (e : Module.Basis (Fin n) C E) (z : Fin n → E) :
    f z = e.det z • f e := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff C]
  intro φ
  have := congrArg (fun g => g z) ((φ.compAlternatingMap f).eq_smul_basis_det e)
  simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at this
  rw [map_sub, this, map_smul, smul_eq_mul, mul_comm, sub_self]

theorem isLatticeBasis_map (hv : v.Integers O) {h N n : ℕ} (π : (Fin h → C) →ₗ[C] (Fin N → C))
    (E : Submodule C (Fin h → C)) (hE : ∀ x ∈ E, π x = 0 → x = 0) (y : Fin n → Fin h → C)
    (hy : ∀ i, y i ∈ E) (hli : LinearIndependent C y)
    (L : Submodule v.valuationSubring (Fin N → C))
    (hL : ∀ w, w ∈ L ↔ ∃ x ∈ Submodule.span O (Set.range y), π x = w) :
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis v (fun i => π (y i)) L := by
  constructor
  · refine hli.map (f := π) ?_
    rw [Submodule.disjoint_def]
    intro x hx hx0
    refine hE x ?_ hx0
    exact (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hy i)) hx
  · ext w
    rw [mem_span_valuationSubring_iff v hv, hL]
    have : Set.range (fun i => π (y i)) = (π.restrictScalars O) '' Set.range y := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, Submodule.mem_map]
    rfl

end Small

end GlobalTheory.FrameModel

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.DetInv.span_wedge_lie_fil_eq_smul_detLattice : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (a b h : ℕ), h = Module.finrank ℤ_[p] Λ * (a + b) → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) (z : Fin (a + b) → eig C (actH D) τ), IsBasisOf C (lieSub C D τ) (fun i => bC C D (z (Fin.castAdd b i))) → IsBasisOf C (filQuot C D τ) (fun i => (z (Fin.natAdd a i) : Fin h → C)) → ∃ c : C, v c = ∏ᶠ σ : {σ : Λ →+* O // σ ≠ τ}, v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1 ∧ (Submodule.span O {exteriorPower.ιMulti C (a + b) z} : Set (detLine C (actH D) τ (a + b))) = (fun w => c • w) '' (detLattice C (actH D) τ (a + b) : Set (detLine C (actH D) τ (a + b))) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ α hα a b h hh D τ z hzL hzF
  classical
  obtain ⟨⟨hindT, -, -⟩, ⟨hindH, htopH, hdimH⟩⟩ :=
    GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ (a + b) h hh D
  obtain ⟨e, hQ, -, -, hdet⟩ :=
    GlobalTheory.T.exists_basis_quotient_lattice_eigen C v O Λ h (a + b) hv (actH D) τ hindH htopH (hdimH τ)
  obtain ⟨Φ, hΦ1, hΦ2⟩ := GlobalTheory.T.dvr_alpha_determinant_property p C v O hv ε hε Λ α hα (a + b) h hh D
  haveI : Finite (Λ →+* O) := (GlobalTheory.T.ring_homs_dvr_card_eq_finrank p C v O hv Λ).1
  letI : Fintype (Λ →+* O) := Fintype.ofFinite _
  have hinj : Function.Injective (embVal v hv α) := by
    intro σ σ' he
    have he' : σ α = σ' α := hv.hom_inj (congrArg Subtype.val he)
    let S : Subalgebra ℤ_[p] Λ :=
      { σ.eqLocus σ' with
        algebraMap_mem' := fun r => by
          show σ (algebraMap ℤ_[p] Λ r) = σ' (algebraMap ℤ_[p] Λ r)
          have h1 := GlobalTheory.T.padic_ring_hom_eq_canonical p O (σ.comp (algebraMap ℤ_[p] Λ))
          have h2 := GlobalTheory.T.padic_ring_hom_eq_canonical p O (σ'.comp (algebraMap ℤ_[p] Λ))
          exact (RingHom.congr_fun h1 r).trans (RingHom.congr_fun h2 r).symm }
    have hle : Algebra.adjoin ℤ_[p] {α} ≤ S := Algebra.adjoin_le (by simpa [S] using he')
    ext x
    have hx : x ∈ Algebra.adjoin ℤ_[p] {α} := hα ▸ Algebra.mem_top
    exact hle hx
  have hint := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
  have hX : ∀ l, D.G.map (WittVector.fontaineTheta O p) * actH D l =
      actT D l * D.G.map (WittVector.fontaineTheta O p) := by
    intro l
    have e' := congrArg (fun M => M.map (WittVector.fontaineTheta O p)) (hint.2.2.1 l)
    simp only [Matrix.map_mul] at e'
    unfold actH actT
    rw [e']
    simp only [rhoTA, Matrix.map_map]
    rfl
  have hfilt : GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration (embVal v hv α) (modelLattice v Φ D.Fil) :=
    isFiltration_modelLattice_ker C v O hv Λ α h (a + b) (actH D) (actT D) _ Φ hX hΦ1 hΦ2
  have hker : ∀ y : Fin h → C, bC C D y = 0 ↔
      ∀ s, Φ y s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace (modelLattice v Φ D.Fil) s :=
    mulVec_eq_zero_iff_mem_filSpace C v O hv Λ α h (a + b) (actH D) (actT D) _ Φ hX hΦ1 hΦ2 hinj hfilt
  have hrank : ∀ s, a + b - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace (modelLattice v Φ D.Fil) s) =
      D.lieRank s := by
    intro s
    have h1 := finrank_add_finrank_map_eig C v O hv Λ h (a + b) (actH D) Φ (bC C D) _ hΦ1 hker s
    have h2 : LinearMap.range (bC C D) ⊓ eig C (actT D) s = (eig C (actH D) s).map (bC C D) :=
      (GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actH D) (actT D)
        (D.G.map (WittVector.fontaineTheta O p)) hX).2 htopH hindT s
    rw [GlobalTheory.T.lie_rank_eq_finrank_eigen_inter p C v O hv ε Λ h D s, h2]
    omega
  have hu := isLatticeBasis_lie C v O hv Λ α h (a + b) (actH D) (actT D) _ Φ hX hΦ1 hΦ2 hker τ a
    (fun i => z (Fin.castAdd b i)) hzL
  let π : (Fin h → C) →ₗ[C] (Fin (a + b) → C) :=
    (LinearMap.proj τ : ((Λ →+* O) → Fin (a + b) → C) →ₗ[C] _) ∘ₗ Φ.toLinearMap
  have hπ : ∀ x, π x = Φ x τ := fun _ => rfl
  have hE : ∀ x ∈ eig C (actH D) τ, π x = 0 → x = 0 :=
    eq_zero_of_apply_eq_zero v hv (actH D) Φ hΦ1 τ
  have hm := isLatticeBasis_map v hv π _ hE (fun i => (z (Fin.natAdd a i) : Fin h → C))
    (fun i => (z _).2) hzF.1
    (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (a + b) → C) (modelLattice v Φ D.Fil) τ) (by
      intro w
      rw [hzF.2]
      unfold GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot filQuot
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨t, ht, rfl⟩ := (mem_modelLattice v hv Φ _ _).1 hy
        obtain ⟨x, hx, hxe⟩ := exists_eig_apply_eq v hv (actH D) Φ hΦ1 τ (Φ (incl C h t) τ)
        exact ⟨x, (mem_eigPart_iff v hv (actH D) Φ hΦ1 τ _ x).2 ⟨hx, t, ht, hxe.symm⟩, hxe⟩
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨-, t, ht, hte⟩ := (mem_eigPart_iff v hv (actH D) Φ hΦ1 τ _ x).1 hx
        exact ⟨_, (mem_modelLattice v hv Φ _ _).2 ⟨t, ht, rfl⟩, hte⟩)
  have hspan : ∀ x : Fin h → C, x ∈ Submodule.span O (Set.range fun i => (e i : Fin h → C)) ↔
      ∃ x' ∈ quotLattice C (actH D) τ, (x' : Fin h → C) = x := by
    intro x
    have : Set.range (fun i => (e i : Fin h → C)) =
        ((eig C (actH D) τ).subtype.restrictScalars O) '' Set.range e := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, Submodule.mem_map, hQ]
    rfl
  have hx := isLatticeBasis_map v hv π _ hE (fun i => (e i : Fin h → C))
    (fun i => (e _).2) (e.linearIndependent.map' _ (Submodule.ker_subtype _))
    (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (a + b) → C)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice (embVal v hv α) (a + b)) τ) (by
      intro w
      unfold GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨t, rfl⟩ := (mem_freeLattice_iff v hv α Φ hΦ2 _).1 hy
        obtain ⟨x, hx, hxe⟩ := exists_eig_apply_eq v hv (actH D) Φ hΦ1 τ (Φ (incl C h t) τ)
        refine ⟨x, (hspan x).2 ⟨⟨x, hx⟩, ⟨t, ?_⟩, rfl⟩, hxe⟩
        rw [mem_iSup_eig_iff v hv (actH D) Φ hΦ1, map_sub, Pi.sub_apply, sub_eq_zero]
        exact hxe.symm
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨x', ⟨t, ht⟩, rfl⟩ := (hspan x).1 hx
        rw [mem_iSup_eig_iff v hv (actH D) Φ hΦ1, map_sub, Pi.sub_apply, sub_eq_zero] at ht
        exact ⟨_, (mem_freeLattice_iff v hv α Φ hΦ2 _).2 ⟨t, rfl⟩, ht⟩)
  have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hv0 : 0 < v (p : C) := zero_lt_iff.2 ((v.ne_zero_iff).2 hp0)
  have hv1 : v (p : C) < 1 := by
    have hp : algebraMap O C (p : O) = (p : C) := map_natCast _ _
    refine lt_of_le_of_ne (hp ▸ hv.map_le_one _) fun h1 => (Fact.out : ¬IsUnit (p : O)) ?_
    exact hv.isUnit_of_one (hp ▸ hp0.isUnit) (hp ▸ h1)
  obtain ⟨c, hc, hcd⟩ := det_append_eq_mul_det C v (p : C) hv0 hv1 (Λ →+* O) (embVal v hv α) a b
    (modelLattice v Φ D.Fil) τ hinj hfilt _ _ _ hx hu hm
  have hX0 : (Matrix.of fun i => π (e i)).det ≠ 0 := by
    have hu : IsUnit (Matrix.of fun i => π (e i)) :=
      Matrix.linearIndependent_rows_iff_isUnit.1 hx.1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  have hce : e.det z = c := by
    have h1 := alternating_apply_eq_det_smul
      ((Matrix.detRowAlternating : (Fin (a + b) → C) [⋀^Fin (a + b)]→ₗ[C] C).compLinearMap
        (π ∘ₗ (eig C (actH D) τ).subtype)) e z
    have h2 : (Fin.append (fun i => Φ (z (Fin.castAdd b i)) τ)
        (fun i => π (z (Fin.natAdd a i)))) = fun i => π (z i) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; rfl
      · rw [Fin.append_right]
    rw [h2] at hcd
    apply mul_right_cancel₀ hX0
    rw [← hcd]
    exact h1.symm
  refine ⟨c, ?_, ?_⟩
  · rw [hc, finprod_eq_prod_of_fintype]
    rw [Finset.prod_subtype (p := fun σ : Λ →+* O => σ ≠ τ) (Finset.univ.erase τ) (by simp)]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [hrank]
    rfl
  · rw [hdet, alternating_apply_eq_det_smul _ e z, hce]
    ext w
    simp only [SetLike.mem_coe, Submodule.mem_span_singleton, Set.mem_image]
    constructor
    · rintro ⟨o, rfl⟩
      exact ⟨_, ⟨o, rfl⟩, smul_comm _ _ _⟩
    · rintro ⟨_, ⟨o, rfl⟩, rfl⟩
      exact ⟨o, smul_comm _ _ _⟩
end
