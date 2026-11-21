import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthCharacterEqualityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacter
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpoly
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCountOfSsRankStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrvG6OfAllPartsStatement

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu_character : MuChar := by
  first | exact @GlobalTheory.MuCharProof.muChar_holds | exact GlobalTheory.MuCharProof.muChar_holds | (intros; apply GlobalTheory.MuCharProof.muChar_holds <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.SSListPf

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial GlobalTheory.StringRepresentationDecomposition
open scoped Matrix

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

def AInv {V : Type} [AddCommGroup V] [Module K V] (ρ : Γ →* Module.End K V) (W : Submodule K V) : Prop :=
  ∀ g, ∀ v ∈ W, ρ g v ∈ W

def resEnd {V : Type} [AddCommGroup V] [Module K V] (ρ : Γ →* Module.End K V) (U : Submodule K V)
    (hU : AInv ρ U) : Γ →* Module.End K U where
  toFun g := (ρ g).restrict (hU g)
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp [LinearMap.restrict_apply, Module.End.mul_apply]

def quoEnd {V : Type} [AddCommGroup V] [Module K V] (ρ : Γ →* Module.End K V) (U : Submodule K V)
    (hU : AInv ρ U) : Γ →* Module.End K (V ⧸ U) where
  toFun g := U.mapQ U (ρ g) (hU g)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp
  map_mul' g h := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp [Module.End.mul_apply]

def matRep {V : Type} [AddCommGroup V] [Module K V] {m : ℕ} (ρ : Γ →* Module.End K V)
    (b : Module.Basis (Fin m) K V) : Γ →* GL (Fin m) K :=
  MonoidHom.toHomUnits
    (((LinearMap.toMatrixAlgEquiv b : Module.End K V ≃ₐ[K] Matrix (Fin m) (Fin m) K) :
      Module.End K V →* Matrix (Fin m) (Fin m) K).comp ρ)

theorem matRep_val {V : Type} [AddCommGroup V] [Module K V] {m : ℕ} (ρ : Γ →* Module.End K V)
    (b : Module.Basis (Fin m) K V) (g : Γ) :
    ((matRep ρ b g : GL _ _) : Matrix (Fin m) (Fin m) K) = LinearMap.toMatrix b b (ρ g) := by
  simp only [matRep, MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, MonoidHom.coe_coe]
  rfl

theorem matRep_mulVec {V : Type} [AddCommGroup V] [Module K V] {m : ℕ} (ρ : Γ →* Module.End K V)
    (b : Module.Basis (Fin m) K V) (g : Γ) (y : V) :
    ((matRep ρ b g : GL _ _) : Matrix (Fin m) (Fin m) K) *ᵥ b.equivFun y = b.equivFun (ρ g y) := by
  rw [matRep_val, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
  exact LinearMap.toMatrix_mulVec_repr b b (ρ g) y

theorem charpoly_matRep {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {m : ℕ}
    (ρ : Γ →* Module.End K V) (b : Module.Basis (Fin m) K V) (g : Γ) :
    ((matRep ρ b g : GL _ _) : Matrix (Fin m) (Fin m) K).charpoly = (ρ g).charpoly := by
  rw [matRep_val, LinearMap.charpoly_toMatrix]

theorem charpoly_res_quot {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (e : Module.End K V) (W : Submodule K V) (he : ∀ x ∈ W, e x ∈ W) :
    e.charpoly = (e.restrict he).charpoly * (W.mapQ W e he).charpoly := by
  let bW := Module.finBasis K W
  let bQ := Module.finBasis K (V ⧸ W)
  let b := Module.Basis.sumQuot bW bQ
  let A := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K (V ⧸ W))) K := Matrix.of fun i l ↦
    (b.repr (e (b (Sum.inr l)))) (Sum.inl i)
  let D := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices h : LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.charpoly_toMatrix e b, h, Matrix.charpoly_fromBlocks_zero₂₁,
      LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k0 =>
      simp only [b, Module.Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply Module.Basis.sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k0 =>
      suffices W.mkQ (e (bW k0)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he _ (Submodule.coe_mem (bW k0))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, Module.Basis.sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← Module.Basis.sumQuot_inr bW bQ l, W.mapQ_apply]
      simp

def Split {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Γ →* Module.End K V) : Prop :=
  ∃ L : List (Σ m : ℕ, Γ →* GL (Fin m) K), (∀ p ∈ L, 1 ≤ p.1 ∧ IsIrrSub p.2 ⊤) ∧
    ∀ g, (ρ g).charpoly = (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod

theorem split_zero {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Γ →* Module.End K V) (hV : Module.finrank K V = 0) : Split ρ := by
  refine ⟨[], fun p hp => absurd hp List.not_mem_nil, fun g => ?_⟩
  rw [List.map_nil, List.prod_nil]
  exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree, hV])

theorem split_irr {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Γ →* Module.End K V) (hV : 0 < Module.finrank K V)
    (hirr : ∀ W : Submodule K V, AInv ρ W → W = ⊥ ∨ W = ⊤) : Split ρ := by
  let b := Module.finBasis K V
  refine ⟨[⟨Module.finrank K V, matRep ρ b⟩], fun p hp => ?_, fun g => ?_⟩
  · rw [List.mem_singleton] at hp
    subst hp
    refine ⟨hV, ?_, fun _ _ _ => Submodule.mem_top, fun W' _ hW' => ?_⟩
    · intro h0
      have h1 : (fun _ => (1 : K)) ∈ (⊤ : Submodule K (Fin (Module.finrank K V) → K)) := Submodule.mem_top
      rw [h0, Submodule.mem_bot] at h1
      have h2 := congrFun h1 ⟨0, hV⟩
      simp at h2
    · have h1 : AInv ρ (W'.comap (b.equivFun : V →ₗ[K] (Fin (Module.finrank K V) → K))) := by
        intro g y hy
        show b.equivFun (ρ g y) ∈ W'
        rw [← matRep_mulVec]
        exact hW' g _ hy
      have h2 : (W'.comap (b.equivFun : V →ₗ[K] (Fin (Module.finrank K V) → K))).map
          (b.equivFun : V →ₗ[K] (Fin (Module.finrank K V) → K)) = W' :=
        Submodule.map_comap_eq_of_surjective b.equivFun.surjective W'
      rcases hirr _ h1 with h3 | h3
      · left
        rw [← h2, h3, Submodule.map_bot]
      · right
        rw [← h2, h3, Submodule.map_top, LinearMap.range_eq_top.mpr b.equivFun.surjective]
  · rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (charpoly_matRep ρ b g).symm

theorem split_step {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Γ →* Module.End K V) (W : Submodule K V) (hW : AInv ρ W)
    (h1 : Split (resEnd ρ W hW)) (h2 : Split (quoEnd ρ W hW)) : Split ρ := by
  refine ⟨h1.choose ++ h2.choose, fun p hp => ?_, fun g => ?_⟩
  · rcases List.mem_append.mp hp with h | h
    · exact h1.choose_spec.1 p h
    · exact h2.choose_spec.1 p h
  · rw [List.map_append, List.prod_append, ← h1.choose_spec.2 g, ← h2.choose_spec.2 g]
    exact charpoly_res_quot (ρ g) W (hW g)

theorem split_all (d : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    Module.finrank K V = d → ∀ ρ : Γ →* Module.End K V, Split ρ := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hV ρ
  by_cases hex : ∃ W : Submodule K V, AInv ρ W ∧ W ≠ ⊥ ∧ W ≠ ⊤
  · have hW : AInv ρ hex.choose := hex.choose_spec.1
    have hb : hex.choose ≠ ⊥ := hex.choose_spec.2.1
    have ht : hex.choose ≠ ⊤ := hex.choose_spec.2.2
    have hlt : Module.finrank K hex.choose < d := by
      rw [← hV]; exact Submodule.finrank_lt ht
    have hpos : 0 < Module.finrank K hex.choose :=
      Nat.pos_of_ne_zero fun h => hb (Submodule.finrank_eq_zero.mp h)
    have hq : Module.finrank K (V ⧸ hex.choose) + Module.finrank K hex.choose = d := by
      rw [← hV]; exact Submodule.finrank_quotient_add_finrank _
    exact split_step ρ hex.choose hW (ih _ hlt hex.choose rfl (resEnd ρ hex.choose hW))
      (ih _ (by omega) (V ⧸ hex.choose) rfl (quoEnd ρ hex.choose hW))
  · push_neg at hex
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exact split_zero ρ (hV.trans h0)
    · refine split_irr ρ (hV ▸ h0) fun W hW => ?_
      by_cases hb : W = ⊥
      · exact Or.inl hb
      · exact Or.inr (hex W hW hb)

end SSListPf

open Formalism.MainNotions.N Polynomial GlobalTheory.StringRepresentationDecomposition

theorem ssList_holds : SSList := by
  intro k _ Γ _ n ρ
  let ρE : Γ →* Module.End k (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)) :
      Matrix (Fin n) (Fin n) k →* Module.End k (Fin n → k)).comp ((Units.coeHom _).comp ρ)
  have hρg : ∀ g, ρE g = Matrix.toLin' ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) k) := fun g => rfl
  have h := SSListPf.split_all n (Fin n → k) (by simp) ρE
  refine ⟨h.choose, h.choose_spec.1, fun g => ?_⟩
  rw [← h.choose_spec.2 g, hρg, Matrix.charpoly_toLin']

end GlobalTheory
end
end

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_constituents_charpoly_product : SSList := by
  atlas_forward_decl GlobalTheory.ssList_holds
end

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrreducible_constituent_ranks_unique_of_charpoly : SSRankUnique := by
  first | exact @GlobalTheory.SSRank.ssRankUnique_holds | exact GlobalTheory.SSRank.ssRankUnique_holds | (intros; apply GlobalTheory.SSRank.ssRankUnique_holds <;> assumption)
end

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigencharacter_of_summand_charZero : EigenCharTwist := by
  first | exact @GlobalTheory.eigenCharTwist_holds | exact GlobalTheory.eigenCharTwist_holds | (intros; apply GlobalTheory.eigenCharTwist_holds <;> assumption)
end

section
open Polynomial

namespace GlobalTheory.AlgClosedResidueField

theorem isAlgClosed_residueField {K : Type} [Field K] (O : ValuationSubring K) [IsAlgClosed K] :
    IsAlgClosed (IsLocalRing.ResidueField O) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue O) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue O) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨q, hqp, hdeg, hq⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  have hd : (q.map (algebraMap O K)).degree ≠ 0 := by
    rw [hq.degree_map, hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hx' : q.eval₂ (algebraMap O K) x = 0 := by
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hx
  have hint : IsIntegral O x := ⟨q, hq, hx'⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hy : q.eval y = 0 := by
    rw [Polynomial.eval₂_at_apply] at hx'
    exact (IsFractionRing.injective O K) (by rw [hx', map_zero])
  refine ⟨IsLocalRing.residue O y, ?_⟩
  rw [← hqp, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]

end GlobalTheory.AlgClosedResidueField
end

section
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

open Matrix

namespace GlobalTheory.ValRing

section Lat

variable {K : Type} [Field K] (O : ValuationSubring K) {Γ : Type} [Group Γ] {n : ℕ}

def actL (M : Matrix (Fin n) (Fin n) K) : (Fin n → K) →ₗ[O] (Fin n → K) :=
  (Matrix.mulVecLin M).restrictScalars O

theorem actL_apply (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : actL O M v = M *ᵥ v := rfl

def lat (ρ : Γ →* GL (Fin n) K) (S : Finset Γ) : Submodule O (Fin n → K) :=
  Submodule.span O (Set.range fun p : S × Fin n =>
    ((ρ p.1.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single p.2 1 : Fin n → K))

theorem gen_mem (ρ : Γ →* GL (Fin n) K) (S : Finset Γ)
    (hS : ∀ g, ∃ s ∈ S, ∀ i j, ((ρ (s⁻¹ * g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (g t : Γ) (i : Fin n) :
    ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((ρ t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single i 1 : Fin n → K)) ∈ lat O ρ S := by
  obtain ⟨s, hs, hh⟩ := hS (g * t)
  set h := ((ρ (s⁻¹ * (g * t)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hhdef
  have e1 : ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((ρ t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single i 1 : Fin n → K)) =
      ((ρ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (h *ᵥ (Pi.single i 1 : Fin n → K)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hhdef, ← Units.val_mul, ← Units.val_mul, ← map_mul,
      ← map_mul, mul_inv_cancel_left]
  have e2 : h *ᵥ (Pi.single i 1 : Fin n → K) = ∑ k, h k i • (Pi.single k 1 : Fin n → K) := by
    funext m
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e1, e2, Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [Matrix.mulVec_smul]
  exact (lat O ρ S).smul_mem (⟨h k i, hh k i⟩ : O) (Submodule.subset_span ⟨(⟨s, hs⟩, k), rfl⟩)

theorem lat_stable (ρ : Γ →* GL (Fin n) K) (S : Finset Γ)
    (hS : ∀ g, ∃ s ∈ S, ∀ i j, ((ρ (s⁻¹ * g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O) (g : Γ) :
    ∀ x ∈ lat O ρ S, actL O ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x ∈ lat O ρ S := by
  have h : lat O ρ S ≤ (lat O ρ S).comap (actL O ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨t, i⟩, rfl⟩
    exact gen_mem O ρ S hS g t.1 i
  exact fun x hx => h hx

theorem single_mem (ρ : Γ →* GL (Fin n) K) (S : Finset Γ) (h1 : (1 : Γ) ∈ S) (i : Fin n) :
    (Pi.single i 1 : Fin n → K) ∈ lat O ρ S :=
  Submodule.subset_span ⟨(⟨1, h1⟩, i), by
    show ((ρ 1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single i 1 : Fin n → K) = _
    rw [map_one, Units.val_one, Matrix.one_mulVec]⟩

def act (ρ : Γ →* GL (Fin n) K) (S : Finset Γ)
    (hS : ∀ g, ∃ s ∈ S, ∀ i j, ((ρ (s⁻¹ * g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O) :
    Γ →* Module.End O (lat O ρ S) where
  toFun δ := (actL O ((ρ δ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).restrict (lat_stable O ρ S hS δ)
  map_one' := by
    ext x : 1
    apply Subtype.ext
    simp [actL_apply]
  map_mul' := by
    intro a b
    ext x : 1
    apply Subtype.ext
    simp [actL_apply, Matrix.mulVec_mulVec]

theorem act_apply (ρ : Γ →* GL (Fin n) K) (S : Finset Γ)
    (hS : ∀ g, ∃ s ∈ S, ∀ i j, ((ρ (s⁻¹ * g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (δ : Γ) (x : lat O ρ S) :
    ((act O ρ S hS δ x : lat O ρ S) : Fin n → K) =
      ((ρ δ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K) := rfl

theorem lat_finite (ρ : Γ →* GL (Fin n) K) (S : Finset Γ) : Module.Finite O (lat O ρ S) :=
  Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range _))

theorem lat_torsion (ρ : Γ →* GL (Fin n) K) (S : Finset Γ) : Submodule.torsion O (lat O ρ S) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  rw [Submodule.mem_bot]
  obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
  have ha : ((a : O) : K) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero a (Subtype.ext h)
  have h2 : ((a : O) : K) • (x : Fin n → K) = 0 := congrArg Subtype.val hax
  exact Subtype.ext ((smul_eq_zero.mp h2).resolve_left ha)

theorem exists_basis (ρ : Γ →* GL (Fin n) K) (S : Finset Γ) (h1 : (1 : Γ) ∈ S) :
    Nonempty (Module.Basis (Fin n) O (lat O ρ S)) := by
  have := lat_finite O ρ S
  have : Module.Flat O (lat O ρ S) :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr (lat_torsion O ρ S)
  have : Module.Free O (lat O ρ S) := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O (lat O ρ S)
  have hle : Fintype.card (Module.Free.ChooseBasisIndex O (lat O ρ S)) ≤ n := by
    have li := b.linearIndependent.map' (lat O ρ S).subtype (Submodule.ker_subtype _)
    have liK := (LinearIndependent.iff_fractionRing O K).mp li
    simpa using liK.fintype_card_le_finrank
  have hge : n ≤ Fintype.card (Module.Free.ChooseBasisIndex O (lat O ρ S)) := by
    have li : LinearIndependent O fun i : Fin n =>
        (⟨Pi.single i 1, single_mem O ρ S h1 i⟩ : lat O ρ S) := by
      apply LinearIndependent.of_comp (lat O ρ S).subtype
      refine (LinearIndependent.iff_fractionRing O K).mpr ?_
      have e : ((lat O ρ S).subtype ∘ fun i : Fin n =>
          (⟨Pi.single i 1, single_mem O ρ S h1 i⟩ : lat O ρ S)) = fun i => Pi.basisFun K (Fin n) i := by
        funext i
        simp
      rw [e]
      exact (Pi.basisFun K (Fin n)).linearIndependent
    have := li.fintype_card_le_finrank
    rwa [Module.finrank_eq_card_basis b, Fintype.card_fin] at this
  exact ⟨b.reindex (Fintype.equivFinOfCardEq (le_antisymm hle hge))⟩

theorem coe_repr_sum (ρ : Γ →* GL (Fin n) K) (S : Finset Γ) (b : Module.Basis (Fin n) O (lat O ρ S))
    (x : lat O ρ S) (l : Fin n) :
    ∑ i, algebraMap O K (b.repr x i) * ((b i : lat O ρ S) : Fin n → K) l = (x : Fin n → K) l := by
  have h := congrArg (fun y : lat O ρ S => (y : Fin n → K) l) (b.sum_repr x)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Algebra.smul_def] at h
  exact h

theorem conj (ρ : Γ →* GL (Fin n) K) (S : Finset Γ)
    (hS : ∀ g, ∃ s ∈ S, ∀ i j, ((ρ (s⁻¹ * g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (h1 : (1 : Γ) ∈ S) :
    ∃ (ρ0 : Γ →* GL (Fin n) O) (P : GL (Fin n) K), ∀ g,
      ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (P : Matrix (Fin n) (Fin n) K) * ((ρ0 g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O).map (algebraMap O K) *
          ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨b⟩ := exists_basis O ρ S h1
  let G : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => ((b j : lat O ρ S) : Fin n → K) i
  let D : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun i j => algebraMap O K (b.repr ⟨Pi.single j 1, single_mem O ρ S h1 j⟩ i)
  have hGD : G * D = 1 := by
    refine Matrix.ext fun l j => ?_
    rw [Matrix.mul_apply]
    have := coe_repr_sum O ρ S b ⟨Pi.single j 1, single_mem O ρ S h1 j⟩ l
    simp only [G, D, Matrix.of_apply]
    rw [Matrix.one_apply]
    convert this using 1
    · exact Finset.sum_congr rfl fun i _ => mul_comm (((b i : lat O ρ S) : Fin n → K) l) _
    · simp [Pi.single_apply]
  have hDG : D * G = 1 := mul_eq_one_comm.mp hGD
  let P : GL (Fin n) K := ⟨G, D, hGD, hDG⟩
  let ρ₀ : Γ →* GL (Fin n) O :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp (act O ρ S hS).toHomUnits
  refine ⟨ρ₀, P, fun γ => ?_⟩
  set C := LinearMap.toMatrixAlgEquiv b (act O ρ S hS γ) with hC
  have hρ0 : ((ρ₀ γ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = C := rfl
  have key : ((ρ γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * G = G * C.map (algebraMap O K) := by
    refine Matrix.ext fun l j => ?_
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have h1' := act_apply O ρ S hS γ (b j)
    have h2 := coe_repr_sum O ρ S b (act O ρ S hS γ (b j)) l
    rw [h1'] at h2
    simp only [G, Matrix.of_apply, Matrix.map_apply, hC, LinearMap.toMatrixAlgEquiv_apply]
    simp only [Matrix.mulVec, dotProduct] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hρ0]
  show ((ρ γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = G * C.map (algebraMap O K) * D
  rw [← key, Matrix.mul_assoc, hGD, Matrix.mul_one]

end Lat

section Top

variable {K : Type} [Field K] (O : ValuationSubring K)

theorem exists_cover [TopologicalSpace K] (hO : IsOpen (O : Set K)) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] {n : ℕ} (ρ : Γ →* GL (Fin n) K)
    (hρ : Continuous fun g => ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ S : Finset Γ, (1 : Γ) ∈ S ∧
      ∀ g, ∃ s ∈ S, ∀ i j, ((ρ (s⁻¹ * g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O := by
  let U : Γ → Set Γ := fun s => {x | ∀ i j, ((ρ (s⁻¹ * x) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O}
  have hU : ∀ s, IsOpen (U s) := by
    intro s
    have e : U s = ⋂ i, ⋂ j,
        (fun x => ((ρ (s⁻¹ * x) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ⁻¹' (O : Set K) := by
      ext x
      simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage ((hρ.comp (continuous_const.mul continuous_id)).matrix_elem i j)
  have hcov : Set.univ ⊆ ⋃ s, U s := by
    intro x _
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    show ∀ i j, ((ρ (x⁻¹ * x) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O
    intro i j
    rw [inv_mul_cancel, map_one, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcov
  classical
  refine ⟨insert 1 t, Finset.mem_insert_self _ _, fun g => ?_⟩
  have hg := ht (Set.mem_univ g)
  rw [Set.mem_iUnion₂] at hg
  obtain ⟨s, hs, hgs⟩ := hg
  exact ⟨s, Finset.mem_insert_of_mem hs, hgs⟩

theorem res_algClosed [IsAlgClosed K] : IsAlgClosed (IsLocalRing.ResidueField O) := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField
  | exact @_root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField
  | exact _root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField
  | (apply _root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField ..)

end Top

section Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def unitBall : ValuationSubring K := GlobalTheory.ClosedBallValuationSubring.closedBallValuationSubring K

theorem mem_unitBall (x : K) : x ∈ (unitBall : ValuationSubring K) ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem mem_maximalIdeal_unitBall (x : (unitBall : ValuationSubring K)) :
    x ∈ IsLocalRing.maximalIdeal (unitBall : ValuationSubring K) ↔ ‖(x : K)‖ < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hx
    refine lt_of_le_of_ne x.2 fun h1 => hx ?_
    have hx0 : (x : K) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : K)⁻¹, ?_⟩, Subtype.ext ?_⟩
    · show ‖(x : K)⁻¹‖ ≤ 1
      rw [norm_inv, h1, inv_one]
    · show (x : K) * (x : K)⁻¹ = 1
      exact mul_inv_cancel₀ hx0
  · rintro hx ⟨u, hu⟩
    have h0 : ((u : (unitBall : ValuationSubring K)) : K) *
        (((u⁻¹ : (unitBall : ValuationSubring K)ˣ) : (unitBall : ValuationSubring K)) : K) = 1 :=
      congrArg Subtype.val u.mul_inv
    have h := congrArg norm h0
    rw [norm_mul, norm_one] at h
    have h2 : ‖((u⁻¹ : (unitBall : ValuationSubring K)ˣ) : K)‖ ≤ 1 := (u⁻¹ : (unitBall : ValuationSubring K)ˣ).1.2
    rw [hu] at h
    nlinarith [norm_nonneg ((u⁻¹ : (unitBall : ValuationSubring K)ˣ) : K), norm_nonneg (x : K)]

theorem isOpen_unitBall : IsOpen ((unitBall : ValuationSubring K) : Set K) := by
  have : ((unitBall : ValuationSubring K) : Set K) = Metric.closedBall 0 1 := by
    ext x
    simp [mem_unitBall]
  rw [this]
  exact IsUltrametricDist.isOpen_closedBall 0 one_ne_zero

end Ball

theorem valRingModel : ValRingModel := by
  intro l _
  let O : ValuationSubring (Qbar l) := unitBall
  refine ⟨O, inferInstance, inferInstance, res_algClosed O, algebraMap O (Qbar l), fun a b h => Subtype.ext h,
    ?_, fun x => mem_maximalIdeal_unitBall x, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  · intro Γ _ _ _ _ n ρ hρ
    obtain ⟨S, h1, hS⟩ := exists_cover O isOpen_unitBall ρ hρ
    exact conj O ρ S hS h1

end GlobalTheory.ValRing
end
end

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_ring_model : ValRingModel := by
  atlas_forward_decl GlobalTheory.ValRing.valRingModel
end

section
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.SixthNumerics

theorem numerics : Numerics := by
  intro r t d n a A hr ht had hw hsum hpos hn hle
  have hd : d = t + 2 * a := by omega
  have hA : A ≠ 0 := by
    rintro rfl
    simp at hsum
    omega
  have hmem : ∀ x ∈ A, x = 1 := by
    intro x hx
    have h1 := Multiset.count_le_of_le x hle
    rw [Multiset.count_nsmul] at h1
    have hc : 1 ≤ Multiset.count x A := Multiset.one_le_count_iff_mem.mpr hx
    have h2 : d ≤ Multiset.count x (r ::ₘ Multiset.replicate t 1) :=
      le_trans (by nlinarith) h1
    by_contra hx1
    rw [Multiset.count_cons, Multiset.count_replicate] at h2
    split_ifs at h2 <;> omega
  have hrep : A = Multiset.replicate (Multiset.card A) 1 := Multiset.eq_replicate_card.mpr hmem
  have hcard : 1 ≤ Multiset.card A := Multiset.card_pos.mpr hA
  have h1 := Multiset.count_le_of_le 1 hle
  rw [Multiset.count_nsmul, Multiset.count_cons, Multiset.count_replicate_self] at h1
  have hc1 : Multiset.count 1 A = Multiset.card A := by
    conv_lhs => rw [hrep]
    exact Multiset.count_replicate_self _ _
  rw [hc1] at h1
  have hr1 : (1 : ℕ) ≠ r := by omega
  simp [hr1] at h1
  have hsum' : n = Multiset.card A := by
    rw [← hsum, hrep]; simp
  have : Multiset.card A = 1 := by nlinarith
  refine ⟨by omega, ?_⟩
  have : a = 0 := by nlinarith
  omega

theorem rest : Rest := by
  intro ι _ d A r hd hA hs
  have hc := congrArg Multiset.card hs
  have hc' : ∑ k, d k * Multiset.card (A k) = 1 := by
    rw [Multiset.card_sum] at hc
    simpa [Multiset.card_nsmul] using hc
  have hterm : ∀ k, 1 ≤ d k * Multiset.card (A k) := fun k =>
    Nat.mul_le_mul (hd k) (Multiset.card_pos.mpr (hA k))
  have hle : ∀ k, d k * Multiset.card (A k) = 1 := by
    intro k
    have := Finset.single_le_sum (f := fun k => d k * Multiset.card (A k))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
    have := hterm k
    omega
  have hcardle : Fintype.card ι ≤ 1 := by
    have := Finset.card_nsmul_le_sum Finset.univ (fun k => d k * Multiset.card (A k)) 1
      (fun k _ => hterm k)
    simp at this
    omega
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hs
  have hcard : Fintype.card ι = 1 := le_antisymm hcardle Fintype.card_pos
  refine ⟨hcard, fun k => ?_⟩
  have hdk : d k = 1 := Nat.eq_one_of_mul_eq_one_right (hle k)
  refine ⟨hdk, ?_⟩
  have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcardle
  rw [Finset.sum_eq_single k (fun b _ hb => absurd (Subsingleton.elim b k) hb)
    (fun h => absurd (Finset.mem_univ k) h), hdk, one_smul] at hs
  exact hs

theorem numerics_and_rest : Numerics ∧ Rest := ⟨numerics, rest⟩

end GlobalTheory.SixthNumerics
end

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton : Numerics ∧ Rest := by
  atlas_forward_decl GlobalTheory.SixthNumerics.numerics_and_rest
end

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.ClosingSixth

theorem conclusionG6_of_adm : ∀ D : D7, SumRepresentations.admitted D → RbEx D → SumRepresentations.ConclusionG6 D :=
  GlobalTheory.T.conclusionG6_of_all_parts GlobalTheory.T.sixth_decomposition GlobalTheory.T.sixth_weight_statement GlobalTheory.T.sixth_character_equality GlobalTheory.T.mu_character GlobalTheory.T.eigencharacter_of_summand_charZero
    (GlobalTheory.T.residue_count_of_ss_rank GlobalTheory.T.valuation_ring_model GlobalTheory.T.exists_irreducible_constituents_charpoly_product GlobalTheory.T.absIrreducible_constituent_ranks_unique_of_charpoly)
    GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton.1 GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton.2

end GlobalTheory.ClosingSixth
end
