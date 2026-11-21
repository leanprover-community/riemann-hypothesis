import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MonomialLinesPermutation
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeHostAutPermutation
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueHostAutEmbedding
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTiesDistinctGeneric
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootModelOriginCompatibility
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeDivisorsOfOmegaBundle

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Top.PermInv

theorem exists_word_multiset {α : Type} (s : Multiset α) :
    ∃ w : Fin (Multiset.card s) → α, ∑ k, ({w k} : Multiset α) = s := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨Fin.elim0, by simp⟩
  | cons a s ih =>
    obtain ⟨w, hw⟩ := ih
    rw [Multiset.card_cons]
    refine ⟨Fin.cons a w, ?_⟩
    rw [Fin.sum_univ_succ]
    simp [hw, Multiset.singleton_add]

theorem degree_eq_card {α : Type} (μ : α →₀ ℕ) : μ.degree = Multiset.card (Finsupp.toMultiset μ) := by
  rw [Finsupp.card_toMultiset]
  rfl

theorem exists_word {α : Type} (μ : α →₀ ℕ) (d : ℕ) (h : μ.degree = d) :
    ∃ w : Fin d → α, ∑ k, Finsupp.single (w k) 1 = μ := by
  subst h
  have hc : Multiset.card (Finsupp.toMultiset μ) = μ.degree := (degree_eq_card μ).symm
  obtain ⟨w, hw⟩ := exists_word_multiset (Finsupp.toMultiset μ)
  refine ⟨fun k => w (Fin.cast hc.symm k), ?_⟩
  classical
  have H : Finsupp.toMultiset (∑ k, Finsupp.single (w (Fin.cast hc.symm k)) 1) = Finsupp.toMultiset μ := by
    rw [map_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    exact (Fintype.sum_equiv (finCongr hc.symm) _ _ (fun k => rfl)).trans hw
  simpa [Finsupp.toMultiset_toFinsupp] using congrArg Multiset.toFinsupp H

theorem degree_mapDomain {α β : Type} (f : α → β) (μ : α →₀ ℕ) :
    (Finsupp.mapDomain f μ).degree = μ.degree := by
  rw [degree_eq_card, degree_eq_card, ← Finsupp.toMultiset_map, Multiset.card_map]

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem arMono_word (M : RootModel Ψ N) (II : IntersectionSystem) (hII : IsIntersectionSystem II) (t : ℝ)
    (w : Fin (dimFl Ψ N + 1) → Ψ × Fin N) :
    M.arMono II t (Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1)) =
      II _ _ M.P _ (fun j => M.x t (w j)) / (M.δ : ℝ) := by
  have e : Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1) =
      ∑ k, Finsupp.single (some (w k)) (1 : ℕ) := by
    simp [Finsupp.mapDomain_finsetSum]
  obtain ⟨hdeg, -, -, hv⟩ := GlobalTheory.T.monomial_lines_permutation II hII M.K M.ι M.P (dimFl Ψ N + 1) _ (M.line t) (fun k => some (w k))
    M.arith (by rintro (_ | r); exacts [M.A_smooth, M.x_smooth t r])
  have hnone : (∑ k, Finsupp.single (some (w k)) (1 : ℕ) : Option (Ψ × Fin N) →₀ ℕ) none = 0 := by
    simp [Finsupp.finsetSum_apply]
  rw [e, RootModel.arMono, if_pos hdeg, hnone, pow_zero, mul_one, hv]
  rfl

end GlobalTheory.CompanionTheory.Ar.Top.PermInv

namespace GlobalTheory.CompanionTheory.Ar.Top.PermInv

theorem limUnder_arMono_perm {Ψ : Type} [Fintype Ψ] {N : ℕ} (M M' : RootModel Ψ N) (II : IntersectionSystem)
    (hII : IsIntersectionSystem II) (hM : M.Converges II) (hM' : M'.Converges II) (σ : Equiv.Perm Ψ)
    (hlim : ∀ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N, Tendsto (fun t => II _ _ M.P _ (fun j => M.x t (σ (w j).1, (w j).2)) /
      (M.δ : ℝ) - II _ _ M'.P _ (fun j => M'.x t (w j)) / (M'.δ : ℝ)) (𝓝[>] 0) (𝓝 0))
    (μ : Ψ × Fin N →₀ ℕ) :
    (limUnder (𝓝[>] (0 : ℝ)) fun t => M.arMono II t
        (Finsupp.mapDomain some (Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) μ))) =
      limUnder (𝓝[>] (0 : ℝ)) fun t => M'.arMono II t (Finsupp.mapDomain some μ) := by
  by_cases hd : μ.degree = dimFl Ψ N + 1
  · obtain ⟨w, rfl⟩ := exists_word μ _ hd
    have e : Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (∑ k, Finsupp.single (w k) 1) =
        ∑ k, Finsupp.single (σ (w k).1, (w k).2) (1 : ℕ) := by
      simp [Finsupp.mapDomain_finsetSum]
    have hf : (fun t => M.arMono II t (Finsupp.mapDomain some
        (Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (∑ k, Finsupp.single (w k) 1)))) =
        fun t => II _ _ M.P _ (fun j => M.x t (σ (w j).1, (w j).2)) / (M.δ : ℝ) := by
      funext t
      rw [e]
      exact arMono_word M II hII t (fun k => (σ (w k).1, (w k).2))
    have hg : (fun t => M'.arMono II t (Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1))) =
        fun t => II _ _ M'.P _ (fun j => M'.x t (w j)) / (M'.δ : ℝ) := by
      funext t
      exact arMono_word M' II hII t w
    obtain ⟨L1, h1⟩ := hM (Finsupp.mapDomain some
        (Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (∑ k, Finsupp.single (w k) 1)))
    obtain ⟨L2, h2⟩ := hM' (Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1))
    rw [h1.limUnder_eq, h2.limUnder_eq]
    rw [hf] at h1
    rw [hg] at h2
    exact sub_eq_zero.1 (tendsto_nhds_unique (h1.sub h2) (hlim w))
  · have h0 : ∀ (K : RootModel Ψ N) (m : Ψ × Fin N →₀ ℕ), m.degree = μ.degree →
        (fun t => K.arMono II t (Finsupp.mapDomain some m)) = fun _ => 0 := by
      intro K m hm
      funext t
      rw [RootModel.arMono, if_neg (by rw [degree_mapDomain, hm]; exact hd)]
    rw [h0 M _ (degree_mapDomain _ μ), h0 M' μ rfl]

theorem propA_of_limits : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : GlobalTheory.CompanionTheory.Ar.Top.RootTower Ψ N)
    (II : IntersectionSystem) (Γ : Subgroup (Equiv.Perm Ψ)), T.Conv II → (∀ τ τ' : Ψ, ∃ s ∈ Γ, s τ = τ') →
    (∀ s ∈ Γ, ∀ B : ℕ, 2 ≤ B → ∃ π : Equiv.Perm T.Comp, ∀ (c : T.Comp)
      (w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N),
      Tendsto (fun t => II _ _ (T.M B c).P _ (fun j => (T.M B c).x t (s (w j).1, (w j).2)) / (T.M B c).δ -
        II _ _ (T.M B (π c)).P _ (fun j => (T.M B (π c)).x t (w j)) / (T.M B (π c)).δ) (𝓝[>] 0) (𝓝 0)) →
    IsIntersectionSystem II → T.PropA II := by
  intro Ψ _ _ N T II Γ hC htr hlim hII
  refine ⟨Γ, htr, fun σ hσ B hB F => ?_⟩
  obtain ⟨π, hπ⟩ := hlim σ hσ B hB
  have hb : ∀ (m : Option (Ψ × Fin N) →₀ ℕ) (a : ℝ),
      (monomial m a : RPA Ψ N) = a • (basisMonomials (Option (Ψ × Fin N)) ℝ) m := by
    intro m a
    simp [coe_basisMonomials, smul_monomial]
  have hmono : ∀ (c : T.Comp) (μ : Ψ × Fin N →₀ ℕ) (a : ℝ),
      T.PPc II B c (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) (monomial μ a)) =
        T.PPc II B (π c) (monomial μ a) := by
    intro c μ a
    simp only [RootTower.PPc, toA, rename_monomial]
    rw [hb, hb, map_smul, map_smul, RootModel.PP, RootModel.PP, Module.Basis.constr_basis,
      Module.Basis.constr_basis,
      limUnder_arMono_perm (T.M B c) (T.M B (π c)) II hII (hC B c) (hC B (π c)) σ (hπ c) μ]
  have hsum : ∀ (c : T.Comp) (f : RP Ψ N →ₐ[ℝ] RP Ψ N),
      T.PPc II B c (f F) = ∑ μ ∈ F.support, T.PPc II B c (f (monomial μ (F.coeff μ))) := by
    intro c f
    conv_lhs => rw [F.as_sum]
    simp only [RootTower.PPc, toA, map_sum]
  calc T.PPt II B (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F)
      = ∑ c, ∑ μ ∈ F.support, T.PPc II B (π c) (monomial μ (F.coeff μ)) := by
        unfold RootTower.PPt
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hsum c (rename (fun x : Ψ × Fin N => (σ x.1, x.2)))]
        exact Finset.sum_congr rfl fun μ _ => hmono c μ _
    _ = ∑ c, ∑ μ ∈ F.support, T.PPc II B c (monomial μ (F.coeff μ)) :=
        Equiv.sum_comp π (fun c => ∑ μ ∈ F.support, T.PPc II B c (monomial μ (F.coeff μ)))
    _ = T.PPt II B F := by
        unfold RootTower.PPt
        refine Finset.sum_congr rfl fun c _ => ?_
        have := hsum c (AlgHom.id ℝ (RP Ψ N))
        simpa using this.symm

end GlobalTheory.CompanionTheory.Ar.Top.PermInv
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_symmetry_limit_compat : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : GlobalTheory.CompanionTheory.Ar.Top.RootTower Ψ N) (II : IntersectionSystem) (Γ : Subgroup (Equiv.Perm Ψ)), T.Conv II → (∀ τ τ' : Ψ, ∃ s ∈ Γ, s τ = τ') → (∀ s ∈ Γ, ∀ B : ℕ, 2 ≤ B → ∃ π : Equiv.Perm T.Comp, ∀ (c : T.Comp) (w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N), Tendsto (fun t => II _ _ (T.M B c).P _ (fun j => (T.M B c).x t (s (w j).1, (w j).2)) / (T.M B c).δ - II _ _ (T.M B (π c)).P _ (fun j => (T.M B (π c)).x t (w j)) / (T.M B (π c)).δ) (𝓝[>] 0) (𝓝 0)) → IsIntersectionSystem II → T.PropA II := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.PermInv.propA_of_limits
end

section
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def relabGroup (H : Host E) : Subgroup (Equiv.Perm (CMType H)) where
  carrier := {s | ∃ g : HostAut H, ∀ τ, (s τ).1 = τ.1.comp g.σ.toRingHom}
  one_mem' := ⟨HostAut.refl H, fun τ => by ext x; rfl⟩
  mul_mem' := by
    rintro s₁ s₂ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    refine ⟨⟨g₁.σ.trans g₂.σ, by simp [g₁.fix, g₂.fix]⟩, fun τ => ?_⟩
    rw [Equiv.Perm.mul_apply, h₁, h₂]
    ext x; rfl
  inv_mem' := by
    rintro s ⟨g, h⟩
    refine ⟨g.symm, fun τ => ?_⟩
    have e := h (s⁻¹ τ)
    rw [show s (s⁻¹ τ) = τ from Equiv.apply_symm_apply s τ] at e
    rw [e]
    ext x
    show _ = (s⁻¹ τ).1 (g.σ (g.σ.symm x))
    rw [RingEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA

open GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA in
theorem GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA.propA_of_hodgeTower : CmpPair → TwistAut → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (S : ℕ → Finset ℕ) (n : ℕ) (tie : ∀ B k, HodgeTie Y (S B) n (T.M B k)), IsGalois ℚ E → Mono (spMap β) → T.Conv II → (∀ B k k', ∀ p ∈ S B, (tie B k').A.R p = (tie B k).A.R p) → (∀ (B : ℕ) (Φ : Xo.X ≅ Xo.X), Φ.hom ≫ Xo.s = Xo.s → ∃ π : Equiv.Perm T.Comp, ∀ k, IsImageCpt Φ (tie B k).A (tie B (π k)).A) → T.PropA II := by
  intro hCmp hTw II hII E _ _ _ H D l Xo c O _ β Y _ T S n tie hGal hMono hConv hR hPerm
  refine GlobalTheory.T.tower_symmetry_limit_compat (CMType H) (D.p + D.q) T II (relabGroup H) hConv ?_ ?_ hII.1
  · intro τ τ'
    obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_host_aut_embedding E H τ.1 τ'.1 τ.2 τ'.2
    obtain ⟨π, hπ, -⟩ := GlobalTheory.T.cm_type_host_aut_permutation E H l c g
    exact ⟨π, ⟨g, hπ⟩, Subtype.ext ((hπ τ).trans hg.symm)⟩
  · intro s hs B _
    obtain ⟨g₀, hg₀⟩ := hs
    have hinv : ∀ τ, (s⁻¹ τ).1 = τ.1.comp g₀.symm.σ.toRingHom := by
      intro τ
      have e := hg₀ (s⁻¹ τ)
      rw [show s (s⁻¹ τ) = τ from Equiv.apply_symm_apply s τ] at e
      rw [e]
      ext x
      show _ = (s⁻¹ τ).1 (g₀.σ (g₀.σ.symm x))
      rw [RingEquiv.apply_symm_apply]
    obtain ⟨⟨a⟩, hA⟩ := hTw E H D l Xo g₀.symm
    obtain ⟨h, Φ, hΦ, ⟨m⟩⟩ := hA a
    obtain ⟨πc, himg⟩ := hPerm B Φ hΦ
    refine ⟨πc, fun k w => ?_⟩
    have key := hCmp II hII E H D l Xo c O β Y g₀.symm Φ m.toSABMap s⁻¹ (S B) n (T.M B k) (T.M B (πc k))
      (tie B k) (tie B (πc k)) hMono hΦ hinv (himg k) (fun p hp => hR B k (πc k) p hp)
      (fun j => (s (w j).1, (w j).2))
    have e2 : ∀ x, s⁻¹ (s x) = x := fun x => Equiv.symm_apply_apply s x
    simpa only [e2, Prod.mk.eta] using key
end

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tie_galois : CmpPair → TwistAut → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (S : ℕ → Finset ℕ) (n : ℕ) (tie : ∀ B k, HodgeTie Y (S B) n (T.M B k)), IsGalois ℚ E → Mono (spMap β) → T.Conv II → (∀ B k k', ∀ p ∈ S B, (tie B k').A.R p = (tie B k).A.R p) → (∀ (B : ℕ) (Φ : Xo.X ≅ Xo.X), Φ.hom ≫ Xo.s = Xo.s → ∃ π : Equiv.Perm T.Comp, ∀ k, IsImageCpt Φ (tie B k).A (tie B (π k)).A) → T.PropA II := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA.propA_of_hodgeTower
end

section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerPropA

theorem mono_spMap_ringOfIntegers (F : Type) [Field F] [NumberField F] :
    Mono (spMap (algebraMap (𝓞 F) F)) := by
  have := IsPreimmersion.of_isLocalization (S := F) (nonZeroDivisors (𝓞 F))
  exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 F) F))))

theorem genPt_eq_of_factor {X : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {a : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X}
    {g₁ : Ω₁ →+* Ω} {g₂ : Ω₂ →+* Ω}
    (h₁ : a = Spec.map (CommRingCat.ofHom g₁) ≫ ξ₁) (h₂ : a = Spec.map (CommRingCat.ofHom g₂) ≫ ξ₂) :
    genPt ξ₁ = genPt ξ₂ := by
  have e₁ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₁ = a w := by
    intro w
    rw [h₁, Scheme.Hom.comp_apply]
    exact congrArg ξ₁ (Subsingleton.elim (α := PrimeSpectrum Ω₁) _ _)
  have e₂ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₂ = a w := by
    intro w
    rw [h₂, Scheme.Hom.comp_apply]
    exact congrArg ξ₂ (Subsingleton.elim (α := PrimeSpectrum Ω₂) _ _)
  exact (e₁ (IsLocalRing.closedPoint Ω)).trans (e₂ (IsLocalRing.closedPoint Ω)).symm

theorem propA_of_origin : CmpPair → TwistAut → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : TowerOrigin Y T), IsGalois ℚ E → (∀ B a, (o.Or B a).𝔐.OmVB) → (∀ a, (∀ x : (o.Sys a).X, ∃ (U : Set (o.Sys a).X) (lam : (o.Sys a).X → Fin ((o.Fx a).m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, (o.Sys a).A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • (o.Fx a).pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ ((o.Sys a).A.chart j).source → (fderiv ℂ (fun z i => lam (((o.Sys a).A.chart j).symm z) i / lam (((o.Sys a).A.chart j).symm z) p) ((o.Sys a).A.chart j x)).ker = ⊥)) → (∀ B a a', ∀ p ∈ o.S B, (o.Or B a').𝔐.R p = (o.Or B a).𝔐.R p) → T.Conv II → T.PropA II := by
  intro hpair htw II hII E _ _ _ H D l Xo c Y _ T o hgal hOm hhol hR hconv
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := ⟨⟩
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := mono_spMap_ringOfIntegers c.F
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hdisc : ∀ B, ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ o.S B := by
    intro B p hp hd
    rw [o.S_iff]
    refine ⟨hp, Or.inr ?_⟩
    rw [o.bad_iff]
    exact ⟨hp, Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _⟩
  have hex : ∀ B a, ∃ t : HodgeTie Y (o.S B) (Module.finrank ℚ c.F) (T.M B a), t.A = (o.Or B a).𝔐 := by
    intro B a
    obtain ⟨-, ⟨x, hx⟩, -⟩ := HodgeCpt.basic _ _ _ _ _ _ _ _ Y _ _ _ _ _ (o.Or B a).𝔐 hinj
    exact GlobalTheory.T.prime_divisors_of_omega_bundle E H D l Xo c (𝓞 c.F) _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) (hOm B a)
      (hdisc B) (GlobalTheory.T.root_model_origin_compatibility E H D l Xo c (𝓞 c.F) _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) x hx
        hmono (hhol a))
  choose tie htie using hex
  have hgen : ∀ B a, genPt (tie B a).A.ξ₀ = genPt (o.Fx a).ξf := by
    intro B a
    rw [htie B a]
    exact genPt_eq_of_factor (o.Or B a).𝔐.fn_over (o.Or B a).g_over
  refine GlobalTheory.T.hodge_tie_galois hpair htw II hII E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y T o.S
    (Module.finrank ℚ c.F) tie hgal hmono hconv ?_ ?_
  · intro B k k' p hp
    rw [htie B k', htie B k]
    exact hR B k k' p hp
  · intro B Φ hΦ
    refine GlobalTheory.T.hodge_ties_distinct_generic E H D l Xo c (𝓞 c.F) _ Y (o.S B) _ T.Comp (T.M B) (tie B) hmono ?_ ?_ Φ hΦ
    · intro k k' h
      apply o.comp_inj
      simpa only [hgen] using h
    · intro q hq
      obtain ⟨a, ha⟩ := o.comp_onto q hq
      exact ⟨a, (hgen B a).trans ha⟩

end GlobalTheory.CompanionTheory.Ar.TowerPropA
end
end
