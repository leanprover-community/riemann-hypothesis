import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtension
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueSat
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.X_join_model
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPluckerFrame

section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PluckerBirat

theorem exists_minor_ne_zero {Ω : Type*} [Field Ω] {M i : ℕ} (A : Fin M → Fin i → Ω)
    (hA : ∀ t : Fin i → Ω, t ∈ Submodule.span Ω (Set.range A)) :
    ∃ I : Fin i → Fin M, Matrix.det (Matrix.of fun a b : Fin i => A (I a) b) ≠ 0 := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent Ω (Set.range A)
  have htop : (⊤ : Submodule Ω (Fin i → Ω)) ≤ Submodule.span Ω (Set.range ((↑) : b → Fin i → Ω)) := by
    rw [Subtype.range_coe, hspan]
    exact fun t _ => hA t
  let bas := Module.Basis.mk hli htop
  have e : b ≃ Fin i := bas.indexEquiv (Pi.basisFun Ω (Fin i))
  have hI : ∀ a : Fin i, ∃ l, A l = (e.symm a : Fin i → Ω) := fun a => hb (e.symm a).2
  choose I hI using hI
  refine ⟨I, ?_⟩
  have hrow : LinearIndependent Ω (Matrix.of fun a b : Fin i => A (I a) b).row := by
    have : (Matrix.of fun a b : Fin i => A (I a) b).row = ((↑) : b → Fin i → Ω) ∘ e.symm := by
      funext a
      exact hI a
    rw [this]
    exact hli.comp _ e.symm.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.1 hrow
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

theorem chartRing_le_fnField (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type*} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type}
    (x : (Σ k, ι k) → Ω) (s : ∀ k, ι k) {r : Ω} (hr : r ∈ chartRing O (mseg x) s) :
    r ∈ fnField O x := by
  rw [chartRing] at hr
  induction hr using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨t, rfl⟩ := hy
    show (∏ k, x ⟨k, t k⟩) / (∏ k, x ⟨k, s k⟩) ∈ fnField O x
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => Subfield.subset_closure (Or.inr ⟨⟨k, (t k, s k)⟩, rfl⟩)
  | algebraMap c => exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Ω : Type*} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]

theorem mem_span_of_twistedDualGens (E : ChartBundle O (mseg x) N V) {M : ℕ} {a : K → ℤ}
    {φ : Fin M → Module.Dual Ω V} (hg : IsTwistedDualGens x E a φ) {s₀ : ∀ k, ι k}
    (hs : mseg x s₀ ≠ 0) (ψ : Module.Dual Ω V) : ψ ∈ Submodule.span Ω (Set.range φ) := by
  classical
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := E.frame s₀ hs
  have hne : ∃ l, f l ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
  obtain ⟨l, hl⟩ := hne
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  let bas := Module.Basis.mk hli hsp.ge
  obtain ⟨kg, G, hG, hgen⟩ := GroundTheory.Heights₂.Heights.Model.chartBundle_exists_gens E hs
  have hcoord : ∀ q, bas.coord q ∈ Submodule.span Ω (Set.range φ) := by
    intro q
    have h1 : ∀ g, ∃ n : ℕ, f l ^ n * bas.coord q (G g) ∈ chartRing O (mseg x) s₀ := by
      intro g
      obtain ⟨a', ha', he⟩ := (hiff (G g)).1 ⟨0, by simpa using hG g⟩
      have : bas.coord q (G g) = a' q := by
        rw [he, map_sum]
        simp only [map_smul]
        have hbq : ∀ q', bas.coord q (b q') = if q' = q then 1 else 0 := by
          intro q'
          have : b q' = bas q' := (Module.Basis.mk_apply hli hsp.ge q').symm
          rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
        simp [hbq]
      rw [this]
      exact ha' q
    choose n hn using h1
    set n₀ := Finset.univ.sup n with hn₀
    have h2 : ∀ g, f l ^ n₀ * bas.coord q (G g) ∈ chartRing O (mseg x) s₀ := by
      intro g
      have hle : n g ≤ n₀ := Finset.le_sup (Finset.mem_univ g)
      rw [← pow_sub_mul_pow _ hle, mul_assoc]
      exact mul_mem (pow_mem (hf l) _) (hn g)
    have h3 : ∀ v ∈ E.lat s₀, (f l ^ n₀ • bas.coord q) v ∈ chartRing O (mseg x) s₀ := by
      intro v hv
      obtain ⟨β, hβ, rfl⟩ := hgen v hv
      simp only [LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      refine sum_mem fun g _ => ?_
      exact mul_mem (hβ g) (h2 g)
    obtain ⟨u, -, hu⟩ := hg.generate s₀ hs _ h3
    have h4 : f l ^ n₀ • bas.coord q ∈ Submodule.span Ω (Set.range φ) := by
      rw [hu]
      exact sum_mem fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    have h5 := Submodule.smul_mem _ (f l ^ n₀)⁻¹ h4
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul] at h5
  rw [← bas.sum_dual_apply_smul_coord ψ]
  exact sum_mem fun q _ => Submodule.smul_mem _ _ (hcoord q)

theorem exists_flagMinor_ne_zero {M : ℕ} {φ : Fin M → Module.Dual Ω V}
    (hφ : ∀ ψ : Module.Dual Ω V, ψ ∈ Submodule.span Ω (Set.range φ))
    (w : Module.Basis (Fin N) Ω V) (i : ℕ) (hi : i ≤ N) :
    ∃ I : Fin i → Fin M, flagMinor φ w i hi I ≠ 0 := by
  classical
  let L : Module.Dual Ω V →ₗ[Ω] (Fin i → Ω) :=
    LinearMap.pi fun b => Module.Dual.eval Ω V (w (Fin.castLE hi b))
  refine exists_minor_ne_zero (fun l b => φ l (w (Fin.castLE hi b))) fun t => ?_
  let ψ : Module.Dual Ω V := ∑ b, t b • w.coord (Fin.castLE hi b)
  have hL : L ψ = t := by
    funext b
    simp [L, ψ, Module.Dual.eval_apply, Finsupp.single_apply, Fin.castLE_inj]
  have h := Submodule.mem_map_of_mem (f := L) (hφ ψ)
  rw [Submodule.map_span, ← Set.range_comp, hL] at h
  exact h

theorem flagMinor_div_mem (E : ChartBundle O (mseg x) N V) {M : ℕ} {a : K → ℤ}
    {φ : Fin M → Module.Dual Ω V} (hg : IsTwistedDualGens x E a φ) {s₀ : ∀ k, ι k}
    (hs : mseg x s₀ ≠ 0) (w : Module.Basis (Fin N) Ω V)
    (hw : ∀ i, ∃ c : O, algebraMap O Ω c ≠ 0 ∧ algebraMap O Ω c • w i ∈ E.lat s₀)
    (i : ℕ) (hi : i ≤ N) (I I' : Fin i → Fin M) :
    flagMinor φ w i hi I / flagMinor φ w i hi I' ∈ fnField O x := by
  classical
  choose c hc0 hc using hw
  have hr : ∀ l b, ∃ r ∈ chartRing O (mseg x) s₀,
      φ l (algebraMap O Ω (c b) • w b) = r * ∏ k, x ⟨k, s₀ k⟩ ^ a k :=
    fun l b => hg.sections s₀ hs l _ (hc b)
  choose r hrm hr using hr
  set T : Ω := ∏ k, x ⟨k, s₀ k⟩ ^ a k with hT
  let D : Fin i → Ω := fun b => (algebraMap O Ω (c (Fin.castLE hi b)))⁻¹ * T
  have hφw : ∀ l b, φ l (w b) = (algebraMap O Ω (c b))⁻¹ * T * r l b := by
    intro l b
    have := hr l b
    rw [map_smul, smul_eq_mul] at this
    field_simp [hc0 b]
    linear_combination this
  have hdet : ∀ J : Fin i → Fin M, flagMinor φ w i hi J = (∏ b, D b) *
      Matrix.det (Matrix.of fun a' b : Fin i => r (J a') (Fin.castLE hi b)) := by
    intro J
    rw [← Matrix.det_mul_row]
    unfold flagMinor
    congr 1
    ext a' b
    simp [hφw, D]
  have hmem : ∀ J : Fin i → Fin M,
      Matrix.det (Matrix.of fun a' b : Fin i => r (J a') (Fin.castLE hi b)) ∈ fnField O x := by
    intro J
    rw [Matrix.det_apply']
    refine sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun b _ => ?_)
    exact chartRing_le_fnField O x s₀ (hrm _ _)
  rw [hdet I, hdet I']
  by_cases hD : ∏ b, D b = 0
  · simp [hD, zero_mem]
  · rw [mul_div_mul_left _ _ hD]
    exact div_mem (hmem I) (hmem I')

end GlobalTheory.CompanionTheory.Ar.Num.PluckerBirat

open GlobalTheory.CompanionTheory.Ar.Num.PluckerBirat in
theorem GlobalTheory.CompanionTheory.Ar.Num.plucker_birat : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (J : Type) [Fintype J] [DecidableEq J] (E : J → ChartBundle O (mseg x) N V) (M : J → ℕ) (a : J → K → ℤ) (φ : ∀ j, Fin (M j) → Module.Dual Ω V), (∀ j, IsTwistedDualGens x (E j) (a j) (φ j)) → ∀ (w : Module.Basis (Fin N) Ω V) (s₀ : ∀ k, ι k), mseg x s₀ ≠ 0 → (∀ k, ∃ I, pluckerCoord φ w ⟨k, I⟩ ≠ 0) ∧ ((∀ j i, ∃ c : O, algebraMap O Ω c ≠ 0 ∧ algebraMap O Ω c • w i ∈ (E j).lat s₀) → fnField O (joinCoord x (pluckerCoord φ w)) = fnField O x) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ J _ _ E M a φ hg w s₀ hs
  refine ⟨fun k => ?_, fun hw => le_antisymm ?_ ?_⟩
  · exact exists_flagMinor_ne_zero (mem_span_of_twistedDualGens (E k.1) (hg k.1) hs) w k.2
      (Nat.lt_succ_iff.mp k.2.2)
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨⟨k, p, q⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · rcases k with k | k
      · exact Subfield.subset_closure (Or.inr ⟨⟨k, (p, q)⟩, rfl⟩)
      · exact flagMinor_div_mem (E k.1) (hg k.1) hs w (hw k.1) k.2 (Nat.lt_succ_iff.mp k.2.2) p q
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨⟨k, p, q⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨Sum.inl k, (p, q)⟩, rfl⟩)
end

section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.CommonFlag

theorem exists_basis_mem {O Ω τ V : Type} [CommRing O] [Field Ω] [Algebra O Ω] [AddCommGroup V]
    [Module Ω V] {N : ℕ} {y : τ → Ω} (B : ChartBundle O y N V) {c : τ} (hc : y c ≠ 0) :
    ∃ w : Module.Basis (Fin N) Ω V, ∀ i, w i ∈ B.lat c := by
  classical
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hsum
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  have hbl : ∀ q, ∃ n : ℕ, f l ^ n • b q ∈ B.lat c := fun q =>
    (hiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by by_cases h : q' = q <;> simp [h]⟩,
      by simp [Pi.single_apply]⟩
  choose n hn using hbl
  refine ⟨(Module.Basis.mk hli hsp.ge).unitsSMul fun q => Units.mk0 (f l ^ n q) (pow_ne_zero _ hl),
    fun q => ?_⟩
  rw [Module.Basis.unitsSMul_apply, Module.Basis.mk_apply]
  exact hn q

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N n : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : Fin (n + 1) → ChartBundle O (mseg x) N V), (∀ j, SameGeneric O x (E 0) (E j)) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω) (EB : Fin (n + 1) → ChartBundle O (mseg (joinCoord x z)) N V) (w : Module.Basis (Fin N) Ω V) (b : Fin (n + 1) → Fin N → K ⊕ K' → ℤ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ fnField O (joinCoord x z) = fnField O x ∧ ∀ j, IsPull O x z (E j) (EB j) ∧ IsFlagFrame (joinCoord x z) (EB j) w (b j) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hx N n V _ _ E hE
  obtain ⟨hK, hx0, hinj, hT⟩ := (PositivityTheory.Xgn.A_join_model.isModelOver_iff x d).1 hx
  choose s₀ hs₀ using hx0
  have hs : mseg x s₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hs₀ k
  obtain ⟨w, hw⟩ := exists_basis_mem (E 0) hs
  have hgen : ∀ j, ∃ (a : K → ℤ) (M : ℕ) (φ : Fin M → Module.Dual Ω V),
      IsTwistedDualGens x (E j) a φ := fun j => by
    obtain ⟨a, ha⟩ := TwistedDualGensExist.proof O Ω K ι x N V (E j)
    exact ⟨a, ha a le_rfl⟩
  choose a M φ hφ using hgen
  obtain ⟨hz, hfn⟩ := GlobalTheory.CompanionTheory.Ar.Num.plucker_birat O Ω K ι x N V (Fin (n + 1)) E M a φ hφ w s₀ hs
  have hfn' := hfn fun j i => by
    obtain ⟨c, hc, hcw⟩ := (hE j s₀ hs).1 (w i) (hw i)
    exact ⟨c, (map_ne_zero_iff _ hinj).2 hc, hcw⟩
  have hpull : ∀ j, ∃ EB : ChartBundle O (mseg (joinCoord x (pluckerCoord φ w))) N V,
      IsPull O x (pluckerCoord φ w) (E j) EB := fun j =>
    (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V (E j)).1 _ _ (pluckerCoord φ w)
  choose EB hEB using hpull
  refine ⟨Fin (n + 1) × Fin (N + 1), inferInstance, inferInstance, pluckerIdx N M, inferInstance,
    pluckerCoord φ w, EB, w, fun j => pluckerDeg (a j) j, ?_, hfn', fun j => ⟨hEB j,
      PositivityTheory.Xgn.t_plucker_frame O Ω K ι x N V (Fin (n + 1)) E M a φ hφ w j (EB j) (hEB j)⟩⟩
  refine (PositivityTheory.Xgn.A_join_model.isModelOver_iff _ d).2 ⟨inferInstance, ?_, hinj, ?_⟩
  · rintro (k | k)
    · exact ⟨s₀ k, hs₀ k⟩
    · exact hz k
  · rw [hfn', hT]

end GlobalTheory.CompanionTheory.Ar.CommonFlag
end
