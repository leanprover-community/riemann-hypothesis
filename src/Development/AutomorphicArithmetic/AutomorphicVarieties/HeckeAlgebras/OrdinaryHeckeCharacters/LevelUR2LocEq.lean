import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ModuleStructureOfCommuting
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2LevOut
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemHeckeLevelOfLocalComponentsMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemMaximalCompactOfUnderEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DenseU

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem le_mem_under {l : ℕ} {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) :
    ((l : ℕ) : 𝓞 L) ∈ w.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := by
  change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal
  rw [map_natCast]

private theorem le_cmp_same {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w w' : Plc L}
    (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (g : Ga l L n)
    (hg : cmp n w g ∈ KO (w.adicCompletion L) (Fin n)) : cmp n w' g ∈ KO (w'.adicCompletion L) (Fin n) := by
  by_cases h' : ((l : ℕ) : 𝓞 L) ∉ w'.asIdeal
  · have h0 : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := by
      rw [le_mem_under, ← h, ← le_mem_under]
      exact h'
    obtain ⟨_, x, rfl⟩ := g
    unfold CaseU.cmp at hg ⊢
    rw [dif_pos h0] at hg
    rw [dif_pos h']
    exact UpperTheory.mem_maximalCompact_of_under_eq L n x w w' h hg
  · unfold CaseU.cmp
    rw [dif_neg h']
    exact one_mem _

theorem UpperTheory.V.Hi.levelUR2LevEq :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K₀ : (hset Q₀ τ₀).Lev) (K : (hset Q τ₀).Lev), V₀.S' = s.S → (∀ q, K.1 q = KO ((Q.wq q).adicCompletion L) (Fin n)) → ∀ u : Ub n s, u ∈ (hset Q τ₀).lev K ↔ u ∈ (hset Q₀ τ₀).lev K₀ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c m τ₀ K₀ K h0 hK u
  have hem : ∀ q : Q₀.Q, False := fun q => by
    refine Q₀.notS q ?_
    rw [← h0, Q₀.range]
    exact Or.inr ⟨q, rfl⟩
  constructor
  · intro hu
    obtain ⟨h1, h2⟩ := levelUR2LevOut l L Ω s n hn V Q c m τ₀ K u hu
    refine UpperTheory.mem_heckeLevel_of_local_components_mem l L Ω s n hn V₀ Q₀ c m τ₀ K₀ u (fun w hw => ?_) fun q => (hem q).elim
    by_cases hw' : w.under (𝓞 (Lp L)) ∈ V.S'
    · rw [Q.range] at hw'
      rcases hw' with hw' | ⟨q, hq⟩
      · exact (hw (h0 ▸ hw')).elim
      · refine le_cmp_same (w := Q.wq q) hq.symm _ ?_
        have h3 := h2 q
        rw [hK q] at h3
        exact h3
    · exact h1 w hw'
  · intro hu
    obtain ⟨h1, _⟩ := levelUR2LevOut l L Ω s n hn V₀ Q₀ c m τ₀ K₀ u hu
    refine UpperTheory.mem_heckeLevel_of_local_components_mem l L Ω s n hn V Q c m τ₀ K u (fun w hw => h1 w fun hw' => hw ?_) fun q => ?_
    · rw [Q.range]
      exact Or.inl (h0 ▸ hw')
    · rw [hK q]
      exact h1 _ (h0 ▸ Q.notS q)
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem lq_lc {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    (r : Resid F O n) : IsLocallyConstant fun g : F.G₀ => r.Dbar.chi (MonoidAlgebra.single g 1) := by
  have h : IsLocallyConstant fun (g : F.G₀) (i : Fin n) => r.chib i g :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
      have := Filter.eventually_all.2 fun i => (JEx.lc_of_open _ (r.chib_open i)).eventually_eq x
      exact this.mono fun y hy => funext hy
  have e : (fun g : F.G₀ => r.Dbar.chi (MonoidAlgebra.single g 1)) =
      (fun t : Fin n → (ResidueField O)ˣ => (Matrix.diagonal fun i => (t i : ResidueField O)).charpoly) ∘
        fun (g : F.G₀) (i : Fin n) => r.chib i g := by
    funext g
    rw [Resid.Dbar, (AlgebraTools.Det.repApi _).2.1]
    rfl
  rw [e]
  exact h.comp _

private theorem lq_dense {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (hc : Continuous p)
    (hs : Function.Surjective p) {S : Set X} (hS : Dense S) {T : Set Y} (h : ∀ x ∈ S, p x ∈ T) : Dense T :=
  (hs.denseRange.dense_image hc hS).mono (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

attribute [-instance] UpperTheory.V.GradeZeroInterpolatingElement.instIsLocalRingSubtypePadicAlgClMemSubalgebraPadicIntO in
theorem UpperTheory.V.Hi.levelUR2LocEq :
    Af.HypothesesH → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (r : Resid V₀.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : HD Q₀ ι Λ) (K₀ : (hset Q₀ R.τ₀).Lev) (K : (hset Q R.τ₀).Lev), V₀.S' = s.S → (∀ q, K.1 q = KO ((Q.wq q).adicCompletion L) (Fin n)) → ∀ (p : V.frame.G₀ →* V₀.frame.G₀), Continuous p → Function.Surjective p → (∀ g, p (V.pr g) = V₀.pr g) → ∀ j : (hset Q R.τ₀).Op → (hset Q₀ R.τ₀).Op, (∀ x : Vl l L × Fin n, j (.inr x) = .inr x) → (∀ (w : (hset Q R.τ₀).Wp) (k : Fin n), ∃ hw, j (.inl (w, k)) = .inl (⟨w.1, hw⟩, k)) → (∀ i, (hset Q R.τ₀).op Λ.Λ i = (hset Q₀ R.τ₀).op Λ.Λ (j i)) ∧ ∀ f : (hset Q₀ R.τ₀).X.Fn Λ.Λ R.m, f ∈ (hset Q R.τ₀).MK (A := Λ.Λ) R.θ (fun i => R.a (j i)) K ↔ f ∈ (hset Q₀ R.τ₀).MK R.θ R.a K₀ := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c r ι Λ R K₀ K h0 hK p hp hs hpr j hj1 hj2
  have hop : ∀ i, (hset Q R.τ₀).op Λ.Λ i = (hset Q₀ R.τ₀).op Λ.Λ (j i) := by
    rintro (⟨w, k⟩ | x)
    · obtain ⟨hw, e⟩ := hj2 w k
      exact Eq.trans rfl (congrArg ((hset Q₀ R.τ₀).op Λ.Λ) e).symm
    · exact Eq.trans rfl (congrArg ((hset Q₀ R.τ₀).op Λ.Λ) (hj1 x)).symm
  refine ⟨hop, fun f => ?_⟩
  have hAx := axU hP.litN l L Ω s n hn V₀ Q₀ c _ R.τ₀
  have hAx' := axU hP.litN l L Ω s n hn V Q c _ R.τ₀
  obtain ⟨hdom, hden⟩ := denseU hP.litN l L Ω s n hn V₀ Q₀ c _ R.τ₀ r Λ R.θ R.theta
  let lam : Wt L l n := fun _ => ⟨0, fun _ _ _ => le_rfl⟩
  have haut := autU hP l L Ω s n hn V₀ Q₀ c r ι _ R.τ₀ R.type
  have hlev : (hset Q R.τ₀).lev K = (hset Q₀ R.τ₀).lev K₀ :=
    Subgroup.ext fun u => levelUR2LevEq l L Ω s n hn V₀ V Q₀ Q c _ R.τ₀ K₀ K h0 hK u
  have key := levelUR2H3Abs hP.litN L Ω l n c _ hAx Λ.Λ R.θ R.isWt hdom ι _ haut lam trivial (hden lam) R.a K₀
    _ (lq_lc r) R.res.frob _ j (fun x => ⟨.inr x, hj1 x⟩) (lq_dense hp hs hAx'.dense (by
      rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
      obtain ⟨hw0, -⟩ := hj2 ⟨w, hw⟩ ⟨0, hn⟩
      refine ⟨⟨w, hw0⟩, fun k => ?_, B, σ, hB, hσ, hpr _⟩
      obtain ⟨_, e⟩ := hj2 ⟨w, hw⟩ k
      exact ⟨_, e⟩))
  rw [← key]
  have e1 : (hset Q R.τ₀).op Λ.Λ = fun i => (hset Q₀ R.τ₀).op Λ.Λ (j i) := funext hop
  have e2 : (hset Q R.τ₀).MK (A := Λ.Λ) R.θ (fun i => R.a (j i)) K = _ :=
    congrArg₂ (fun U o => locPart ((hset Q₀ R.τ₀).X.Ord ((hset Q₀ R.τ₀).τA Λ.Λ) R.θ U) o
      fun i => algebraMap c.O Λ.Λ (R.a (j i))) hlev e1
  exact SetLike.ext_iff.1 e2 f
end
