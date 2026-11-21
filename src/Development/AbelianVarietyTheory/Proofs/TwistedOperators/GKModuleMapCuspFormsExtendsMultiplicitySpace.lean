import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonLevelGrowthExponentGKMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobBdSeminorm
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionSmoothVectorsScalar

section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_level_growth_exponent_gKMap : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ → ∃ (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) ∧ ∀ u, (∀ k ∈ U, k ∈ GfC V → ∀ g, T₀ u (g * k) = T₀ u g) ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T₀ u) ≠ ⊤ := by
  first | exact @GlobalTheory.GKUnif.exists_level_exponent | exact GlobalTheory.GKUnif.exists_level_exponent | (intros; apply GlobalTheory.GKUnif.exists_level_exponent <;> assumption)
end

section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlacePoint_commute_of_ne_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), atTau θ V τ g * atTau θ V τ' g' = atTau θ V τ' g' * atTau θ V τ g := by
  first | exact @GlobalTheory.PointAtPlaceComm.atTau_comm | exact GlobalTheory.PointAtPlaceComm.atTau_comm | (intros; apply GlobalTheory.PointAtPlaceComm.atTau_comm <;> assumption)
end

section
section
open Function

namespace GlobalTheory.FactorwiseExtension

variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
  {E : Type} [AddCommGroup E] [Module ℂ E]

def piecewiseSubmodule (A B : ∀ τ, Submodule ℂ (H τ)) (s : Finset ι) (τ : ι) : Submodule ℂ (H τ) :=
  if τ ∈ s then B τ else A τ

def Invariant (A B : ∀ τ, Submodule ℂ (H τ)) (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E)))
    (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E)) (T₀ : MultilinearMap ℂ H E) (s : Finset ι)
    (T : MultilinearMap ℂ H E) : Prop :=
  (∀ u, (∀ τ, u τ ∈ A τ) → T u = T₀ u) ∧
  (∀ τ, τ ∉ s → ∀ u : ∀ τ, H τ, (∀ τ', τ' ≠ τ → u τ' ∈ piecewiseSubmodule A B s τ') →
      ∀ r ∈ Rk τ, ∀ x ∈ A τ, T (update u τ (r.1 x)) = r.2 (T (update u τ x))) ∧
  (∀ τ, τ ∈ s → ∀ u : ∀ τ, H τ, (∀ τ', τ' ≠ τ → u τ' ∈ piecewiseSubmodule A B s τ') →
      T.toLinearMap u τ ∈ C τ ∧
      ∀ r ∈ Rg τ, ∀ x ∈ B τ, T (update u τ (r.1 x)) = r.2 (T (update u τ x)))

theorem toLinearMap_congr (T : MultilinearMap ℂ H E) {w w' : ∀ τ, H τ} (i : ι)
    (h : ∀ j, j ≠ i → w j = w' j) : T.toLinearMap w i = T.toLinearMap w' i := by
  ext x
  simp only [MultilinearMap.toLinearMap_apply]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [update_of_ne hj, h j hj]

theorem toLinearMap_update_add (T : MultilinearMap ℂ H E) {i j : ι} (h : i ≠ j) (w : ∀ τ, H τ)
    (x y : H i) : T.toLinearMap (update w i (x + y)) j =
      T.toLinearMap (update w i x) j + T.toLinearMap (update w i y) j := by
  ext a
  simp only [MultilinearMap.toLinearMap_apply, LinearMap.add_apply]
  rw [update_comm h, update_comm h, update_comm h, T.map_update_add]

theorem toLinearMap_update_smul (T : MultilinearMap ℂ H E) {i j : ι} (h : i ≠ j) (w : ∀ τ, H τ)
    (c : ℂ) (x : H i) : T.toLinearMap (update w i (c • x)) j = c • T.toLinearMap (update w i x) j := by
  ext a
  simp only [MultilinearMap.toLinearMap_apply, LinearMap.smul_apply]
  rw [update_comm h, update_comm h, T.map_update_smul]

end GlobalTheory.FactorwiseExtension

namespace GlobalTheory.FactorwiseExtension

variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
  {E : Type} [AddCommGroup E] [Module ℂ E]

theorem invariant_insert (A B : ∀ τ, Submodule ℂ (H τ)) (hAB : ∀ τ, A τ ≤ B τ)
    (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E)))
    (hRk : ∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ A τ, r.1 x ∈ A τ) (hRg : ∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ B τ, r.1 x ∈ B τ)
    (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E))
    (hC : ∀ τ, ∀ L ∈ C τ, ∀ L' : H τ →ₗ[ℂ] E, (∀ x ∈ B τ, L' x = L x) → L' ∈ C τ)
    (hext : ∀ τ (L : H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ A τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ B τ, L' (r.1 x) = r.2 (L' x)) ∧ ∀ x ∈ A τ, L' x = L x)
    (huniq : ∀ τ, ∀ L ∈ C τ, (∀ x ∈ A τ, L x = 0) → ∀ x ∈ B τ, L x = 0)
    (hpostC : ∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ')
    (hbs : ∀ τ τ', τ ≠ τ' → ∀ F : H τ →ₗ[ℂ] H τ' →ₗ[ℂ] E, (∀ w ∈ B τ, F w ∈ C τ') →
      (∀ a ∈ A τ', F.flip a ∈ C τ) → ∀ b ∈ B τ', F.flip b ∈ C τ)
    (T₀ : MultilinearMap ℂ H E) (s : Finset ι) (τ₀ : ι) (hτ₀ : τ₀ ∉ s) (T : MultilinearMap ℂ H E)
    (hT : Invariant A B Rk Rg C T₀ s T) : ∃ T', Invariant A B Rk Rg C T₀ (insert τ₀ s) T' := by
  obtain ⟨hTa, hTb, hTc⟩ := hT
  set D' := piecewiseSubmodule A B (insert τ₀ s) with hD'
  have hD'0 : D' τ₀ = B τ₀ := if_pos (Finset.mem_insert_self τ₀ s)
  have hBD' : ∀ x ∈ B τ₀, x ∈ D' τ₀ := fun x hx => by rw [hD'0]; exact hx
  have hD'B : ∀ x ∈ D' τ₀, x ∈ B τ₀ := fun x hx => by rw [← hD'0]; exact hx
  have hD'ne : ∀ τ, τ ≠ τ₀ → D' τ = piecewiseSubmodule A B s τ := by
    intro τ hτ
    simp only [hD', piecewiseSubmodule, Finset.mem_insert, hτ, false_or]
  have hAD' : ∀ τ, ∀ x ∈ A τ, x ∈ D' τ := by
    intro τ x hx
    simp only [hD', piecewiseSubmodule]
    split_ifs
    · exact hAB τ hx
    · exact hx
  have hD0 : piecewiseSubmodule A B s τ₀ = A τ₀ := if_neg hτ₀

  have hret := fun τ => (D' τ).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  choose g hg using hret
  let R : ∀ τ, H τ →ₗ[ℂ] H τ := fun τ => (D' τ).subtype ∘ₗ g τ
  have hRmem : ∀ τ x, R τ x ∈ D' τ := fun τ x => (g τ x).2
  have hRid : ∀ τ, ∀ x ∈ D' τ, R τ x = x := by
    intro τ x hx
    have := congrArg (fun f => ((f ⟨x, hx⟩ : D' τ) : H τ)) (hg τ)
    simpa [R] using this

  have goodL : ∀ w : ∀ τ, H τ, (∀ τ', τ' ≠ τ₀ → w τ' ∈ D' τ') →
      ∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀, T.toLinearMap w τ₀ (r.1 x) = r.2 (T.toLinearMap w τ₀ x) := by
    intro w hw r hr x hx
    simp only [MultilinearMap.toLinearMap_apply]
    exact hTb τ₀ hτ₀ w (fun τ' h => by rw [← hD'ne τ' h]; exact hw τ' h) r hr x hx
  choose! Ext hExtC hExtG hExtA using hext τ₀
  have ExtAdd : ∀ L₁ L₂ : H τ₀ →ₗ[ℂ] E, (∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀, L₁ (r.1 x) = r.2 (L₁ x)) →
      (∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀, L₂ (r.1 x) = r.2 (L₂ x)) →
      ∀ b ∈ B τ₀, Ext (L₁ + L₂) b = Ext L₁ b + Ext L₂ b := by
    intro L₁ L₂ h₁ h₂ b hb
    have h₁₂ : ∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀, (L₁ + L₂) (r.1 x) = r.2 ((L₁ + L₂) x) := by
      intro r hr x hx
      simp only [LinearMap.add_apply, map_add, h₁ r hr x hx, h₂ r hr x hx]
    have := huniq τ₀ (Ext (L₁ + L₂) - Ext L₁ - Ext L₂)
      (sub_mem (sub_mem (hExtC _ h₁₂) (hExtC _ h₁)) (hExtC _ h₂))
      (by
        intro x hx
        simp only [LinearMap.sub_apply, LinearMap.add_apply, hExtA _ h₁₂ x hx, hExtA _ h₁ x hx,
          hExtA _ h₂ x hx]
        abel) b hb
    simp only [LinearMap.sub_apply] at this
    rw [sub_sub, sub_eq_zero] at this
    exact this
  have ExtSmul : ∀ (c : ℂ) (L : H τ₀ →ₗ[ℂ] E), (∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀, L (r.1 x) = r.2 (L x)) →
      ∀ b ∈ B τ₀, Ext (c • L) b = c • Ext L b := by
    intro c L h b hb
    have hc : ∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀, (c • L) (r.1 x) = r.2 ((c • L) x) := by
      intro r hr x hx
      simp only [LinearMap.smul_apply, map_smul, h r hr x hx]
    have := huniq τ₀ (Ext (c • L) - c • Ext L) (sub_mem (hExtC _ hc) (Submodule.smul_mem _ c (hExtC _ h)))
      (by
        intro x hx
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, hExtA _ hc x hx, hExtA _ h x hx, sub_self]) b hb
    simp only [LinearMap.sub_apply, LinearMap.smul_apply] at this
    rw [sub_eq_zero] at this
    exact this
  have hPupd : ∀ (v : ∀ τ, H τ) (i : ι) (z : H i),
      (fun τ => R τ (update v i z τ)) = update (fun τ => R τ (v τ)) i (R i z) := by
    intro v i z
    funext j
    exact apply_update (fun k => (R k : H k → H k)) v i z j
  have hmemU : ∀ (v : ∀ τ, H τ) (i : ι) (z : H i) τ', update (fun τ => R τ (v τ)) i (R i z) τ' ∈ D' τ' := by
    intro v i z τ'
    rw [← hPupd]
    exact hRmem _ _
  let f : (∀ τ, H τ) → E := fun v => Ext (T.toLinearMap (fun τ => R τ (v τ)) τ₀) (R τ₀ (v τ₀))
  have h0position : ∀ (v : ∀ τ, H τ) (x : H τ₀),
      f (update v τ₀ x) = Ext (T.toLinearMap (fun τ => R τ (v τ)) τ₀) (R τ₀ x) := by
    intro v x
    show Ext (T.toLinearMap (fun τ => R τ (update v τ₀ x τ)) τ₀) (R τ₀ (update v τ₀ x τ₀)) = _
    rw [update_self, toLinearMap_congr T (w := fun τ => R τ (update v τ₀ x τ)) (w' := fun τ => R τ (v τ)) τ₀
      (fun j hj => by simp only [update_of_ne hj])]
  have hiposition : ∀ i, i ≠ τ₀ → ∀ (v : ∀ τ, H τ) (z : H i),
      f (update v i z) = Ext (T.toLinearMap (update (fun τ => R τ (v τ)) i (R i z)) τ₀) (R τ₀ (v τ₀)) := by
    intro i hi v z
    show Ext (T.toLinearMap (fun τ => R τ (update v i z τ)) τ₀) (R τ₀ (update v i z τ₀)) = _
    rw [hPupd, update_of_ne (Ne.symm hi)]
  have hRB : ∀ x, R τ₀ x ∈ B τ₀ := fun x => hD'B _ (hRmem τ₀ x)
  have hgU : ∀ (v : ∀ τ, H τ) (i : ι) (z : H i), ∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀,
      T.toLinearMap (update (fun τ => R τ (v τ)) i (R i z)) τ₀ (r.1 x) =
        r.2 (T.toLinearMap (update (fun τ => R τ (v τ)) i (R i z)) τ₀ x) :=
    fun v i z => goodL _ (fun τ' _ => hmemU v i z τ')
  let T' : MultilinearMap ℂ H E := MultilinearMap.mk' f
    (by
      intro v i x y
      by_cases hi : i = τ₀
      · subst hi
        rw [h0position, h0position, h0position, map_add, map_add]
      · rw [hiposition i hi, hiposition i hi, hiposition i hi, map_add, toLinearMap_update_add T hi,
          ExtAdd _ _ (hgU v i x) (hgU v i y) _ (hRB _)])
    (by
      intro v i c x
      by_cases hi : i = τ₀
      · subst hi
        rw [h0position, h0position, map_smul, map_smul]
      · rw [hiposition i hi, hiposition i hi, map_smul, toLinearMap_update_smul T hi,
          ExtSmul _ _ (hgU v i x) _ (hRB _)])
  have hT'apply : ∀ v, T' v = f v := fun v => rfl
  have goodval : ∀ v : ∀ τ, H τ, (∀ τ', τ' ≠ τ₀ → v τ' ∈ D' τ') →
      T' v = Ext (T.toLinearMap v τ₀) (R τ₀ (v τ₀)) := by
    intro v hv
    rw [hT'apply]
    show Ext (T.toLinearMap (fun τ => R τ (v τ)) τ₀) (R τ₀ (v τ₀)) = _
    rw [toLinearMap_congr T (w := fun τ => R τ (v τ)) (w' := v) τ₀ (fun j hj => hRid j _ (hv j hj))]
  have hgen : ∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ D' τ') → ∀ y ∈ D' τ, ∀ τ',
      update u τ y τ' ∈ D' τ' := by
    intro τ u hu y hy τ'
    by_cases h : τ' = τ
    · subst h; rw [update_self]; exact hy
    · rw [update_of_ne h]; exact hu τ' h
  have hshift : ∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ D' τ') → ∀ a ∈ A τ₀, ∀ τ', τ' ≠ τ →
      update u τ₀ a τ' ∈ piecewiseSubmodule A B s τ' := by
    intro τ u hu a ha τ' h
    by_cases h' : τ' = τ₀
    · subst h'; rw [update_self, hD0]; exact ha
    · rw [update_of_ne h', ← hD'ne τ' h']; exact hu τ' h
  have hposition0 : ∀ u : ∀ τ, H τ, (∀ τ', τ' ≠ τ₀ → u τ' ∈ D' τ') →
      T'.toLinearMap u τ₀ ∈ C τ₀ ∧
        ∀ r ∈ Rg τ₀, ∀ x ∈ B τ₀, T' (update u τ₀ (r.1 x)) = r.2 (T' (update u τ₀ x)) := by
    intro u hu
    have hL := goodL u hu
    have key : ∀ x, T' (update u τ₀ x) = Ext (T.toLinearMap u τ₀) (R τ₀ x) := by
      intro x
      rw [goodval _ (fun τ' h => by rw [update_of_ne h]; exact hu τ' h), update_self,
        toLinearMap_congr T (w := update u τ₀ x) (w' := u) τ₀ (fun j hj => update_of_ne hj _ _)]
    constructor
    · refine hC τ₀ _ (hExtC _ hL) _ ?_
      intro x hx
      rw [MultilinearMap.toLinearMap_apply, key, hRid _ _ (hBD' _ hx)]
    · intro r hr x hx
      rw [key, key, hRid _ _ (hBD' _ (hRg τ₀ r hr x hx)), hRid _ _ (hBD' _ hx), hExtG _ hL r hr x hx]
  have hpositionEq : ∀ τ, τ ≠ τ₀ → ∀ u : ∀ τ, H τ, (∀ τ', τ' ≠ τ → u τ' ∈ D' τ') →
      ∀ r, r ∈ Rk τ ∪ Rg τ → ∀ y₁ y₂, y₁ ∈ D' τ → y₂ ∈ D' τ →
      (∀ a ∈ A τ₀, T (update (update u τ₀ a) τ y₁) = r.2 (T (update (update u τ₀ a) τ y₂))) →
      T' (update u τ y₁) = r.2 (T' (update u τ y₂)) := by
    intro τ hτ u hu r hr y₁ y₂ hy₁ hy₂ hA
    have hu0 : u τ₀ ∈ D' τ₀ := hu τ₀ (Ne.symm hτ)
    have hg₁ := goodL _ (fun τ' _ => hgen τ u hu y₁ hy₁ τ')
    have hg₂ := goodL _ (fun τ' _ => hgen τ u hu y₂ hy₂ τ')
    rw [goodval _ (fun τ' _ => hgen τ u hu y₁ hy₁ τ'), goodval _ (fun τ' _ => hgen τ u hu y₂ hy₂ τ')]
    simp only [update_of_ne (Ne.symm hτ)]
    rw [hRid _ _ hu0]
    have := huniq τ₀ (Ext (T.toLinearMap (update u τ y₁) τ₀) - r.2 ∘ₗ Ext (T.toLinearMap (update u τ y₂) τ₀))
      (sub_mem (hExtC _ hg₁) (hpostC τ τ₀ hτ r hr _ (hExtC _ hg₂)))
      (by
        intro a ha
        rw [LinearMap.sub_apply, LinearMap.comp_apply, hExtA _ hg₁ a ha, hExtA _ hg₂ a ha,
          MultilinearMap.toLinearMap_apply, MultilinearMap.toLinearMap_apply, update_comm hτ,
          update_comm hτ, hA a ha, sub_self]) (u τ₀) (hD'B _ hu0)
    rwa [LinearMap.sub_apply, LinearMap.comp_apply, sub_eq_zero] at this
  refine ⟨T', ?_, ?_, ?_⟩
  · intro u hu
    have hL := goodL u (fun τ' _ => hAD' τ' _ (hu τ'))
    rw [goodval u (fun τ' _ => hAD' τ' _ (hu τ')), hRid τ₀ _ (hAD' τ₀ _ (hu τ₀)), hExtA _ hL _ (hu τ₀),
      MultilinearMap.toLinearMap_apply, update_eq_self, hTa u hu]
  · intro τ hτ u hu r hr x hx
    have hne : τ ≠ τ₀ := fun h => hτ (h ▸ Finset.mem_insert_self τ₀ s)
    have hτs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
    exact hpositionEq τ hne u hu r (Set.mem_union_left _ hr) _ _ (hAD' _ _ (hRk τ r hr x hx)) (hAD' _ _ hx)
      (fun a ha => hTb τ hτs (update u τ₀ a) (hshift τ u hu a ha) r hr x hx)
  · intro τ hτ u hu
    by_cases hne : τ = τ₀
    · subst hne
      exact hposition0 u hu
    have hτs : τ ∈ s := by
      rcases Finset.mem_insert.1 hτ with h | h
      · exact absurd h hne
      · exact h
    have hBDτ : ∀ x ∈ B τ, x ∈ D' τ := fun x hx => by
      rw [hD'ne τ hne]; simp only [piecewiseSubmodule, if_pos hτs]; exact hx
    constructor
    · let F : H τ →ₗ[ℂ] H τ₀ →ₗ[ℂ] E := LinearMap.mk₂ ℂ (fun w b => T' (update (update u τ w) τ₀ b))
        (by intro w₁ w₂ b; rw [update_comm hne, update_comm hne, update_comm hne, T'.map_update_add])
        (by intro c w b; rw [update_comm hne, update_comm hne, T'.map_update_smul])
        (by intro w b₁ b₂; rw [T'.map_update_add])
        (by intro c w b; rw [T'.map_update_smul])
      have hF1 : ∀ w ∈ B τ, F w ∈ C τ₀ := by
        intro w hw
        have h := (hposition0 (update u τ w) (fun τ' _ => hgen τ u hu w (hBDτ w hw) τ')).1
        convert h using 1
        ext b
        simp only [F, LinearMap.mk₂_apply, MultilinearMap.toLinearMap_apply]
      have hF2 : ∀ a ∈ A τ₀, F.flip a ∈ C τ := by
        intro a ha
        refine hC τ _ (hTc τ hτs (update u τ₀ a) (hshift τ u hu a ha)).1 _ ?_
        intro x hx
        have hw : ∀ τ', τ' ≠ τ₀ → update (update u τ x) τ₀ a τ' ∈ D' τ' := fun τ' h => by
          rw [update_of_ne h]; exact hgen τ u hu x (hBDτ x hx) τ'
        rw [LinearMap.flip_apply, LinearMap.mk₂_apply, MultilinearMap.toLinearMap_apply, goodval _ hw,
          update_self, hRid _ _ (hAD' _ _ ha), hExtA _ (goodL _ hw) a ha, MultilinearMap.toLinearMap_apply,
          update_idem, update_comm hne]
      have hF3 := hbs τ τ₀ hne F hF1 hF2 (u τ₀) (hD'B _ (hu τ₀ (Ne.symm hne)))
      convert hF3 using 1
      ext x
      rw [LinearMap.flip_apply, LinearMap.mk₂_apply, MultilinearMap.toLinearMap_apply]
      congr 1
      rw [eq_comm, update_eq_self_iff]
      exact (update_of_ne (Ne.symm hne) _ _).symm
    · intro r hr x hx
      exact hpositionEq τ hne u hu r (Set.mem_union_right _ hr) _ _ (hBDτ _ (hRg τ r hr x hx)) (hBDτ _ hx)
        (fun a ha => (hTc τ hτs (update u τ₀ a) (hshift τ u hu a ha)).2 r hr x hx)

end GlobalTheory.FactorwiseExtension

theorem GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (A B : ∀ τ, Submodule ℂ (H τ)), (∀ τ, A τ ≤ B τ) →
    ∀ (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E))),
    (∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ A τ, r.1 x ∈ A τ) → (∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ B τ, r.1 x ∈ B τ) →
    ∀ (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E)),
    (∀ τ, ∀ L ∈ C τ, ∀ L' : H τ →ₗ[ℂ] E, (∀ x ∈ B τ, L' x = L x) → L' ∈ C τ) →
    (∀ τ (L : H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ A τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ B τ, L' (r.1 x) = r.2 (L' x)) ∧ ∀ x ∈ A τ, L' x = L x) →
    (∀ τ, ∀ L ∈ C τ, (∀ x ∈ A τ, L x = 0) → ∀ x ∈ B τ, L x = 0) →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ') →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ r' ∈ Rg τ', r.2 ∘ₗ r'.2 = r'.2 ∘ₗ r.2) →
    (∀ τ τ', τ ≠ τ' → ∀ F : H τ →ₗ[ℂ] H τ' →ₗ[ℂ] E, (∀ w ∈ B τ, F w ∈ C τ') → (∀ a ∈ A τ', F.flip a ∈ C τ) →
      ∀ b ∈ B τ', F.flip b ∈ C τ) →
    ∀ T₀ : MultilinearMap ℂ H E,
    (∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ A τ') → ∀ r ∈ Rk τ, ∀ x ∈ A τ,
      T₀ (Function.update u τ (r.1 x)) = r.2 (T₀ (Function.update u τ x))) →
    ∃ T : MultilinearMap ℂ H E, (∀ u, (∀ τ, u τ ∈ A τ) → T u = T₀ u) ∧
      ∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ B τ') →
        T.toLinearMap u τ ∈ C τ ∧
          ∀ r ∈ Rg τ, ∀ x ∈ B τ, T (Function.update u τ (r.1 x)) = r.2 (T (Function.update u τ x)) := by
  intro ι _ _ H _ _ E _ _ A B hAB Rk Rg hRk hRg C hC hext huniq hpostC _hcomm hbs T₀ h0
  obtain ⟨T, hTa, -, hTc⟩ : ∃ T, GlobalTheory.FactorwiseExtension.Invariant A B Rk Rg C T₀ Finset.univ T := by
    refine Finset.induction_on (motive := fun s => ∃ T, GlobalTheory.FactorwiseExtension.Invariant A B Rk Rg C T₀ s T)
      Finset.univ ?_ ?_
    · refine ⟨T₀, fun u _ => rfl, ?_, ?_⟩
      · intro τ _ u hu r hr x hx
        exact h0 τ u (fun τ' h => by simpa [GlobalTheory.FactorwiseExtension.piecewiseSubmodule] using hu τ' h) r hr x hx
      · intro τ h
        simp at h
    · rintro τ₀ s hτ₀ ⟨T, hT⟩
      exact GlobalTheory.FactorwiseExtension.invariant_insert A B hAB Rk Rg hRk hRg C hC hext huniq hpostC hbs
        T₀ s τ₀ hτ₀ T hT
  refine ⟨T, hTa, fun τ u hu => hTc τ (Finset.mem_univ τ) u (fun τ' h => ?_)⟩
  simpa [GlobalTheory.FactorwiseExtension.piecewiseSubmodule] using hu τ' h
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinear_positionwise_extension_of_equivariant : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (A B : ∀ τ, Submodule ℂ (H τ)), (∀ τ, A τ ≤ B τ) →
    ∀ (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E))),
    (∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ A τ, r.1 x ∈ A τ) → (∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ B τ, r.1 x ∈ B τ) →
    ∀ (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E)),
    (∀ τ, ∀ L ∈ C τ, ∀ L' : H τ →ₗ[ℂ] E, (∀ x ∈ B τ, L' x = L x) → L' ∈ C τ) →
    (∀ τ (L : H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ A τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ B τ, L' (r.1 x) = r.2 (L' x)) ∧ ∀ x ∈ A τ, L' x = L x) →
    (∀ τ, ∀ L ∈ C τ, (∀ x ∈ A τ, L x = 0) → ∀ x ∈ B τ, L x = 0) →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ') →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ r' ∈ Rg τ', r.2 ∘ₗ r'.2 = r'.2 ∘ₗ r.2) →
    (∀ τ τ', τ ≠ τ' → ∀ F : H τ →ₗ[ℂ] H τ' →ₗ[ℂ] E, (∀ w ∈ B τ, F w ∈ C τ') → (∀ a ∈ A τ', F.flip a ∈ C τ) →
      ∀ b ∈ B τ', F.flip b ∈ C τ) →
    ∀ T₀ : MultilinearMap ℂ H E,
    (∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ A τ') → ∀ r ∈ Rk τ, ∀ x ∈ A τ,
      T₀ (Function.update u τ (r.1 x)) = r.2 (T₀ (Function.update u τ x))) →
    ∃ T : MultilinearMap ℂ H E, (∀ u, (∀ τ, u τ ∈ A τ) → T u = T₀ u) ∧
      ∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ B τ') →
        T.toLinearMap u τ ∈ C τ ∧
          ∀ r ∈ Rg τ, ∀ x ∈ B τ, T (Function.update u τ (r.1 x)) = r.2 (T (Function.update u τ x)) := by
  atlas_forward_decl GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension
end

section
section
open Filter Topology
open scoped Uniformity

namespace GlobalTheory

theorem bilinear_bound_of_dense_right : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p →
    ∀ {X₁ X₂ : Type} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    (j₁ : X₁ →ₗ[ℂ] E) (j₂ : X₂ →ₗ[ℂ] E), Function.Injective j₁ → IsClosed (Set.range j₁) →
    ∀ (D₂ : Submodule ℂ X₂), (∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set X₂))) →
    ∀ (F : X₁ →ₗ[ℂ] X₂ →ₗ[ℂ] E),
    (∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F w b) ≤ q (j₂ b)) →
    (∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w a) ≤ q (j₁ w)) →
    ∀ b i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w b) ≤ q (j₁ w) := by
  intro E _ _ _ _ _ _ p hp X₁ X₂ _ _ _ _ j₁ j₂ hinj hcl D₂ hdense F h₁ h₂ b i
  haveI : ContinuousSMul ℂ E := hp.continuousSMul
  haveI : FirstCountableTopology E := hp.firstCountableTopology
  haveI : PolynormableSpace ℂ E := hp.toPolynormableSpace
  haveI : IsTopologicalAddGroup E := inferInstance
  set Y : Submodule ℂ E := LinearMap.range j₁ with hYdef
  have hYc : IsClosed (Y : Set E) := by simpa [Y, LinearMap.coe_range] using hcl
  haveI : IsUniformAddGroup Y := Y.toAddSubgroup.isUniformAddGroup
  haveI : CompleteSpace Y := hYc.completeSpace_coe
  haveI : FirstCountableTopology Y := Topology.IsInducing.subtypeVal.firstCountableTopology
  haveI : (𝓤 Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : BarrelledSpace ℂ Y := inferInstance
  let e : X₁ ≃ₗ[ℂ] Y := LinearEquiv.ofInjective j₁ hinj
  have he : ∀ w, ((e w : Y) : E) = j₁ w := fun w => rfl

  let gl : D₂ → Y →ₗ[ℂ] E := fun a => (F.flip (a : X₂)).comp e.symm.toLinearMap
  have hgl : ∀ a y, gl a y = F (e.symm y) a := fun a y => rfl
  have hgc : ∀ a, Continuous (gl a) := by
    intro a
    refine hp.continuous_of_continuous_comp (gl a) fun k => ?_
    obtain ⟨q, hq, hle⟩ := h₂ a a.2 k
    refine Seminorm.continuous_of_le (q := q.comp Y.subtype) (hq.comp continuous_subtype_val) ?_
    intro y
    have := hle (e.symm y)
    rw [← he, e.apply_symm_apply] at this
    simpa [Seminorm.comp_apply, hgl] using this
  let g : D₂ → Y →L[ℂ] E := fun a => ⟨gl a, hgc a⟩
  let l : Filter D₂ := Filter.comap (fun a : D₂ => j₂ a) (𝓝 (j₂ b))
  haveI : l.NeBot := by
    rw [Filter.comap_neBot_iff]
    intro t ht
    obtain ⟨_, htx, ⟨a, ha, rfl⟩⟩ := mem_closure_iff_nhds.mp (hdense b) t ht
    exact ⟨⟨a, ha⟩, htx⟩
  have hT : Tendsto (fun a y => g a y) l (𝓝 fun y => F (e.symm y) b) := by
    rw [tendsto_pi_nhds]
    intro y
    rw [hp.tendsto_nhds]
    intro k ε hε
    obtain ⟨q, hq, hle⟩ := h₁ (e.symm y) k
    have ht : Tendsto (fun a : D₂ => q (j₂ a - j₂ b)) l (𝓝 0) := by
      have h0 : Tendsto (fun a : D₂ => j₂ a - j₂ b) l (𝓝 (j₂ b - j₂ b)) :=
        tendsto_comap.sub tendsto_const_nhds
      have := (hq.tendsto _).comp h0
      simpa [Function.comp_def] using this
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with a ha
    calc p k (g a y - F (e.symm y) b) = p k (F (e.symm y) ((a : X₂) - b)) := by
          simp [g, hgl, map_sub]
      _ ≤ q (j₂ ((a : X₂) - b)) := hle _
      _ < ε := by simpa [map_sub] using ha
  let G : Y →L[ℂ] E := continuousLinearMapOfTendsto g hT
  have hG : ∀ y, G y = F (e.symm y) b := fun y => rfl
  have hr : Continuous ((p i).comp G.toLinearMap) := (hp.continuous_seminorm i).comp G.continuous
  obtain ⟨q, hq, hle⟩ := Seminorm.exists_le_comp_of_isInducing hr (f := Y.subtype) .subtypeVal
  refine ⟨q, hq, fun w => ?_⟩
  have := hle (e w)
  simpa [Seminorm.comp_apply, hG, he] using this

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_seminorm_bound_of_dense_second_slot : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p →
    ∀ {X₁ X₂ : Type} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    (j₁ : X₁ →ₗ[ℂ] E) (j₂ : X₂ →ₗ[ℂ] E), Function.Injective j₁ → IsClosed (Set.range j₁) →
    ∀ (D₂ : Submodule ℂ X₂), (∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set X₂))) →
    ∀ (F : X₁ →ₗ[ℂ] X₂ →ₗ[ℂ] E),
    (∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F w b) ≤ q (j₂ b)) →
    (∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w a) ≤ q (j₁ w)) →
    ∀ b i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w b) ≤ q (j₁ w) := by
  atlas_forward_decl GlobalTheory.bilinear_bound_of_dense_right
end

section
namespace GlobalTheory

open Complex

theorem mem_closure_of_forall_dual_vanish :
    ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by
  intro E _ _ _ _ p hp Z x h
  haveI := hp.continuousSMul
  haveI : LocallyConvexSpace ℝ E := hp.toLocallyConvexSpace
  by_contra hx
  rw [← Z.topologicalClosure_coe] at hx
  obtain ⟨f, u, hfx, hf⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ)
    ((Z.topologicalClosure.restrictScalars ℝ).convex) Z.isClosed_topologicalClosure hx
  simp only [RCLike.re_to_complex] at hfx hf
  have hre : ∀ w ∈ Z, (f w).re = 0 := by
    intro w hw
    by_contra hne
    set t : ℝ := (u - 1) / (f w).re
    have hmem : ((t : ℂ) • w) ∈ Z.topologicalClosure :=
      Z.le_topologicalClosure (Z.smul_mem _ hw)
    have h1 := hf _ hmem
    rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul] at h1
    have : t * (f w).re = u - 1 := by
      simp only [t]; field_simp
    linarith
  have hvan : ∀ z ∈ Z, f z = 0 := by
    intro z hz
    have h1 := hre z hz
    have h2 := hre (Complex.I • z) (Z.smul_mem _ hz)
    rw [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im] at h2
    apply Complex.ext
    · simpa using h1
    · simp at h2; simpa using h2
  have h0 := hf 0 (Z.topologicalClosure.zero_mem)
  have hfx0 := h f hvan
  rw [map_zero] at h0
  rw [hfx0] at hfx
  simp at h0 hfx
  linarith

end GlobalTheory

alias _root_.GlobalTheory.T.mem_closure_of_forall_clm_vanish := _root_.GlobalTheory.mem_closure_of_forall_dual_vanish
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ),
    w ∈ M.sm τ ↔ SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w := by
  first | exact @GlobalTheory.SmVecModel.mem_sm_iff | exact GlobalTheory.SmVecModel.mem_sm_iff | (intros; apply GlobalTheory.SmVecModel.mem_sm_iff <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SobFrame

section Conj

variable {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}

theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) (P⁻¹ * X * P) w = dRep σ X w := by
  unfold dRep
  simp only [exp_smul_conj_inv hP, conj_cancel hP]

theorem foldr_dRep_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : H) :
    (l.map fun X => P⁻¹ * X * P).foldr (dRep fun g => σ (P * g * P⁻¹)) w = l.foldr (dRep σ) w := by
  induction l with
  | nil => rfl
  | cons X l ih => simp only [List.map_cons, List.foldr_cons, ih, dRep_conj_inv hP]

theorem smoothVec_conj_inv (hP : IsUnit P) {A B : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hAB : ∀ X ∈ A, P⁻¹ * X * P ∈ B) {w : H} (hw : SmoothVec B (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec A σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => hAB _ (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

end Conj

theorem conj_mem_lieAt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) :
    (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
  have hX' : Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X = 0 := hX
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
  rw [← M.fr_gram τ]
  have e : ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) +
      (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * X * M.fr τ) =
      (M.fr τ)ᴴ * ((Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X) * M.fr τ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hc, Matrix.mul_nonsing_inv_cancel_left _ _ hd,
      Matrix.add_mul, Matrix.mul_add]
  rw [e, hX', Matrix.zero_mul, Matrix.mul_zero]

theorem sobCont_rep_of_bound : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ)
    (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) →
    (∀ w, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w → ‖ℓ w‖ ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) →
    Sobolev₂ (lieAt V τ) (M.rep τ) ℓ := by
  intro D V S M τ ℓ L C hL hC
  have hP := M.fr_unit τ
  refine ⟨L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ), C, ?_, fun w hw => ?_⟩
  · intro l hl X hX
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
    obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
    exact conj_mem_lieAt M τ (hL l₀ hl₀ X₀ hX₀)
  · have hw' : SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w :=
      smoothVec_conj_inv (σ := M.σ τ) hP (fun _ hX => conj_mem_lieAt M τ hX) hw
    have hs : ((L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ)).map
        fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum = GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w := by
      unfold GlobalTheory.SmoothGlob.sobNorm
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun l _ => ?_
      exact congrArg norm (foldr_dRep_conj_inv (σ := M.σ τ) hP l w)
    rw [hs]
    exact hC w hw'

end GlobalTheory.SobFrame

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolevContinuous_modelRep_of_sobolevBound : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ)
    (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) →
    (∀ w, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w → ‖ℓ w‖ ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) →
    Sobolev₂ (lieAt V τ) (M.rep τ) ℓ := by
  atlas_forward_decl GlobalTheory.SobFrame.sobCont_rep_of_bound
end

section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FactorExtension

open GlobalTheory.SmoothGlob

variable {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]

theorem smul_seminorm_cont {q : Seminorm ℂ E} (hq : Continuous q) (c : NNReal) : Continuous (c • q) := by
  rw [Seminorm.coe_smul]
  exact hq.const_smul c

theorem bound_via {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {p : ℕ → Seminorm ℂ E} {N L : H →ₗ[ℂ] E}
    (hN : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) →
      ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → sobNorm σ S w ≤ q (N w))
    (hL : L ∈ sobBd ε σ p) (i : ℕ) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → p i (L w) ≤ q (N w) := by
  obtain ⟨S, C, hS, hb⟩ := hL i
  obtain ⟨q, hq, hqb⟩ := hN S hS
  refine ⟨Real.toNNReal |C| • q, smul_seminorm_cont hq _, fun w hw => ?_⟩
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (abs_nonneg C)]
  calc p i (L w) ≤ C * sobNorm σ S w := hb w hw
    _ ≤ |C| * sobNorm σ S w := mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg σ S w)
    _ ≤ |C| * q (N w) := mul_le_mul_of_nonneg_left (hqb w hw) (abs_nonneg C)

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem form_zero (hHC : GlobalTheory.Published.HarishChandraModules) (M : DSModel V S) (τ : D.what₂.Tau) {p : ℕ → Seminorm ℂ E}
    (hp : WithSeminorms p) {L : M.H τ →ₗ[ℂ] E} (hL : L ∈ sobBd (M.ε τ) (M.σ τ) p) (f : E →L[ℂ] ℂ)
    (h0 : ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, f (L a) = 0) : ∀ w ∈ M.sm τ, f (L w) = 0 := by
  have hq : Continuous ((normSeminorm ℂ ℂ).comp (f : E →ₗ[ℂ] ℂ)) := continuous_norm.comp f.continuous
  obtain ⟨Sl, C, hS, hb⟩ := sobBd_seminorm hp hL _ hq
  have hsc := GlobalTheory.T.sobolevContinuous_modelRep_of_sobolevBound M τ ((f : E →ₗ[ℂ] ℂ) ∘ₗ L) Sl C hS (fun w hw => by simpa using hb w hw)
  exact GlobalTheory.T.sobolevForm_eq_zero_on_smooth_of_kFinite_discreteSeries hHC D V S M τ _ hsc h0

theorem uniq (hHC : GlobalTheory.Published.HarishChandraModules) (M : DSModel V S) (τ : D.what₂.Tau) {p : ℕ → Seminorm ℂ E}
    (hp : WithSeminorms p) {L : M.H τ →ₗ[ℂ] E} (hL : L ∈ sobBd (M.ε τ) (M.σ τ) p)
    (h0 : ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L a = 0) : ∀ w ∈ M.sm τ, L w = 0 := by
  intro w hw
  have h := GlobalTheory.T.mem_closure_of_forall_clm_vanish hp ⊥ (L w) fun f _ => form_zero hHC M τ hp hL f (fun a ha => by rw [h0 a ha, map_zero]) w hw
  rw [Submodule.bot_coe, closure_singleton] at h
  exact h

end GlobalTheory.FactorExtension

namespace GlobalTheory.FactorExtension

open GlobalTheory.SmoothGlob

theorem extend_positions : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (π dπ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ τ, GlobalTheory.SmoothGlob.IsSmoothModRep (M.ε τ) p (π τ) (dπ τ)) → (∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'), (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g)) → ∀ T₀ : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E, (∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = M.σ τ k (u τ) → T₀ (Function.update u τ w) = π τ k (T₀ u)) → (∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) → T₀ (Function.update u τ w) = dπ τ X (T₀ u)) → ∃ T : MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) E, (∀ (v : M.Vec) (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M), (∀ τ, (v τ : M.H τ) = u τ) → T v = T₀ u) ∧ (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) ∧ ∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w := by
  intro hHC hCW D V S M E _ _ _ _ _ _ p π dπ hπ hcomm T₀ hK hL
  haveI hc : ∀ τ, CompleteSpace (M.H τ) := fun τ => (M.ds τ).1
  have hsm : ∀ τ w, w ∈ M.sm τ ↔ SmoothVec (lieSet (M.ε τ)) (M.σ τ) w := fun τ w => GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff M τ w
  have hstd : ∀ τ, GlobalTheory.TypeSum.Std (M.ε τ) (M.σ τ) := fun τ => GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  have hAB : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := fun τ v hv => (hsm τ v).2 ((hstd τ).2.2.1 v hv)
  have hPex : ∀ τ, ∃ P : M.H τ →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, P x = x := by
    intro τ
    obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).subtype
      (Submodule.ker_subtype _)
    exact ⟨P, fun x => LinearMap.congr_fun hP x⟩
  choose P hP using hPex
  have hP' : ∀ τ (x : M.H τ) (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), P τ x = ⟨x, hx⟩ := fun τ x hx => hP τ ⟨x, hx⟩
  let T₀' : MultilinearMap ℂ (fun τ => M.H τ) E := T₀.compLinearMap P
  let Rk : ∀ τ, Set ((M.H τ → M.H τ) × (E →ₗ[ℂ] E)) := fun τ =>
    {r | (∃ k ∈ Formalism.REAL.Kset (M.ε τ), r = (⇑(M.σ τ k), (π τ k : E →ₗ[ℂ] E))) ∨
      ∃ X ∈ lieSet (M.ε τ), r = (dRep (M.σ τ) X, (dπ τ X : E →ₗ[ℂ] E))}
  let Rg : ∀ τ, Set ((M.H τ → M.H τ) × (E →ₗ[ℂ] E)) := fun τ =>
    {r | ∃ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), r = (⇑(M.σ τ g), (π τ g : E →ₗ[ℂ] E))}
  have hRk : ∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, r.1 x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := by
    rintro τ r (⟨k, hk, rfl⟩ | ⟨X, hX, rfl⟩) x hx
    · obtain ⟨A, hA, ha, hs⟩ := hx
      exact ⟨A, hA, hs k hk x ha, hs⟩
    · exact GlobalTheory.TypeSum.isKFin_dRep _ _ _ (M.σ τ) (hstd τ) x hx X hX
  have hRg : ∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ M.sm τ, r.1 x ∈ M.sm τ := by
    rintro τ r ⟨g, hg, rfl⟩ x hx
    rw [GlobalTheory.SmVec.sm_eq] at hx ⊢
    exact GlobalTheory.SmVec.sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 hx hg
  let C : ∀ τ, Submodule ℂ (M.H τ →ₗ[ℂ] E) := fun τ => sobBd (M.ε τ) (M.σ τ) p
  have hC : ∀ τ, ∀ L ∈ C τ, ∀ L' : M.H τ →ₗ[ℂ] E, (∀ x ∈ M.sm τ, L' x = L x) → L' ∈ C τ :=
    fun τ L hL L' h => sobBd_congr hL fun w hw => h w ((hsm τ w).2 hw)

  have hcw : ∀ τ (L : M.H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L (r.1 x) = r.2 (L x)) →
      ∃ T : M.H τ →ₗ[ℂ] E, (∀ v, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) v → T v = L v) ∧
        IsSmoothGMap (M.ε τ) (M.σ τ) p (π τ) T ∧ IsClosed (T '' {w | SmoothVec (lieSet (M.ε τ)) (M.σ τ) w}) ∧
        ((∃ v, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) v ∧ L v ≠ 0) →
          ∀ Sl : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ l ∈ Sl, ∀ X ∈ l, X ∈ lieSet (M.ε τ)) →
            ∃ q : Seminorm ℂ E, Continuous q ∧
              ∀ w, SmoothVec (lieSet (M.ε τ)) (M.σ τ) w → sobNorm (M.σ τ) Sl w ≤ q (T w)) := by
    intro τ L hLk
    have hGK : IsGKMap (M.ε τ) (M.σ τ) (π τ) (dπ τ) L :=
      ⟨fun k hk v hv => hLk _ (Or.inl ⟨k, hk, rfl⟩) v hv, fun X hX v hv => hLk _ (Or.inr ⟨X, hX, rfl⟩) v hv⟩
    obtain ⟨T, hT1, hT2, -, hT4, hT5⟩ := hCW V.rank (M.ε τ) (M.H τ) (M.σ τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 E p
      (π τ) (dπ τ) (hπ τ) L hGK
    exact ⟨T, hT1, hT2, hT4, hT5⟩
  have hext : ∀ τ (L : M.H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ M.sm τ, L' (r.1 x) = r.2 (L' x)) ∧
        ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L' x = L x := by
    intro τ L hLk
    obtain ⟨T, hT1, ⟨hT2, hT3⟩, -⟩ := hcw τ L hLk
    refine ⟨T, hT3, ?_, fun x hx => hT1 x hx⟩
    rintro r ⟨g, hg, rfl⟩ x hx
    exact hT2 g hg x ((hsm τ x).1 hx)
  have huniq : ∀ τ, ∀ L ∈ C τ, (∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L x = 0) → ∀ x ∈ M.sm τ, L x = 0 :=
    fun τ L hL h0 => uniq hHC M τ (hπ τ).withSeminorms hL h0
  have hpostC : ∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ' := by
    rintro τ τ' - r ((⟨k, -, rfl⟩ | ⟨X, -, rfl⟩) | ⟨g, -, rfl⟩) L hL
    · exact sobBd_comp (hπ τ').withSeminorms hL (π τ k)
    · exact sobBd_comp (hπ τ').withSeminorms hL (dπ τ X)
    · exact sobBd_comp (hπ τ').withSeminorms hL (π τ g)
  have hcomm' : ∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ r' ∈ Rg τ', r.2 ∘ₗ r'.2 = r'.2 ∘ₗ r.2 := by
    rintro τ τ' hne r ((⟨k, hk, rfl⟩ | ⟨X, hX, rfl⟩) | ⟨g, hg, rfl⟩) r' ⟨g', hg', rfl⟩
    · have h := hcomm τ τ' hne k (GlobalTheory.TypeSum.K_le_UJ hk) g' hg'
      ext x
      exact congrArg (fun f : E →L[ℂ] E => f x) h
    · have h := dRep_comm (hπ τ) hX (π τ' g') fun t =>
        hcomm τ' τ hne.symm g' hg' _ (GlobalTheory.TypeSum.exp_mem_UJ hX t)
      ext x
      exact (congrArg (fun f : E →L[ℂ] E => f x) h).symm
    · have h := hcomm τ τ' hne g hg g' hg'
      ext x
      exact congrArg (fun f : E →L[ℂ] E => f x) h
  have h0 : ∀ τ (u : ∀ τ, M.H τ), (∀ τ', τ' ≠ τ → u τ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ') → ∀ r ∈ Rk τ,
      ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ,
      T₀' (Function.update u τ (r.1 x)) = r.2 (T₀' (Function.update u τ x)) := by
    intro τ u _ r hr x hx
    have e : ∀ y : M.H τ, T₀' (Function.update u τ y) = T₀ (Function.update (fun τ' => P τ' (u τ')) τ (P τ y)) :=
      fun y => by
        show T₀ (fun τ' => P τ' (Function.update u τ y τ')) = _
        congr 1
        funext τ'
        exact Function.apply_update (fun τ => P τ) u τ y τ'
    have hr' := hRk τ r hr x hx
    rw [e, e]
    rcases hr with ⟨k, hk, rfl⟩ | ⟨X, hX, rfl⟩
    · have h := hK τ k hk (Function.update (fun τ' => P τ' (u τ')) τ (P τ x)) (P τ (M.σ τ k x))
        (by rw [Function.update_self, hP' τ _ hx, hP' τ _ hr'])
      rw [Function.update_idem] at h
      exact h
    · have h := hL τ X hX (Function.update (fun τ' => P τ' (u τ')) τ (P τ x)) (P τ (dRep (M.σ τ) X x))
        (by rw [Function.update_self, hP' τ _ hx, hP' τ _ hr'])
      rw [Function.update_idem] at h
      exact h
  by_cases hz : ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, T₀ u = 0
  · refine ⟨0, fun v u _ => (hz u).symm, fun τ g _ v w _ => by simp, fun τ i v => ⟨[], 0, by simp, fun w => by simp⟩⟩
  push_neg at hz
  obtain ⟨u₀, hu₀⟩ := hz

  have hNZ : ∀ τ, ∃ N : M.H τ →ₗ[ℂ] E, N ∈ C τ ∧ IsClosed (N '' {w | SmoothVec (lieSet (M.ε τ)) (M.σ τ) w}) ∧
      ∀ Sl : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ l ∈ Sl, ∀ X ∈ l, X ∈ lieSet (M.ε τ)) →
        ∃ q : Seminorm ℂ E, Continuous q ∧
          ∀ w, SmoothVec (lieSet (M.ε τ)) (M.σ τ) w → sobNorm (M.σ τ) Sl w ≤ q (N w) := by
    intro τ
    let u : ∀ τ, M.H τ := fun τ => (u₀ τ : M.H τ)
    have hLk : ∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, T₀'.toLinearMap u τ (r.1 x) = r.2 (T₀'.toLinearMap u τ x) :=
      fun r hr x hx => by
        simp only [MultilinearMap.toLinearMap_apply]
        exact h0 τ u (fun τ' _ => (u₀ τ').2) r hr x hx
    obtain ⟨T, hT1, ⟨-, hT3⟩, hT4, hT5⟩ := hcw τ _ hLk
    refine ⟨T, hT3, hT4, hT5 ⟨u τ, (u₀ τ).2, ?_⟩⟩
    rw [MultilinearMap.toLinearMap_apply, Function.update_eq_self]
    show T₀ (fun τ' => P τ' (u₀ τ' : M.H τ')) ≠ 0
    have : (fun τ' => P τ' (u₀ τ' : M.H τ')) = u₀ := funext fun τ' => hP τ' (u₀ τ')
    rw [this]
    exact hu₀
  have hbs : ∀ τ τ', τ ≠ τ' → ∀ F : M.H τ →ₗ[ℂ] M.H τ' →ₗ[ℂ] E, (∀ w ∈ M.sm τ, F w ∈ C τ') →
      (∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ', F.flip a ∈ C τ) → ∀ b ∈ M.sm τ', F.flip b ∈ C τ := by
    intro τ τ' _ F hF1 hF2 b hb
    obtain ⟨N₁, hN₁C, hN₁cl, hN₁iso⟩ := hNZ τ
    obtain ⟨N₂, hN₂C, -, hN₂iso⟩ := hNZ τ'
    have hp := (hπ τ).withSeminorms
    let j₁ : M.sm τ →ₗ[ℂ] E := N₁ ∘ₗ (M.sm τ).subtype
    let j₂ : M.sm τ' →ₗ[ℂ] E := N₂ ∘ₗ (M.sm τ').subtype
    have hinj : Function.Injective j₁ := by
      refine (injective_iff_map_eq_zero j₁).2 fun x hx => ?_
      obtain ⟨q, -, hq⟩ := hN₁iso [[]] (by simp)
      have h1 := hq x ((hsm τ x).1 x.2)
      have h2 : j₁ x = N₁ x := rfl
      rw [← h2, hx, map_zero] at h1
      have h3 : sobNorm (M.σ τ) [[]] (x : M.H τ) = ‖(x : M.H τ)‖ := by simp [sobNorm]
      rw [h3] at h1
      exact Subtype.ext (norm_le_zero_iff.1 h1)
    have hcl : IsClosed (Set.range j₁) := by
      have e : Set.range j₁ = N₁ '' {w | SmoothVec (lieSet (M.ε τ)) (M.σ τ) w} := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x, (hsm τ x).1 x.2, rfl⟩
        · rintro ⟨w, hw, rfl⟩
          exact ⟨⟨w, (hsm τ w).2 hw⟩, rfl⟩
      rw [e]
      exact hN₁cl
    let D₂ : Submodule ℂ (M.sm τ') := (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ').comap (M.sm τ').subtype
    have hD : ∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set (M.sm τ'))) := by
      intro x
      have h := GlobalTheory.T.mem_closure_of_forall_clm_vanish (hπ τ').withSeminorms (D₂.map j₂) (j₂ x) fun f hf =>
        form_zero hHC M τ' (hπ τ').withSeminorms hN₂C f (fun a ha => hf _ ⟨⟨a, hAB τ' ha⟩, ha, rfl⟩) x x.2
      rwa [Submodule.map_coe] at h
    let F' : M.sm τ →ₗ[ℂ] M.sm τ' →ₗ[ℂ] E := F.compl₁₂ (M.sm τ).subtype (M.sm τ').subtype
    have h₂ : ∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F' w b) ≤ q (j₂ b) := by
      intro w i
      obtain ⟨q, hq, hb⟩ := bound_via hN₂iso (hF1 w w.2) i
      exact ⟨q, hq, fun b => hb b ((hsm τ' b).1 b.2)⟩
    have h₁ : ∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F' w a) ≤ q (j₁ w) := by
      intro a ha i
      obtain ⟨q, hq, hb⟩ := bound_via hN₁iso (hF2 a ha) i
      exact ⟨q, hq, fun w => hb w ((hsm τ w).1 w.2)⟩
    intro i
    obtain ⟨q, hq, hb'⟩ := GlobalTheory.T.exists_seminorm_bound_of_dense_second_slot hp j₁ j₂ hinj hcl D₂ hD F' h₂ h₁ ⟨b, hb⟩ i
    obtain ⟨Sl, C', hS, hb''⟩ := sobBd_seminorm hp hN₁C q hq
    exact ⟨Sl, C', hS, fun w hw => (hb' ⟨w, (hsm τ w).2 hw⟩).trans (hb'' w hw)⟩
  obtain ⟨Tab, hT1, hT2⟩ := GlobalTheory.T.exists_multilinear_positionwise_extension_of_equivariant (H := fun τ => M.H τ) (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ)
    (fun τ => M.sm τ) hAB Rk Rg hRk hRg C hC hext huniq hpostC hcomm' hbs T₀' h0
  have hupd : ∀ (v : M.Vec) τ (w : M.sm τ),
      (fun τ' => ((Function.update v τ w τ' : M.sm τ') : M.H τ')) =
        Function.update (fun τ' => (v τ' : M.H τ')) τ (w : M.H τ) :=
    fun v τ w => funext fun τ' => Function.apply_update (fun τ => ((M.sm τ).subtype : M.sm τ → M.H τ)) v τ w τ'
  refine ⟨Tab.compLinearMap fun τ => (M.sm τ).subtype, ?_, ?_, ?_⟩
  · intro v u hvu
    show Tab (fun τ => (v τ : M.H τ)) = T₀ u
    have e : (fun τ => (v τ : M.H τ)) = fun τ => (u τ : M.H τ) := funext hvu
    rw [e, hT1 _ fun τ => (u τ).2]
    show T₀ (fun τ => P τ (u τ : M.H τ)) = T₀ u
    congr 1
    funext τ
    exact hP τ (u τ)
  · intro τ g hg v w hw
    show Tab (fun τ' => ((Function.update v τ w τ' : M.sm τ') : M.H τ')) = π τ g (Tab fun τ' => (v τ' : M.H τ'))
    rw [hupd, hw]
    have h := (hT2 τ (fun τ' => (v τ' : M.H τ')) fun τ' _ => (v τ').2).2 _ ⟨g, hg, rfl⟩ (v τ) (v τ).2
    rw [Function.update_eq_self] at h
    exact h
  · intro τ i v
    obtain ⟨Sl, C', hS, hb⟩ := (hT2 τ (fun τ' => (v τ' : M.H τ')) fun τ' _ => (v τ').2).1 i
    refine ⟨Sl, C', hS, fun w => ?_⟩
    have h := hb w ((hsm τ w).1 w.2)
    rw [MultilinearMap.toLinearMap_apply] at h
    show p i (Tab (fun τ' => ((Function.update v τ w τ' : M.sm τ') : M.H τ'))) ≤ _
    rw [hupd]
    exact h

end GlobalTheory.FactorExtension
end

section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multilinear_gKMap_extends_to_smooth_vectors : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (π dπ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ τ, GlobalTheory.SmoothGlob.IsSmoothModRep (M.ε τ) p (π τ) (dπ τ)) → (∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'), (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g)) → ∀ T₀ : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E, (∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = M.σ τ k (u τ) → T₀ (Function.update u τ w) = π τ k (T₀ u)) → (∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) → T₀ (Function.update u τ w) = dπ τ X (T₀ u)) → ∃ T : MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) E, (∀ (v : M.Vec) (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M), (∀ τ, (v τ : M.H τ) = u τ) → T v = T₀ u) ∧ (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) ∧ ∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w := by
  first | exact @GlobalTheory.FactorExtension.extend_positions | exact GlobalTheory.FactorExtension.extend_positions | (intros; apply GlobalTheory.FactorExtension.extend_positions <;> assumption)
end

section
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GKExtFields

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem dRep_rep_conj (M : DSModel V S) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : M.H τ) :
    dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) w = dRep (M.σ τ) X w := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  unfold Formalism.L2.Theta.dRep DSModel.rep
  congr 1
  funext t
  have h1 : t • ((M.fr τ)⁻¹ * X * M.fr τ) = (M.fr τ)⁻¹ * (t • X) * M.fr τ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h1, Matrix.exp_conj' _ _ (M.fr_unit τ)]
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

theorem foldr_dRep_conj (M : DSModel V S) (τ : D.what₂.Tau) (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (w : M.H τ) :
    (l.map fun X => (M.fr τ)⁻¹ * X * M.fr τ).foldr (dRep (M.rep τ)) w = l.foldr (dRep (M.σ τ)) w := by
  induction l with
  | nil => rfl
  | cons X l ih => simp only [List.map_cons, List.foldr_cons, ih, dRep_rep_conj]

theorem conj_mem_lieAt (M : DSModel V S) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) : (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hX' : Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X = 0 := hX
  show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
  rw [← M.fr_gram τ]
  have h1 : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, conjTranspose_one, Matrix.one_mul]
  have h2 : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have h3 : (M.fr τ)ᴴ * (Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X) * M.fr τ = 0 := by
    rw [hX']; simp
  simp only [conjTranspose_mul, Matrix.mul_assoc, h1, h2]
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using h3

theorem multMap_fields : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (ι : E →ₗ[ℂ] (GA D V → ℂ)) (N : ℕ) (π : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ d x, p d x = (GlobalTheory.Size.growthSob θ V d N (ι x)).toReal) → (∀ x d, GlobalTheory.Size.growthSob θ V d N (ι x) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ x, ι (π τ g x) = rTr V ((GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ g) (ι x)) → ∀ T : MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) E, (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) → (∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → ι (T (Function.update v τ w)) = rTr V (atTau θ V τ g) (ι (T v))) ∧ ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := by
  intro D θ V S M E _ _ _ _ _ _ p ι N π hp hfin hπ T hTe hTc
  refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg' : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
      GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hg
    rw [hTe τ _ hg' v w hw, hπ τ _ hg']
    have he : (GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ (M.fr τ * g * (M.fr τ)⁻¹) = atTau θ V τ g := by
      show atTau θ V τ ((M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ) = atTau θ V τ g
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    rw [he]
  · let f : M.sm τ →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (ι.comp (T.toLinearMap v τ))
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend f
    have hℓw : ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := fun w => by
      have := LinearMap.congr_fun hℓ w
      simpa [f, MultilinearMap.toLinearMap_apply] using this
    refine ⟨ℓ, ?_, hℓw⟩
    obtain ⟨L, C, hL, hC⟩ := hTc τ 0 v
    refine ⟨L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ), GlobalTheory.Grow.height V x ^ N * C, ?_, fun w hw => ?_⟩
    · intro l hl X hX
      obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
      obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
      exact GlobalTheory.GKExtFields.conj_mem_lieAt M τ (hL l₀ hl₀ X₀ hX₀)
    · have hmem : w ∈ M.sm τ := Submodule.subset_span hw
      have hw' : ℓ w = ι (T (Function.update v τ ⟨w, hmem⟩)) x := hℓw ⟨w, hmem⟩
      rw [hw']
      set y := T (Function.update v τ ⟨w, hmem⟩)
      have hpos : 0 < GlobalTheory.Grow.height V x ^ N := pow_pos (GlobalTheory.Grow.height_pos V x) N
      have hsz : p 0 y = (GlobalTheory.Size.growthSize V N (ι y)).toReal := by
        rw [hp]; simp [GlobalTheory.Size.growthSob]
      have hne : GlobalTheory.Size.growthSize V N (ι y) ≠ ⊤ := by
        have := hfin y 0; simpa [GlobalTheory.Size.growthSob] using this
      have hb : ‖ι y x‖ ≤ GlobalTheory.Grow.height V x ^ N * p 0 y := by
        have h1 : ENNReal.ofReal (‖ι y x‖ / GlobalTheory.Grow.height V x ^ N) ≤ GlobalTheory.Size.growthSize V N (ι y) :=
          le_iSup (fun g => ENNReal.ofReal (‖ι y g‖ / GlobalTheory.Grow.height V g ^ N)) x
        rw [ENNReal.ofReal_le_iff_le_toReal hne, div_le_iff₀ hpos, ← hsz] at h1
        linarith
      have hs : ((L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ)).map
          fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum = GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L (⟨w, hmem⟩ : M.sm τ) := by
        unfold GlobalTheory.SmoothGlob.sobNorm
        rw [List.map_map]
        congr 1
        refine List.map_congr_left fun l _ => ?_
        simp only [Function.comp_apply, GlobalTheory.GKExtFields.foldr_dRep_conj]
      rw [hs, mul_assoc]
      exact hb.trans (mul_le_mul_of_nonneg_left (hC ⟨w, hmem⟩) hpos.le)

end GlobalTheory.GKExtFields

end
end

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casselmanWallach_multMap_equivariant_sobolevContinuous : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (ι : E →ₗ[ℂ] (GA D V → ℂ)) (N : ℕ) (π : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ d x, p d x = (GlobalTheory.Size.growthSob θ V d N (ι x)).toReal) → (∀ x d, GlobalTheory.Size.growthSob θ V d N (ι x) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ x, ι (π τ g x) = rTr V ((GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ g) (ι x)) → ∀ T : MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) E, (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) → (∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → ι (T (Function.update v τ w)) = rTr V (atTau θ V τ g) (ι (T v))) ∧ ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := by
  atlas_forward_decl GlobalTheory.GKExtFields.multMap_fields
end

section
section
noncomputable section

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S GlobalTheory.SmVec GlobalTheory.MultGelf Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EquivValues

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def IsEquivMap (θ : InfFam D) (M : DSModel V S) (T : MMap M) : Prop :=
  ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)

def IsSobValued (M : DSModel V S) (T : MMap M) : Prop :=
  ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

variable {θ : InfFam D} {M : DSModel V S} {T : MMap M}

theorem rder_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieG (gramAt D V τ)) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X u) :
    Rder θ V τ X (T (Function.update v τ u)) = T (Function.update v τ w) := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hC τ v x
  obtain ⟨m, ls, a, hls, ha⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (mem_sm M τ).1 u.2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => T (Function.update v τ u) (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := hE τ _ (exp_mem_UH hG hX t) (Function.update v τ u) ⟨_, (mem_sm M τ).2 (hmem t)⟩
      (by rw [Function.update_self]; rfl)
    rw [Function.update_idem] at h2
    have h3 := hℓT ⟨_, (mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  have h4 : HasDerivAt (fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ)
      (∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (dRep (trRep (M.σ τ) (M.fr τ)) X u)⟫_ℂ) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
      (GlobalTheory.T.lieWord_commutes_oneParameter_derivative _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
    simpa using h5
  unfold Rder
  rw [h1, h4.deriv, ← hℓT w, hw, ha _ (dRep_mem hG (isURep M τ) hu hX)]

theorem rderC_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (T (Function.update v τ u)) = T (Function.update v τ w) := by
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  have hp := parts_mem hG (gram_herm (M.fr_gram τ)) Z
  have hu := (mem_sm M τ).1 u.2
  have h1 := rder_apply hE hC τ v hp.1 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ rfl
  have h2 := rder_apply hE hC τ v hp.2 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ rfl
  have h3 : w = ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ +
      Complex.I • ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ := Subtype.ext hw
  rw [h3, T.map_update_add, T.map_update_smul, ← h1, ← h2]
  rfl

theorem foldr_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (T (Function.update v τ u)) =
        T (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (isURep M τ) Z ((mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply hE hC τ v Z w _ rfl

theorem gelf_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = gelfH (gramAt D V τ) (M.rep τ) k (v τ)) :
    gelf θ V τ k (T v) = T (Function.update v τ w) := by
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply hE hC τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : w = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [hw, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  rw [h1]
  refine Eq.trans ?_ (map_sum (T.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

theorem gelf_eigen (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) :
    ∃ c : ℂ, gelf θ V τ k (T v) = c • T v := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  obtain ⟨c, hc⟩ := GelfScalar.gelfH_scalar _ (M.ε τ) (M.H τ) (M.σ τ) (M.fr τ) (gramAt D V τ) (M.fr_unit τ)
    (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 k
  refine ⟨c, ?_⟩
  have hv := hc _ ((mem_sm M τ).1 (v τ).2)
  rw [gelf_apply hE hC τ k v (c • v τ) (by rw [Submodule.coe_smul]; exact hv.symm)]
  have := T.map_update_smul v τ c (v τ)
  rw [Function.update_eq_self] at this
  exact this

theorem zfin (hθ : IsInfFam θ) (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (v : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ T v ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨ℂ ∙ T v, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := gelf_eigen hE hC τ k v
  rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf τ k).smul, hc]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

theorem isAutFunSm : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : MMap M) (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) → (∀ v, Continuous (T v) ∧ (∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, T v (g * k) = T v g) ∧ T v ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T v) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)) → (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) → ∀ v, IsAutFunSm θ V (T v) := by
  intro _ D θ hθ V S M T U N hU hT hE hC v
  obtain ⟨h1, h2, h3, h4, h5⟩ := hT v
  exact GlobalTheory.Grow.UnifModGrowth.isAutFunSm hθ ((GlobalTheory.Size.unifModGrowth_iff_growthSob hθ h4).2 ⟨N, h5⟩)
    ⟨h2, ⟨U, hU, h3⟩, h1⟩ h4 (zfin hθ hE hC v)

end GlobalTheory.EquivValues

end
end

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphicForm_multMap_value : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : MMap M) (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) → (∀ v, Continuous (T v) ∧ (∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, T v (g * k) = T v g) ∧ T v ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T v) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)) → (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) → ∀ v, IsAutFunSm θ V (T v) := by
  atlas_forward_decl GlobalTheory.EquivValues.isAutFunSm
end

section
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GKExtLevel

theorem sobCont_sub_smul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ₁ ℓ₂ : H →ₗ[ℂ] ℂ}
    (c : ℂ) (h₁ : Sobolev₂ Lie σ ℓ₁) (h₂ : Sobolev₂ Lie σ ℓ₂) : Sobolev₂ Lie σ (ℓ₁ - c • ℓ₂) := by
  obtain ⟨S₁, C₁, hS₁, hC₁⟩ := h₁
  obtain ⟨S₂, C₂, hS₂, hC₂⟩ := h₂
  refine ⟨S₁ ++ S₂, |C₁| + ‖c‖ * |C₂|, fun l hl X hX => ?_, fun w hw => ?_⟩
  · rcases List.mem_append.1 hl with h | h
    exacts [hS₁ l h X hX, hS₂ l h X hX]
  · have nn : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
      fun S => List.sum_nonneg fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    have n1 := nn S₁
    have n2 := nn S₂
    rw [List.map_append, List.sum_append]
    have b1 := (hC₁ w hw).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) n1)
    have b2 := (hC₂ w hw).trans (mul_le_mul_of_nonneg_right (le_abs_self C₂) n2)
    have e : ‖(ℓ₁ - c • ℓ₂) w‖ ≤ ‖ℓ₁ w‖ + ‖c‖ * ‖ℓ₂ w‖ := by
      rw [← norm_mul]
      simpa using norm_sub_le (ℓ₁ w) (c * ℓ₂ w)
    have h3 := mul_le_mul_of_nonneg_left b2 (norm_nonneg c)
    have p1 : 0 ≤ |C₁| * (S₂.map fun l => ‖l.foldr (dRep σ) w‖).sum := mul_nonneg (abs_nonneg _) n2
    have p2 : 0 ≤ ‖c‖ * |C₂| * (S₁.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _)) n1
    nlinarith

theorem lev : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ →
    ∀ T : MMap M, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ →
    (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
      ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) →
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  intro hHC D θ _ V S M J χ μ 𝓕 T₀ hT₀ T hext hcont v k hk g
  have hsm : ∀ τ, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, w ∈ M.sm τ := fun τ w hw => by
    haveI := (M.ds τ).1
    exact Submodule.subset_span (GlobalTheory.Published.HarishChandraModules.smoothVec hHC (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 hw
      (M.fr_unit τ) (M.fr_gram τ))
  have key : ∀ s : Finset D.what₂.Tau, ∀ v : M.Vec, (∀ τ ∉ s, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) →
      T v (g * k) = χ k * T v g := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      rw [hext v (fun τ => ⟨v τ, hv τ (Finset.notMem_empty τ)⟩) (fun τ => rfl)]
      exact hT₀.2.2.2.2.2.1 _ k hk g
    | @insert τ s hτ ih =>
      intro v hv
      obtain ⟨ℓ₁, h₁, e₁⟩ := hcont τ v (g * k)
      obtain ⟨ℓ₂, h₂, e₂⟩ := hcont τ v g
      have h0 : ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (ℓ₁ - χ k • ℓ₂) w = 0 := by
        intro w hw
        have hi := ih (Function.update v τ ⟨w, hsm τ w hw⟩) (fun τ' hτ' => by
          by_cases h : τ' = τ
          · subst h
            simpa using hw
          · rw [Function.update_of_ne h]
            exact hv τ' (by simp [h, hτ']))
        have a1 := e₁ ⟨w, hsm τ w hw⟩
        have a2 := e₂ ⟨w, hsm τ w hw⟩
        simp only at a1 a2
        rw [LinearMap.sub_apply, LinearMap.smul_apply, a1, a2, hi, smul_eq_mul, sub_self]
      have hz := GlobalTheory.T.sobolevForm_eq_zero_on_smooth_of_kFinite_discreteSeries hHC D V S M τ _ (sobCont_sub_smul (χ k) h₁ h₂) h0 (v τ) (v τ).2
      have a1 := e₁ (v τ)
      have a2 := e₂ (v τ)
      rw [Function.update_eq_self] at a1 a2
      rw [LinearMap.sub_apply, LinearMap.smul_apply, a1, a2, smul_eq_mul, sub_eq_zero] at hz
      exact hz
  exact key Finset.univ v fun τ h => absurd (Finset.mem_univ τ) h

end GlobalTheory.GKExtLevel
end

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gKMap_extension_level_character_covariant : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ → ∀ T : MMap M, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ → (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) → ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  atlas_forward_decl GlobalTheory.GKExtLevel.lev
end

section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GKExt

theorem kset_sub {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g ∈ Formalism.MainNotions.S.UJset ε := by
  have h1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
  rw [Matrix.star_eq_conjTranspose] at h1
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem conj_back {n : ℕ} {P g : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem conj_mem_lieAt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) :
    (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
  have hX' : Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X = 0 := hX
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
  rw [← M.fr_gram τ]
  have e : ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) +
      (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * X * M.fr τ) =
      (M.fr τ)ᴴ * ((Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X) * M.fr τ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hc, Matrix.mul_nonsing_inv_cancel_left _ _ hd,
      Matrix.add_mul, Matrix.mul_add]
  rw [e, hX', Matrix.zero_mul, Matrix.mul_zero]

theorem exp_conj_inv {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := by
  rw [← Matrix.exp_conj' _ _ hg, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_mem_UH {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset ε) :
    P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hk : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  change (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P) = G
  calc (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P)
      = Pᴴ * (gᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) * g) * P := by
        rw [← h]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h1, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk, h]

theorem extExists : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7,
    GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.ExtExists D := by
  intro hHC hCW D θ hθ V S M J χ μ 𝓕 _ _ T₀ hT₀
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨U, N, hU, hTU⟩ := GlobalTheory.T.exists_common_level_growth_exponent_gKMap hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀
    obtain ⟨E, i1, i2, i3, i4, i5, i6, p, ι, hinj, hrange, hp, hπ⟩ :=
      GlobalTheory.T.exists_smoothCuspForm_frechet_moderateGrowth_rep D θ hθ V (GlobalTheory.ChainFr.Fr.ofModel M) U N hU
    choose π dπ hπ using hπ
    have hmem : ∀ u, T₀ u ∈ LinearMap.range ι := fun u => by
      have ha := hT₀.1 u
      obtain ⟨x, hx⟩ := (hrange _).2 ⟨ha.cont, ha.left, (hTU u).1, hT₀.2.1 u, hT₀.2.2.1 u, (hTU u).2⟩
      exact ⟨x, hx⟩
    let e := LinearEquiv.ofInjective ι hinj
    let T₀' : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E :=
      e.symm.toLinearMap.compMultilinearMap (T₀.codRestrict (LinearMap.range ι) hmem)
    have hT₀' : ∀ u, ι (T₀' u) = T₀ u := fun u => by
      have h1 := congrArg Subtype.val (e.apply_symm_apply ⟨T₀ u, hmem u⟩)
      rw [LinearEquiv.ofInjective_apply] at h1
      exact h1
    have hK : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ),
        (w : M.H τ) = M.σ τ k (u τ) → T₀' (Function.update u τ w) = π τ k (T₀' u) := by
      intro τ k hk u w hw
      apply hinj
      rw [(hπ τ).2.1 k (kset_sub hk), hT₀', hT₀']
      have hk' : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := conj_back (M.fr_unit τ)
      have hmax : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ := by
        change M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
        rw [hk']; exact hk
      refine (hT₀.2.2.2.2.2.2.1 τ _ hmax u w ?_).trans rfl
      rw [hw]
      show _ = M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹) _
      rw [hk']
    have hL : ∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M)
        (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) →
        T₀' (Function.update u τ w) = dπ τ X (T₀' u) := by
      intro τ X hX u w hw
      apply hinj
      rw [(hπ τ).2.2 X hX, hT₀', hT₀']
      have hd : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) = dRep (M.σ τ) X := by
        funext y
        unfold dRep
        congr 1
        funext t
        show M.σ τ (M.fr τ * NormedSpace.exp (t • ((M.fr τ)⁻¹ * X * M.fr τ)) * (M.fr τ)⁻¹) y = _
        rw [exp_conj_inv (M.fr_unit τ), conj_back (M.fr_unit τ)]
      exact hT₀.2.2.2.2.2.2.2 τ _ (conj_mem_lieAt M τ hX) u w (by rw [hw, hd])
    have hcomm : ∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'),
        (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g) := by
      intro τ τ' hne g hg g' hg'
      ext x
      apply hinj
      simp only [ContinuousLinearMap.comp_apply]
      rw [(hπ τ).2.1 g hg, (hπ τ').2.1 g' hg', (hπ τ').2.1 g' hg', (hπ τ).2.1 g hg]
      funext y
      simp only [rTr, mul_assoc]
      exact congrArg (fun z => ι x (y * z)) (GlobalTheory.T.realPlacePoint_commute_of_ne_place D θ hθ V τ τ' hne _ (conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) _
        (conj_mem_UH (M.fr_unit τ') (M.fr_gram τ') hg'))
    obtain ⟨TE, hTE1, hTE2, hTE3⟩ := GlobalTheory.T.multilinear_gKMap_extends_to_smooth_vectors hHC hCW D V S M E p π dπ (fun τ => (hπ τ).1) hcomm T₀' hK hL
    obtain ⟨hequiv, hcont⟩ := GlobalTheory.T.casselmanWallach_multMap_equivariant_sobolevContinuous D θ V S M E p ι N π hp
      (fun x d => ((hrange (ι x)).1 ⟨x, rfl⟩).2.2.2.2.2 d) (fun τ => (hπ τ).2.1) TE hTE2 hTE3
    let T : MMap M := ι.compMultilinearMap TE
    have hext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ := fun v u h => by
      show ι (TE v) = T₀ u
      rw [hTE1 v u h, hT₀']
    refine ⟨T, ⟨?_, fun v => ((hrange _).1 ⟨TE v, rfl⟩).2.2.2.2.1,
      GlobalTheory.T.gKMap_extension_level_character_covariant hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀ T hext hcont, hequiv, hcont⟩, hext⟩
    exact GlobalTheory.T.isSmoothAutomorphicForm_multMap_value hHC D θ hθ V S M T U N hU (fun v => by
      have h := (hrange (ι (TE v))).1 ⟨TE v, rfl⟩
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩) hequiv hcont
  · rintro T T' ⟨hT, hTe⟩ ⟨hT', hT'e⟩
    have hd : T - T' ∈ Mult θ M J χ := Submodule.sub_mem _ (Submodule.subset_span hT) (Submodule.subset_span hT')
    refine sub_eq_zero.1 (GlobalTheory.KFiniteDetermined.restrInj D θ hθ V S M J χ (T - T') hd fun v hv => ?_)
    rw [MultilinearMap.sub_apply, hTe v (fun τ => ⟨v τ, hv τ⟩) (fun τ => rfl),
      hT'e v (fun τ => ⟨v τ, hv τ⟩) (fun τ => rfl), sub_self]

end GlobalTheory.GKExt
end
