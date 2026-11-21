import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.PullSchLI
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelAssembly

theorem two_mul_finrank_isotropic_le {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E)
    (W : Submodule E B.V) (hW : ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0) : 2 * Module.finrank E W ≤ B.rank := by
  let b := Module.finBasis E W
  have hl : LinearIndependent E fun i => B.hT (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h1 : B.hT ((∑ i, star (c i) • b i : W) : B.V) = 0 := by
      rw [← hc]; simp [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]
    have h2 : (∑ i, star (c i) • b i : W) = 0 := Subtype.ext (B.nondeg.1 _ fun y => by rw [h1]; rfl)
    simpa using Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 i
  have h3 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range fun i => B.hT (b i)))
  rw [finrank_span_eq_card hl, Fintype.card_fin, B.rank_eq] at h3
  have h4 : W ≤ (Submodule.span E (Set.range fun i => B.hT (b i))).dualCoannihilator := fun y hy => by
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; exact hW _ (b i).2 _ hy
    | zero => rfl
    | add _ _ _ _ h h' => rw [LinearMap.add_apply, h, h', add_zero]
    | smul _ _ _ h => rw [LinearMap.smul_apply, h, smul_zero]
  have := Submodule.finrank_mono h4
  omega

theorem bddAbove_isotropic_dims {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    BddAbove {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0} :=
  ⟨B.rank, by rintro _ ⟨W, rfl, hW⟩; have := two_mul_finrank_isotropic_le B W hW; omega⟩

theorem two_mul_wittIdx_le_rank {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    2 * Formalism.MainNotions.SchurIrreducible.wittIdx B ≤ B.rank := by
  obtain ⟨W, h, hW⟩ := Nat.sSup_mem (s := {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧
    ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0}) ⟨_, ⊥, rfl, by simp⟩ (bddAbove_isotropic_dims B)
  rw [Formalism.MainNotions.SchurIrreducible.wittIdx, ← h]
  exact two_mul_finrank_isotropic_le B W hW

theorem exists_isRowBasis {D : D7} {n : ℕ} (U : Submodule D.host.E (Fin n → D.host.E)) :
    ∃ c, IsRowBasis U c := by
  refine ⟨fun i => ((Module.finBasis D.host.E U i : U) : Fin n → D.host.E), ?_, ?_⟩
  · exact (Module.finBasis D.host.E U).linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · have : Set.range (fun i => ((Module.finBasis D.host.E U i : U) : Fin n → D.host.E)) =
        U.subtype '' Set.range (Module.finBasis D.host.E U) := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, (Module.finBasis D.host.E U).span_eq, Submodule.map_subtype_top]

theorem absThetaInt_lt_top_of_eq_zero {D : D7} (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {r : ℕ}
    (hr : r = 0) (φ : Mx D V.rank r → ℂ) : GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ := by
  subst hr
  have hc : ∀ h, GlobalTheory.SiegelFormula.absTheta V φ h = ‖φ 0‖ₑ := by
    intro h
    unfold GlobalTheory.SiegelFormula.absTheta
    haveI : Unique (Matrix (Fin V.rank) (Fin 0) D.host.E) :=
      inferInstanceAs (Unique (Fin V.rank → Fin 0 → D.host.E))
    rw [tsum_eq_single default (fun b hb => absurd (Subsingleton.elim b default) hb)]
    have h0 : GlobalTheory.SiegelFormula.invPt V h (default : Matrix (Fin V.rank) (Fin 0) D.host.E) = 0 := by
      funext i j; exact j.elim0
    rw [h0]
  unfold GlobalTheory.SiegelFormula.absThetaInt
  have hq : ∀ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q = ‖φ 0‖ₑ := fun q => hc _
  simp_rw [hq, lintegral_const]
  exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)

end GlobalTheory.CompanionTheory.SiegelAssembly

namespace GlobalTheory.CompanionTheory.SiegelAssembly

end GlobalTheory.CompanionTheory.SiegelAssembly
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelAssemblyLI

open GlobalTheory.CompanionTheory.SiegelAssembly

theorem weilSiegelFormula_of_chapters_LI : GlobalTheory.Published.WeilThetaConvergence → GlobalTheory.Published.WeilEisensteinSiegelConvergence →
    PullSchLI → EisCells → ThetaOrbits → BigCell → GlobalTheory.Published.WeilSiegelFormula := by
  intro hTh hES hP hE hT hB D n V hn h2n ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω ν hν Φ
  haveI := hν
  have hw : 2 * Formalism.MainNotions.SchurIrreducible.wittIdx V ≤ V.rank := two_mul_wittIdx_le_rank V
  have hSet : HidaSetting D n V ψ χ θ μ ω := ⟨hn, h2n, hψ, hχ, hη, hθ, ⟨𝓕, hμ⟩, hω⟩
  have hconv := hES D n V hn h2n ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω Φ
  choose μr 𝓕r hμr using fun r => GlobalTheory.MixModel.exists_isCovolOne D V.rank r
  choose c hc using fun U : Submodule D.host.E (Fin n → D.host.E) => exists_isRowBasis U
  have hEis := hE D n V ψ χ θ μ ω hSet Φ hconv μr (fun r => ⟨𝓕r r, hμr r⟩) c hc
  have hfib : ∀ U : Submodule D.host.E (Fin n → D.host.E),
      HasSum (fun b : HermE D (Module.finrank D.host.E U) => J ψ V (μr _) (pull (c U) Φ.1) b)
        (Ifr V ν (pull (c U) Φ.1)) := by
    intro U
    have hr : Module.finrank D.host.E U ≤ n := by
      have := Submodule.finrank_le U
      simpa using this
    have hpull := hP D θ hθ V.rank _ n (c U) (hc U).1 Φ.1 Φ.2
    have habs : GlobalTheory.SiegelFormula.absThetaInt V ν (pull (c U) Φ.1) < ⊤ := by
      rcases Nat.eq_zero_or_pos (Module.finrank D.host.E U) with h0 | hpos
      · exact absThetaInt_lt_top_of_eq_zero V ν h0 _
      · exact hTh D _ V hpos (Or.inr (by omega)) θ hθ ν hν ⟨_, hpull⟩
    exact hB D _ V (by omega) ψ hψ θ hθ (μr _) (𝓕r _) (hμr _) ν hν _ hpull habs
      (hEis.summable.sigma_factor U)
  exact (hEis.sigma hfib).unique
    (hT D n V θ hθ ν hν Φ (hTh D n V hn (Or.inr (by omega)) θ hθ ν hν Φ) c hc)

end GlobalTheory.CompanionTheory.SiegelAssemblyLI
end
end
