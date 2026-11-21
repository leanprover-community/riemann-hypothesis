import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRegroupCommutative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteMassProductFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGoodReductionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfTwistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteHalfOfTwist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G8FiniteAuxiliaryStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInertStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHypothesesHold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteReindexing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteEulerProductOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonOf

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8.Fin.DoubleCosetCounting

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

theorem avg_comp_mul_left {H : Type} [Group H] (u : H → ℂ) (h : H) : avg (fun y => u (h * y)) = avg u := by
  have hR : rStab (fun y => u (h * y)) = rStab u := by
    ext k
    show (∀ x, u (h * (x * k)) = u (h * x)) ↔ ∀ x, u (x * k) = u x
    constructor
    · intro H x
      have := H (h⁻¹ * x)
      simpa [mul_assoc] using this
    · intro H x
      simpa [mul_assoc] using H (h * x)
  unfold avg
  rw [hR]
  congr 1
  calc ∑ᶠ q : H ⧸ rStab u, u (h * q.out) = ∑ᶠ q : H ⧸ rStab u, u ((h • q).out) := by
        refine finsum_congr fun q => ?_
        obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul (rStab u) (h * q.out)
        have hq : h • q = ((h * q.out : H) : H ⧸ rStab u) := by
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        rw [hq, hr]
        exact (r.2 (h * q.out)).symm
    _ = ∑ᶠ q : H ⧸ rStab u, u q.out := finsum_comp_equiv (MulAction.toPerm h) (f := fun q : H ⧸ rStab u => u q.out)

end PositivityTheory.Rg.BcB.G8.Fin.DoubleCosetCounting

namespace PositivityTheory.Rg.BcB.G8.Fin

open PositivityTheory.Rg.BcB.G8

theorem DcCount_pf : DcCount := by
  intro G _ _ _ θ K Γ δ f _ _ hG hΓ _ _ _ _ _
  have hCT : cptPart (twCent θ δ) ≤ twCent θ δ := (Subgroup.closure_le _).2 fun t ht => ht.1
  have hinv : ∀ t ∈ twCent θ δ, ∀ k ∈ K, ∀ x : G,
      (avg fun k' : K => f ((t * x * k * k')⁻¹ * δ * θ (t * x * k * k'))) =
        avg fun k' : K => f ((x * k')⁻¹ * δ * θ (x * k')) := by
    intro t ht k hk x
    have ht' : t * δ = δ * θ t := ht
    have e1 : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← ht', ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : ∀ y : G, (t * y)⁻¹ * δ * θ (t * y) = y⁻¹ * δ * θ y := by
      intro y
      rw [map_mul, _root_.mul_inv_rev]
      calc y⁻¹ * t⁻¹ * δ * (θ t * θ y) = y⁻¹ * (t⁻¹ * δ * θ t) * θ y := by simp only [mul_assoc]
        _ = y⁻¹ * δ * θ y := by rw [e1]
    have e3 : (fun k' : K => f ((t * x * k * k')⁻¹ * δ * θ (t * x * k * k'))) =
        fun k' : K => (fun y : K => f ((x * y)⁻¹ * δ * θ (x * y))) (⟨k, hk⟩ * k') := by
      funext k'
      have : t * x * k * (k' : G) = t * (x * ((⟨k, hk⟩ * k' : K) : G)) := by simp [mul_assoc]
      rw [this, e2]
    rw [e3]
    exact DoubleCosetCounting.avg_comp_mul_left (fun y : K => f ((x * y)⁻¹ * δ * θ (x * y))) ⟨k, hk⟩
  have hreg := GlobalTheory.T.finsum_doubleCoset_regroup_commutative G (twCent θ δ) Γ (cptPart (twCent θ δ)) K
    (fun x => avg fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))) hG.1 hCT hG.2 hinv
  rw [inf_eq_left.2 hΓ] at hreg
  have key : dcSum Γ K (fun x => f (x⁻¹ * δ * θ x)) =
      ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
        ((Nat.card (Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ *
          avg (fun k : K => f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))) := by
    unfold dcSum
    exact finsum_congr fun q => by rw [div_eq_inv_mul]
  rw [key, hreg]
  rfl

end PositivityTheory.Rg.BcB.G8.Fin

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8.Fin

open PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem unitae_nrm (hU : Unr E) (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    nrmL n w (locEl n w δ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
  by_cases hs : IsSplitAt w
  · unfold nrmL locEl
    rw [if_pos hs, if_pos hs]
  · unfold nrmL locEl
    rw [if_neg hs, if_neg hs]
    obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨hp, -⟩ := hns hs
    rw [map_mul, thE, GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E)) _ (cj w) (fun x => (hp x).symm)]

theorem unitae_single (hU : Unr E) (n : ℕ) (δ : GL (Fin n) E) (hsep : (polE δ).Separable) :
    ∀ᶠ w : Pl E in cofinite, locEl n w δ ∈ GlobalTheory.LFun.KGL w n ∧
      (∀ g : GLw n w, g⁻¹ * locEl n w δ * thL n w g ∈ GlobalTheory.LFun.KGL w n →
        ∃ t ∈ twCent (thL n w) (locEl n w δ), t⁻¹ * g ∈ GlobalTheory.LFun.KGL w n) ∧
      (∀ t ∈ twCent (thL n w) (locEl n w δ), IsCompact (closure (Subgroup.zpowers t : Set (GLw n w))) →
        t ∈ GlobalTheory.LFun.KGL w n) := by
  filter_upwards [GlobalTheory.EulerTwU.eventually_pc_ratF_mem δ, GlobalTheory.EulerTwU.eventually_pc_ratF_mem (δ * thE E n δ),
    GlobalTheory.BCT.SepBezout.bezout_eventually E _ hsep] with w h1 h2 h3
  rw [GlobalTheory.EulerTwU.pc_ratF] at h1 h2
  have hN := unitae_nrm hU n w δ
  have hbez : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w (locEl n w δ)).val.charpoly + v * derivative (nrmL n w (locEl n w δ)).val.charpoly = 1 := by
    have e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ)).val.charpoly =
        (polE δ).map (algebraMap E (w.adicCompletion E)) := Matrix.charpoly_map _ _
    rw [hN, e]
    exact h3
  have hy : locEl n w δ ∈ GlobalTheory.LFun.KGL w n := by
    unfold locEl
    split_ifs
    · exact h2
    · exact h1
  have hNK : nrmL n w (locEl n w δ) ∈ GlobalTheory.LFun.KGL w n := by rw [hN]; exact h2
  refine ⟨hy, ?_, ?_⟩
  · intro g hg
    by_cases hs : IsSplitAt w
    · have hθ : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hnr : nrmL n w (locEl n w δ) = locEl n w δ := by unfold nrmL; rw [if_pos hs]
      rw [hθ, MonoidHom.id_apply] at hg
      rw [hnr] at hbez
      obtain ⟨t, ht, k, hk, hgk⟩ := GlobalTheory.SplitUniq.splitUniq E n w _ g hy hbez hg
      refine ⟨t, ?_, ?_⟩
      · show t * locEl n w δ = locEl n w δ * thL n w t
        rw [hθ, MonoidHom.id_apply]
        exact ht
      · rw [hgk, inv_mul_cancel_left]
        exact hk
    · obtain ⟨t, ht, k, hk, hgk⟩ := GlobalTheory.InertUniq.eq_twCent_mul_KGL E hU n w hs _ g hy hbez hg
      refine ⟨t, ht, ?_⟩
      rw [hgk, inv_mul_cancel_left]
      exact hk
  · intro t ht hc
    have ht' : t * locEl n w δ = locEl n w δ * thL n w t := ht
    have hcomm : t * nrmL n w (locEl n w δ) = nrmL n w (locEl n w δ) * t := by
      by_cases hs : IsSplitAt w
      · have hθ : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
        rw [hθ, MonoidHom.id_apply] at ht'
        unfold nrmL
        rw [if_pos hs]
        exact ht'
      · have hθ : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hs]
        obtain ⟨-, hinv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
        rw [hθ] at ht'
        have hth := GlobalTheory.ThetaPull.thetaGL_thetaGL (a := n) (cj w) hinv t
        unfold nrmL
        rw [if_neg hs]
        calc t * (locEl n w δ * thetaGL n (cj w) (locEl n w δ))
            = locEl n w δ * thetaGL n (cj w) t * thetaGL n (cj w) (locEl n w δ) := by rw [← mul_assoc, ht']
          _ = locEl n w δ * thetaGL n (cj w) (t * locEl n w δ) := by rw [map_mul, mul_assoc]
          _ = locEl n w δ * thetaGL n (cj w) (locEl n w δ * thetaGL n (cj w) t) := by rw [ht']
          _ = locEl n w δ * thetaGL n (cj w) (locEl n w δ) * t := by rw [map_mul, hth, mul_assoc]
    exact GlobalTheory.StabInt.mem_KGL_of_commute E n w _ t hNK hbez hcomm hc

theorem unitae_cpt_fst {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A] [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] (t : A × B) (h : IsCompact (closure (Subgroup.zpowers t : Set (A × B)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set A)) := by
  have hK := h.image continuous_fst
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem unitae_cpt_snd {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B] (t : A × B) (h : IsCompact (closure (Subgroup.zpowers t : Set (A × B)))) :
    IsCompact (closure (Subgroup.zpowers t.2 : Set B)) := by
  have hK := h.image continuous_snd
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem unitAE_holds : UnitAE := by
  intro E _ _ _ hU a b S _ δ₁ δ₂ h₁ h₂
  have hs₁ : (polE δ₁).Separable := by obtain ⟨-, -, h, -⟩ := h₁; exact h
  have hs₂ : (polE δ₂).Separable := by obtain ⟨-, -, h, -⟩ := h₂; exact h
  have hev := (unitae_single hU a δ₁ hs₁).and (unitae_single hU b δ₂ hs₂)
  filter_upwards [(Subtype.val_injective (p := (· ∈ S))).tendsto_cofinite.eventually hev] with w hw
  obtain ⟨⟨hy1, hc1, hk1⟩, ⟨hy2, hc2, hk2⟩⟩ := hw
  rintro y rfl
  refine ⟨Subgroup.mem_prod.2 ⟨hy1, hy2⟩, ?_, ?_⟩
  · rintro ⟨g1, g2⟩ hg
    have hg' := Subgroup.mem_prod.1 hg
    obtain ⟨t1, ht1, hk1'⟩ := hc1 g1 hg'.1
    obtain ⟨t2, ht2, hk2'⟩ := hc2 g2 hg'.2
    refine ⟨(t1, t2), ?_, Subgroup.mem_prod.2 ⟨hk1', hk2'⟩⟩
    have e1 : t1 * locEl a w.1 δ₁ = locEl a w.1 δ₁ * thL a w.1 t1 := ht1
    have e2 : t2 * locEl b w.1 δ₂ = locEl b w.1 δ₂ * thL b w.1 t2 := ht2
    show (t1, t2) * (locEl a w.1 δ₁, locEl b w.1 δ₂) =
      (locEl a w.1 δ₁, locEl b w.1 δ₂) * ((thL a w.1).prodMap (thL b w.1)) (t1, t2)
    exact Prod.ext e1 e2
  · refine (Subgroup.closure_le _).2 fun t ht => ?_
    obtain ⟨ht1, ht2⟩ := ht
    have e : t * (locEl a w.1 δ₁, locEl b w.1 δ₂) =
        (locEl a w.1 δ₁, locEl b w.1 δ₂) * ((thL a w.1).prodMap (thL b w.1)) t := ht1
    have e1 : t.1 ∈ twCent (thL a w.1) (locEl a w.1 δ₁) := congrArg Prod.fst e
    have e2 : t.2 ∈ twCent (thL b w.1) (locEl b w.1 δ₂) := congrArg Prod.snd e
    exact Subgroup.mem_prod.2 ⟨hk1 _ e1 (unitae_cpt_fst t ht2), hk2 _ e2 (unitae_cpt_snd t ht2)⟩

end PositivityTheory.Rg.BcB.G8.Fin

end
end

section
namespace PositivityTheory.Rg.BcB.G8.Fin

theorem kfOC_holds : PositivityTheory.Rg.BcB.G8.KfOC := GlobalTheory.T.finite_kernel_compact_open

theorem finLevel_holds : PositivityTheory.Rg.BcB.G8.FinLevel := GlobalTheory.T.finite_level_facts

theorem suppFin_holds : SuppFin := GlobalTheory.T.finite_support_of_twist GlobalTheory.T.local_support_facts unitAE_holds GlobalTheory.T.rational_finite_places GlobalTheory.T.local_good_reduction

theorem eulerFin_holds : EulerFin :=
  GlobalTheory.T.finite_euler_product_of GlobalTheory.T.finite_conjugacy_exists GlobalTheory.T.finite_restriction_vanishing GlobalTheory.T.aux_statement_21 (GlobalTheory.T.local_comparison_of GlobalTheory.T.local_comparison_inert GlobalTheory.T.local_comparison_split) GlobalTheory.T.local_hypotheses_hold GlobalTheory.T.finite_reindexing

theorem finHalf_holds : PositivityTheory.Rg.BcB.G8.FinHalf :=
  GlobalTheory.T.finite_half_of_twist DcCount_pf GlobalTheory.T.finite_mass_product_formula GlobalTheory.T.rational_finite_places suppFin_holds eulerFin_holds kfOC_holds finLevel_holds

end PositivityTheory.Rg.BcB.G8.Fin
end
