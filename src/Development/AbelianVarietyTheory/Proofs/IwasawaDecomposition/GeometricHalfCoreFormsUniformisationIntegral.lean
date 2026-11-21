import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JEvExistsAndJEvBar
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsIndependentGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspFormOfExtremalVectorMultiplicity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedSectionOfBoundedHolomorphicForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicCuspFormOfAdelicConstantTermsZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreDictionaryGoodAtGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelConjugationAntilinearBijection
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLatOfOfLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfShortRule
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeries
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemHolSubIff
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionPreservesIntegralCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeoActOfTiesOfEquivAll

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemberEvalInj

theorem evInj_of_tieIn : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → EvInj T R v₀ :=
  fun _ _ _ _ _ _ _ T _ R _ v₀ _ hm ht _ => GlobalTheory.EvalAtUnitVector.evInj T R v₀ hm.HW ht.hv₀

end GlobalTheory.MemberEvalInj
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingSpan

section Gen

variable {K C H Y : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H] {σ : K →+* ℂ}

theorem span_range_eq_basis {n : ℕ} (b : Module.Basis (Fin n) K C) (j : C →ₛₗ[σ] H) :
    Submodule.span ℂ (Set.range j) = Submodule.span ℂ (Set.range fun k => j (b k)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨f, rfl⟩
    rw [← b.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩

theorem span_eq_top_of_ev (j : C → H) (ev : H →ₗ[ℂ] (Y → ℂ)) (hinj : Function.Injective ev)
    (h : ∀ x, ev x ∈ Submodule.span ℂ (Set.range fun f => ev (j f))) : Submodule.span ℂ (Set.range j) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have e : (Set.range fun f => ev (j f)) = ev '' Set.range j := Set.range_comp ev j
  have h1 := h x
  rw [e, Submodule.span_image] at h1
  obtain ⟨y, hy, hxy⟩ := h1
  exact hinj hxy ▸ hy

theorem indep_conj {m : ℕ} {φ : Fin m → Y → ℂ} (h : LinearIndependent ℂ φ) :
    LinearIndependent ℂ fun k g => starRingEnd ℂ (φ k g) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc k
  have h2 : ∑ i, star (c i) • φ i = 0 := by
    funext g
    have := congrArg (starRingEnd ℂ) (congrFun hc g)
    simpa [Finset.sum_apply] using this
  simpa using h _ h2 k

end Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def evL (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' a b := by simp [evAt]
  map_smul' c a := by simp [evAt]

set_option maxHeartbeats 1000000 in

theorem jUnif_of (hl : LawsJ T) (hJ : JEvExists T R κ v₀) (hB : JEvBar T R κ) (hI : EvInj T R v₀)
    (h1 : ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (m : ℕ) (b : Fin m → Cu T κ i),
      LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)))
    (h2 : ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c (res T σ) → ∀ (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (x : (R.HW i σ).H),
      evAt R i σ (v₀ i σ) x ∈
        Submodule.span ℂ (Set.range fun f : Cu T κ i => phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1))))
    (h3 : ∀ (i : Fin D.R.m) σ, ¬ GoodEmb T.Q.c (res T σ) →
      Module.finrank ℂ (R.HW i σ).H ≤ Module.finrank ℂ (R.HW i ((starRingEnd ℂ).comp σ)).H) :
    JUnif T R κ v₀ := by
  have good : ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c (res T σ) →
      (∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
        LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k)) ∧
      Submodule.span ℂ (Set.range (jTop T R κ v₀ i σ)) = ⊤ := by
    intro i σ hσ
    have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hl.spaceW _ (inR i) _ hσ
    have he : ∀ f, evL T R i σ (v₀ i σ) (jTop T R κ v₀ i σ f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) :=
      jTop_good T R κ v₀ hσ hV (hJ i σ hσ hV)
    refine ⟨fun m b hb => LinearIndependent.of_comp (evL T R i σ (v₀ i σ)) ?_,
      span_eq_top_of_ev _ (evL T R i σ (v₀ i σ)) (hI i σ hσ) fun x => ?_⟩
    · have e : (evL T R i σ (v₀ i σ)) ∘ (fun k => jTop T R κ v₀ i σ (b k)) =
          fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) := funext fun k => he (b k)
      rw [e]
      exact h1 i _ hσ hV m b hb
    · rw [funext he]
      exact h2 i σ hσ hV x
  intro i σ
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · exact good i σ hσ
  have hσ' : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := hl.spaceW _ (inR i) _ hσ'
  obtain ⟨v, -, he⟩ := jTop_bar T R κ v₀ hσ hV (hB i σ hσ hV)
  have hind : ∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
      LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k) := fun m b hb => by
    refine LinearIndependent.of_comp (evL T R i σ v) ?_
    have e : (evL T R i σ v) ∘ (fun k => jTop T R κ v₀ i σ (b k)) =
        fun k g => starRingEnd ℂ (phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) g) := funext fun k => he (b k)
    rw [e]
    exact indep_conj (h1 i _ hσ' hV m b hb)
  refine ⟨hind, ?_⟩
  obtain ⟨b⟩ := hasB_nTop T hl κ i
  have hs := (good i ((starRingEnd ℂ).comp σ) hσ').2
  rw [span_range_eq_basis b] at hs ⊢
  have d1 : Module.finrank ℂ (R.HW i ((starRingEnd ℂ).comp σ)).H ≤ nTop T κ i := by
    rw [← finrank_top, ← hs]
    exact (finrank_range_le_card _).trans (Fintype.card_fin _).le
  have hi := hind _ b b.linearIndependent
  refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
  rw [finrank_span_eq_card hi, Fintype.card_fin]
  exact (h3 i σ hσ).trans d1

end GlobalTheory.ReadingSpan
end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingSpan

theorem lastPos_of_kapIs {D : D7} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} (h : KapIs κ) (i : Fin D.R.m) :
    ∀ τ k, 1 ≤ (κ i).aP τ k := by
  intro τ k
  rw [(h i τ).1 k, show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by simp only [Ranks.sigW]; omega
  have hk2 := k.2
  have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) (D.R.k + i - 1 - k) k (by simp only [Ranks.r]; omega)
  have h4 : Formalism.L2.NTheta.lamAt (D.hc τ) (k + (D.R.k + i - 1 - k)) = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dif_neg (by omega), dif_pos (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  have h5 := (D.hc τ).gap_be i
  have h6 : ((D.R.k + i - 1 - k : ℕ) : ℚ) = ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (k + 1) := by
    rw [show D.R.k + i - 1 - k = (D.R.sigW ((i : ℕ) + 1)).1 - (k + 1) by omega, Nat.cast_sub hk2]
    push_cast
    rfl
  rw [h4, h6] at h3
  simp only [aPl, if_pos k.2]
  rw [Int.le_toNat (Int.floor_nonneg.2 (by linarith)), Int.le_floor]
  push_cast
  linarith

theorem finrank_le_of_antilinear {H H' : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    [FiniteDimensional ℂ H'] (e : H ≃ₗ⋆[ℂ] H') : Module.finrank ℂ H ≤ Module.finrank ℂ H' := by
  have b := Module.finBasis ℂ H'
  have h : Submodule.span ℂ (Set.range fun k => e.symm.toLinearMap (b k)) = ⊤ := by
    rw [← span_range_eq_basis b e.symm.toLinearMap, show Set.range e.symm.toLinearMap = Set.univ from Set.range_eq_univ.2 e.symm.surjective, Submodule.span_univ]
  rw [← finrank_top, ← h]
  exact (finrank_range_le_card _).trans (Fintype.card_fin _).le

theorem adel_rdU_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
      (rdU (T.U j σ) f) = ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ)⁻¹ • phiC T hV a f := by
  subst hV
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  exact (inv_smul_smul₀ hl _).symm

set_option maxHeartbeats 1000000 in

theorem evAt_mem_span (hP : GlobalTheory.Published.CuspRapidDecay)
    {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels)
    (ht : TieIn T R κ v₀) (hp : T.pb = R.C.P.pb) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (hσ : GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i)
    (x : (R.HW i σ).H) : evAt R i σ (v₀ i σ) x ∈
      Submodule.span ℂ (Set.range fun f : Cu T κ i => phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1))) := by
  obtain ⟨hs, -, w, hw⟩ := GlobalTheory.HolDict.holShape_of_good D G Pl0 T0 A T R κ v₀ ht i σ hσ
  have hg := GlobalTheory.T.coreDictionary_good_at_good_embedding D G Pl0 T0 A T R κ v₀ hL hM ht hp i σ hσ hV w hw
  have hx : (R.HW i σ).e x ∈ R.Wall i σ := (hM.HW i σ).2.1 ▸ LinearMap.mem_range_self _ x
  obtain ⟨h1, h2⟩ := GlobalTheory.T.holomorphic_cusp_form_of_extremal_vector_multiplicity hP D R.θ _ _ (R.MW i σ) w (v₀ i σ) hM.inf hs hw (ht.hv₀ i σ).1 _ _ _ hx
  rw [show levChi _ (R.βW i) (R.datWp i R.triv) = fun _ => 1 from funext (GlobalTheory.ConjEval.levChi_principal R i)] at h1
  obtain ⟨P, hP0, hPb, hP⟩ := GlobalTheory.T.exists_boundedSection_of_boundedHolomorphicForm D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hs hg _ h1
  have hc := GlobalTheory.T.isHolomorphicCuspForm_of_adelic_constantTerms_zero D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hs hg P hPb (hP.symm ▸ h2)
  have hτ : D.what₂.Tau := D.eTau.symm ⟨1, Subgroup.one_mem _⟩
  have hmem := GlobalTheory.OntoCore.holSub0_le_span_cuspA D T ht.laws _ (inR i) (κ i) (fun τ k _ => lastPos_of_kapIs ht.kap i τ k)
    ((ht.kap i hτ).2.2.symm ▸ hn) _ hσ ⟨holCusp_mem_holSub _ _ hc, hP0⟩
  have h3 := Submodule.mem_map_of_mem (f := adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ)))
    (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ)))
      (T.cE ((i : ℕ) + 1) (res T σ)))) hmem
  rw [hP, Submodule.map_span] at h3
  refine Submodule.span_le.2 ?_ h3
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  rw [adel_rdU_eq T hV (wtA (κ i)) f]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩)

set_option maxHeartbeats 1000000 in

theorem jUnif : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ → JEvBar T R κ → EvInj T R v₀ → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ := by
  intro hP D G _ _ Pl0 T0 A T _ R κ v₀ hL hM ht hp hJ hB hI hn
  refine jUnif_of T R κ v₀ ht.laws hJ hB hI (GlobalTheory.PhiIndep.phiC_indep D T κ ht.laws)
    (evAt_mem_span hP T R κ v₀ hL hM ht hp hn) fun i σ hσ => ?_
  obtain ⟨e⟩ := (GlobalTheory.T.hilbertModel_conjugation_antilinear_bijection D G Pl0 T0 A T R κ v₀ hM ht).1 i σ hσ
  exact finrank_le_of_antilinear e

end GlobalTheory.ReadingSpan
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MemberLatFull

section Abstract

open NumberField IsDedekindDomain Formalism.L2.Pj

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]

theorem val_smul_nonneg {la : HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : IsVal la v) (a : 𝓞 K) {f : R}
    (h : 0 ≤ v f) : 0 ≤ v ((a : K) • f) := by
  by_cases ha : (a : K) = 0
  · rw [ha, zero_smul, hv.zero]; exact le_top
  · rw [hv.smul _ _ ha]
    refine add_nonneg ?_ h
    exact_mod_cast vAdd_int_nonneg la ha

theorem val_nonneg_of_pow {la : HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : IsVal la v) {f : R} (k : ℕ)
    (h : 0 ≤ v (f ^ (k + 1))) : 0 ≤ v f := by
  by_contra h0
  rw [not_le] at h0
  refine absurd h (not_le.2 ?_)
  clear h
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    rw [pow_succ, hv.mul]
    calc v (f ^ (k + 1)) + v f ≤ v (f ^ (k + 1)) + 0 := add_le_add le_rfl h0.le
      _ < 0 := by simpa using ih

variable (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))

def Den (P : HeightOneSpectrum (𝓞 K) → Prop) (f : R) : Prop :=
  ∃ t : 𝓞 K, t ≠ 0 ∧ ∀ la, P la → ∀ v ∈ Vs la, 0 ≤ v ((t : K) • f)

variable {Vs} (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) {P P' : HeightOneSpectrum (𝓞 K) → Prop}

theorem Den.mono {f : R} (h : Den Vs P f) (hP : ∀ la, P' la → P la) : Den Vs P' f :=
  let ⟨t, h0, h1⟩ := h
  ⟨t, h0, fun la hl => h1 la (hP la hl)⟩

include hV

theorem den_of_smul {f : R} {t : K} (ht : t ≠ 0) (h : Den Vs P (t • f)) : Den Vs P f := by
  obtain ⟨s, hs, h1⟩ := h
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) t
  have hb0 : (b : K) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  have ha : a ≠ 0 := by
    rintro rfl
    simp at ht
  refine ⟨s * a, mul_ne_zero hs ha, fun la hl v hv => ?_⟩
  have := val_smul_nonneg (hV la v hv) b (h1 la hl v hv)
  rw [smul_smul, smul_smul] at this
  convert this using 3
  change algebraMap (𝓞 K) K (s * a) = algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K s * _
  have hb1 : algebraMap (𝓞 K) K b ≠ 0 := hb0
  rw [map_mul]
  field_simp

theorem den_zero : Den Vs P (0 : R) :=
  ⟨1, one_ne_zero, fun la _ v hv => by rw [smul_zero, (hV la v hv).zero]; exact le_top⟩

theorem Den.add {f g : R} (hf : Den Vs P f) (hg : Den Vs P g) : Den Vs P (f + g) := by
  obtain ⟨s, hs, h1⟩ := hf
  obtain ⟨t, ht, h2⟩ := hg
  refine ⟨s * t, mul_ne_zero hs ht, fun la hl v hv => ?_⟩
  have a1 := val_smul_nonneg (hV la v hv) t (h1 la hl v hv)
  have a2 := val_smul_nonneg (hV la v hv) s (h2 la hl v hv)
  rw [smul_smul] at a1 a2
  rw [smul_add, show ((s * t : 𝓞 K) : K) = (s : K) * (t : K) from map_mul (algebraMap (𝓞 K) K) s t]
  rw [mul_comm] at a1
  exact (le_min a1 a2).trans ((hV la v hv).add _ _)

theorem Den.smul {f : R} (hf : Den Vs P f) (a : K) : Den Vs P (a • f) := by
  by_cases ha : a = 0
  · rw [ha, zero_smul]; exact den_zero hV
  · refine den_of_smul hV (inv_ne_zero ha) ?_
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul]

theorem den_of_span {S : Set R} (hS : ∀ g ∈ S, Den Vs P g) {f : R} (hf : f ∈ Submodule.span K S) : Den Vs P f := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact den_zero hV
  | add x y _ _ hx hy => exact hx.add hV hy
  | smul a x _ hx => exact hx.smul hV a

theorem exists_den_of_span {S : Set R}
    (hS : ∀ g ∈ S, ∃ N : ℕ, N ≠ 0 ∧ Den Vs (fun la => (N : 𝓞 K) ∉ la.asIdeal) g) {f : R}
    (hf : f ∈ Submodule.span K S) : ∃ N : ℕ, N ≠ 0 ∧ Den Vs (fun la => (N : 𝓞 K) ∉ la.asIdeal) f := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨1, one_ne_zero, den_zero hV⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M * N, mul_ne_zero hM hN, (hx.mono fun la hl h => hl (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)).add hV
      (hy.mono fun la hl h => hl (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h))⟩
  | smul a x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    exact ⟨N, hN, hx.smul hV a⟩

theorem Den.union {f : R} (h : Den Vs P f) (h' : Den Vs (fun la => ¬ P la) f) : Den Vs (fun _ => True) f := by
  obtain ⟨s, hs, h1⟩ := h
  obtain ⟨t, ht, h2⟩ := h'
  refine ⟨s * t, mul_ne_zero hs ht, fun la _ v hv => ?_⟩
  rw [show ((s * t : 𝓞 K) : K) = (s : K) * (t : K) from map_mul (algebraMap (𝓞 K) K) s t]
  by_cases hl : P la
  · rw [mul_comm, mul_smul]
    exact val_smul_nonneg (hV la v hv) t (h1 la hl v hv)
  · rw [mul_smul]
    exact val_smul_nonneg (hV la v hv) s (h2 la hl v hv)

theorem Den.of_pow {f : R} {k : ℕ} (h : Den Vs P (f ^ (k + 1))) : Den Vs P f := by
  obtain ⟨t, ht, h1⟩ := h
  refine ⟨t, ht, fun la hl v hv => val_nonneg_of_pow (hV la v hv) k ?_⟩
  have := val_smul_nonneg (hV la v hv) (t ^ k) (h1 la hl v hv)
  rw [smul_smul, show ((t ^ k : 𝓞 K) : K) = (t : K) ^ k from map_pow (algebraMap (𝓞 K) K) t k] at this
  rwa [smul_pow, pow_succ (t : K)]

theorem span_latOf_eq_top [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R] (C : Submodule K R)
    (h : ∀ f ∈ C, Den Vs (fun _ => True) f) : Submodule.span K (latOf C Vs hV : Set C) = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨t, ht, h1⟩ := h f.1 f.2
  have ht0 : (t : K) ≠ 0 := by exact_mod_cast ht
  have h2 : (t : K) • f ∈ Submodule.span K (latOf C Vs hV : Set C) :=
    Submodule.subset_span fun la v hv => h1 la trivial v hv
  have h3 := Submodule.smul_mem _ (t : K)⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ ht0, one_smul] at h3

theorem fullLat_of [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R] (C : Submodule K R) [FiniteDimensional K C]
    (N : (K →+* ℂ) → R → ℝ) (hN : ∀ σ, IsNormOn C σ (N σ)) (B : ℝ)
    (hB : ∀ F ∈ C, (∀ la, ∀ v ∈ Vs la, 0 ≤ v F) → F ≠ 0 → -B ≤ ∑ σ : K →+* ℂ, Real.log (N σ F))
    (h : ∀ f ∈ C, Den Vs (fun _ => True) f) : Formalism.IndefR.FWT.FullLat C Vs hV :=
  ⟨GlobalTheory.IntCuspLat.fg_latOf_of_lowerBound C Vs hV N hN B hB, span_latOf_eq_top hV C h⟩

omit hV in
theorem exists_prime_mem (la : HeightOneSpectrum (𝓞 K)) {N : ℕ} (h0 : N ≠ 0) (h : (N : 𝓞 K) ∈ la.asIdeal) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ N ∧ (ℓ : 𝓞 K) ∈ la.asIdeal := by
  induction N using induction_on_primes with
  | zero => exact absurd rfl h0
  | one => exact absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) la.isPrime.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases la.isPrime.mem_or_mem h with h | h
    · exact ⟨p, hp, dvd_mul_right _ _, h⟩
    · obtain ⟨ℓ, h1, h2, h3⟩ := ih (right_ne_zero_of_mul h0) h
      exact ⟨ℓ, h1, h2.mul_left _, h3⟩

omit hV in
theorem isIntegral_zpow_of_pow_eq_one {x : K} {m : ℕ} (hm : 0 < m) (h : x ^ m = 1) (e : ℕ) (z : ℤ) :
    IsIntegral ℤ ((x ^ e) ^ z) := by
  refine IsIntegral.of_pow hm ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul, mul_comm, pow_mul, h, one_pow, one_zpow]
  exact isIntegral_one

end Abstract

section Lat

open NumberField Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem trivAt_of_coprime {Λ : GenLat E n} {N M ℓ : ℕ} (hU : Λ.Unimod) (hL : Λ.LevOK N M) (h : N.Coprime ℓ) :
    Λ.TrivAt ℓ := by
  classical
  refine ⟨N, h, Submodule.smul_le.2 fun r hr v hv => ?_, hL.2.2.trans inf_le_left⟩
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  rw [mul_smul]
  refine Submodule.smul_mem _ _ fun i _ => ?_
  have h1 : (Pi.single i 1 : Fin n → E) ∈ stdLat E n := fun j _ => by
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same]
      exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne hj]
      exact Submodule.zero_mem _
  have h2 : (N : 𝓞 E) • (Pi.single i 1 : Fin n → E) ∈ Λ.La :=
    (hL.2.2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) h1)).1
  obtain ⟨y, hy⟩ := (hU v).1 hv _ h2
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)] at hy
  have h3 : IsIntegral ℤ (IsCMField.complexConj E (algebraMap (𝓞 E) E y)) :=
    map_isIntegral_int (IsCMField.complexConj E : E →+* E) (RingOfIntegers.isIntegral_coe y)
  refine Submodule.mem_one.2 ⟨⟨_, h3⟩, ?_⟩
  change IsCMField.complexConj E (algebraMap (𝓞 E) E y) = _
  rw [hy]
  simp [Algebra.smul_def, mul_comm]

end Lat

section Span

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Dict

theorem isIntegral_w {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (hI : d.I = ⊤)
    {ph : (Fin n → LaJ Xo c d) → c.F} {ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ} {x₀ : Fin n → LaJ Xo c d}
    (h : d.PhiPin ph ψ x₀) (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂) : _root_.IsIntegral ℤ (d.w x0 q) := by
  have hz : ∀ (l : Geo.Tor.Level H) (c : Coeff l), 0 < l.M' ∧ (⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ l.M' = 1 := fun l c => by
    have h0 : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
    have h1 : zeta l.M' ^ l.M' = 1 := (Complex.isPrimitiveRoot_exp l.M' h0.ne').pow_eq_one
    exact ⟨h0, Subtype.ext (by simpa using h1)⟩
  haveI : Subsingleton (LaJ Xo c d) := by
    rw [Submodule.Quotient.subsingleton_iff, hI, Ideal.map_top, Submodule.top_smul]
  obtain ⟨-, -, -, h1, -, h2⟩ := h
  have h3 := h2 q
  rw [finsum_eq_single _ x₀ (fun x hx => absurd (Subsingleton.elim x x₀) hx), h1, map_one, one_mul] at h3
  unfold DeltaDat.w
  rw [map_mul, h3]
  refine _root_.IsIntegral.mul ?_ (isIntegral_zpow_of_pow_eq_one (hz _ d.c₂).1 (hz _ d.c₂).2 _ _)
  exact map_isIntegral_int (d.eF : c.F →+* d.c₂.F) (isIntegral_zpow_of_pow_eq_one (hz _ c).1 (hz _ c).2 _ _)

set_option maxHeartbeats 1000000 in

theorem den_of_large (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (n : ℕ) (hdom : Dom a n) (hn : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n) (f : T.toCore.R j)
    (hf : f ∈ T.toCore.cuspA j a n) : Den (T.toCore.Vs j) (fun _ => True) f := by
  have hC := GlobalTheory.chartIndependence_unconditional
  have hU := h.unf j hj T.toCore.σ₀ T.toCore.good_σ₀
  have hrk : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := hU.1
  have hr : 1 ≤ D.R.r := by
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have h1 : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n := by
    have h0 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have : D.R.r ≤ Module.finrank ℚ D.host.E * D.R.r := Nat.le_mul_of_pos_left _ h0
    omega
  have hd : ∃ d : DeltaDat (T.Q.Xo j) T.Q.c n, d.IsLev ∧
      (∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ d.cδ = 1 ∧
      d.pd = 1 ∧ d.I = ⊤ ∧ d.l₂.A = T.Q.l.A ∧ d.l₂.M = T.Q.l.M ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, e0, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c h1 n 1 ⊤ T.Q.l (T.Q.Xo j) T.Q.c rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨g, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character _ _ _ _ _ _ n d hlev hnr 1
    exact ⟨{ d with φδ := g }, hlev, hnab, hδ, e1, e0, congrArg (·.A) e2, congrArg (·.M) e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hI, hAe, hMe, ph, x₀, hpin⟩ := hd
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL _ _ (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  have hone : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (z : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ z = 1 :=
    fun k _ _ z => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
  have hunit : UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : T.Q.c.Fˣ) : T.Q.c.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [hone K y, hone K y']
    simp
  have hsf : Squarefree d.l₂.M := by
    rw [hMe, h.pins.2.1.1, Nat.squarefree_mul ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)]
    exact ⟨(D.host.g_prime 0).squarefree, (D.host.g_prime 1).squarefree⟩
  have hspan : ∀ bad : ℕ, 0 < bad → f ∈ Submodule.span T.Q.c.F (shortGen (T.Q.Xo j) T.Q.c nab bad 0 a n d) := by
    intro bad hbad
    have htot : ShortValTot (T.Q.Xo j) T.Q.c nab bad 0 a n d :=
      GlobalTheory.shortValTot_of_pinned hL hC _ _ _ _ _ _ n d (GlobalTheory.levelMaps_closed hL _ _ _ h1)
        (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.1
        (GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ (T.Q.Xo j) T.Q.c)
        (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
        nab bad 0 a
    obtain ⟨hr0, hm⟩ := h.modelW j hj T.toCore.σ₀ T.toCore.good_σ₀
    have hsp := GlobalTheory.Dict.holSub0_le_span_shortGen hC _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d T.toCore.σ₀ D.R.r
      (Formalism.L2.PjFree.Unf.ofPj (T.U j T.toCore.σ₀)) T.toCore.good_σ₀ hU hr h.pins.2.1.2
      (fun k k' => ⟨(hm k).1.trans (hm k').1.symm, (hm k).2.trans (hm k').2.symm⟩)
      (fun k ga hga hv => GlobalTheory.RunIn.gamAt_of_lawsM D T.toCore h.toLawsM j hj _ T.toCore.good_σ₀ k ga hga fun x hx => by
        obtain ⟨u, hu, he⟩ := hv x hx
        refine ⟨u, hu, ?_⟩
        rw [he, Nat.cast_smul_eq_nsmul]
        exact add_sub_cancel_left _ _)
      hlev hnab hunit h3 (fun _ => ⟨ph, 1, x₀, hpin⟩) nab bad 0 a hbad hdom hn
      (fun k => h.chiTriv j hj _ T.toCore.good_σ₀ _ _ hdom k) htot
    have hf' := (Formalism.L2.Pj.mem_cusp _ _ _ a n f).1 hf
    have hind := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c
      T.toCore.σ₀ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j T.toCore.σ₀)) hU a n).1
    refine mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU (Formalism.L2.PjFree.Unf.ofPj (T.U j T.toCore.σ₀)))
      (sec (T.Q.Xo j) T.Q.c a n) hind _ (fun g hg => hg.1) hf'.1 (hsp ?_)
    exact ⟨hf'.2 _ T.toCore.good_σ₀, fun k x hx => dif_neg hx⟩
  obtain ⟨st, hnab⟩ := hnab
  have hV : ∀ la, ∀ v ∈ T.toCore.Vs j la, IsVal la v := fun la => isVal_valSet la
  have key : ∀ bad : ℕ, ∀ g ∈ shortGen (T.Q.Xo j) T.Q.c nab bad 0 a n d, ∃ (Λ : GenLat D.host.E n) (N : ℕ),
      Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.LevOK N d.l₂.M ∧
      Den (T.toCore.Vs j) (fun la => ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 T.Q.c.F) ∈ la.asIdeal ∧ Λ.TrivAt ℓ) g := by
    rintro bad g ⟨hsec, Λ, N, x0, P, a1, a2, a3, a4, -, a6, a7⟩
    obtain ⟨t, ht, hb⟩ := GlobalTheory.IntCuspLat.exists_smul_nonneg_of_shortRule D _ _ _ _ _ n d hlev hnab
      (fun k _ _ z => by rw [hone k z, one_pow]) (isIntegral_w d hI hpin) hsf Λ N a1 a3 a4 a P a6 x0 g hsec a7
    refine ⟨Λ, N, a1, a2, a4, den_of_smul hV ht ⟨1, one_ne_zero, ?_⟩⟩
    rintro la ⟨ℓ, b1, b2, b3⟩ v hv
    exact val_smul_nonneg (hV la v hv) 1 (hb la ℓ b1 b2 b3 v hv)
  obtain ⟨N, hN, hden⟩ := exists_den_of_span hV (fun g hg => by
    obtain ⟨Λ, N, a1, -, a4, hg⟩ := key 1 g hg
    refine ⟨N, a4.1.pos.ne', hg.mono fun la hl => ?_⟩
    obtain ⟨ℓ, b1, -, b3⟩ := exists_prime_mem la (N := Ideal.absNorm la.asIdeal)
      (fun h0 => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)) (Ideal.absNorm_mem _)
    refine ⟨ℓ, b1, b3, trivAt_of_coprime a1 a4 ((Nat.Prime.coprime_iff_not_dvd b1).2 ?_).symm⟩
    rintro ⟨m, rfl⟩
    exact hl (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ b3)) (hspan 1 Nat.one_pos)
  refine hden.union hV (den_of_span hV (fun g hg => ?_) (hspan N (Nat.pos_of_ne_zero hN)))
  obtain ⟨Λ, N', -, ⟨k, a2, a3⟩, -, hg⟩ := key N g hg
  refine hg.mono fun la hl => ?_
  obtain ⟨ℓ, b1, b2, b3⟩ := exists_prime_mem la hN (not_not.1 hl)
  exact ⟨ℓ, b1, b3, k, a2.coprime_dvd_right b2, a3⟩

theorem pow_mem_cusp (D : D7) (T : Core D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n)
    (f : T.R j) (hf : f ∈ T.cuspA j a n) (k : ℕ) :
    ∃ a', Dom a' ((k + 1) * n) ∧ f ^ (k + 1) ∈ T.cuspA j a' ((k + 1) * n) := by
  induction k with
  | zero => exact ⟨a, by simpa using hdom, by simpa using hf⟩
  | succ k ih =>
    obtain ⟨a', h1, h2⟩ := ih
    have hm : CuspMul (T.Q.Xo j) T.Q.c (T.U j) :=
      (Formalism.L2.PjFree.cuspMul_ofPj (T.U j)).1 (GlobalTheory.CuspProduct.cuspMul_holds _ _ _ _ _ _ _ _)
    refine ⟨a' + a, ?_, ?_⟩
    · rw [Nat.succ_mul]
      exact ⟨fun τ => (h1.1 τ).add (hdom.1 τ), h1.2.add hdom.2⟩
    · rw [Nat.succ_mul, pow_succ]
      exact hm a' a _ n _ f h1 hdom h2 hf

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem isLattice_latOf (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (hw : 0 < w.n) :
    Formalism.IndefR.FWT.FullLat (T.toCore.C j w) (T.toCore.Vs j) fun la => isVal_valSet la := by
  haveI : FiniteDimensional T.Q.c.F (T.toCore.C j w) := h.cuspFD j hj _ _ (dom_wtA w)
  obtain ⟨B, hB⟩ := GlobalTheory.IntCuspLat.exists_lowerBound D T.toCore h.toLawsM j hj w
  refine fullLat_of _ _ (T.toCore.Ns j w)
    (fun σ => (isNormOn_supC _ (h.supDef j hj) (dom_wtA w) (goodEmb_goodOf _ σ)).of_goodOf) B hB fun f hf => ?_
  obtain ⟨a', h1, h2⟩ := pow_mem_cusp D T.toCore j _ _ (dom_wtA w) f hf (4 * (Module.finrank ℚ D.host.E * D.R.r) + 3)
  exact (den_of_large D T h j hj a' _ h1 (Nat.le_mul_of_pos_right _ hw) _ h2).of_pow fun la => isVal_valSet la

end Span

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latFull_of_tieIn : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → LatFull T κ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ _ _ ht _ i
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; positivity)
  refine isLattice_latOf D T ht.laws _ (inR i) (κ i) ?_
  rw [(ht.kap i τ).2.2]
  have := D.R.rank_add_five_le
  unfold Ranks.nV
  omega

end GlobalTheory.MemberLatFull
end
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeoIn

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}

set_option maxHeartbeats 1000000 in

theorem mkStable_of_rhoGeo (t : FWTie T R κ v₀) (hp : ∀ i, OMPins T R κ v₀ O i) (hr : RhoGeo t O) (i : Fin D.R.m) :
    (R.FW i).MKStable := by
  have hact : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (O i).lev2 := (hp i).2.act.1
  by_cases hk : ActKeeps (κ := κ) O i
  · have h0 := (hr i).1 hk
    intro g x
    have key : ∀ hx : x ∈ (R.FW i).WK, (R.FW i).ρ g x ∈ (R.FW i).WK ∧ (x ∈ (R.FW i).MK → (R.FW i).ρ g x ∈ (R.FW i).MK) := by
      intro hx
      obtain ⟨f, hf⟩ := (t.e i).surjective ⟨x, hx⟩
      have hfx : ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = x := congrArg Subtype.val hf
      subst hfx
      obtain ⟨h1, h2⟩ := h0 g f
      rw [← h2]
      refine ⟨(t.e i _).2, fun hm => (t.mem_MK i _).2 ?_⟩
      exact GlobalTheory.LevActInt.intAll_actLev T κ i (O i).lev2 t.laws hact g f ⟨_, h1⟩ rfl ((t.mem_MK i f).1 hm)
    exact ⟨fun hx => (key hx).1, fun hx => (key hx.1).2 hx⟩
  · intro g x
    rw [(hr i).2 hk g]
    exact ⟨id, id⟩

end

set_option maxHeartbeats 1000000 in

theorem inGeo_and_lUnif_and_lIntegral : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (ph : Fin D.R.m → ℂ) (B : GeoHalf T R ph), PreChar R → R.grp_chiW → T.pb = R.C.P.pb → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → InGeo B ∧ R.LUnif ∧ R.LIntegral := by
  intro hP D G _ _ Pl0 T0 A T _ R ph B hC hχ hp hn
  have ht : TieIn T R B.κ B.v₀ := ⟨B.fw.laws, B.fw.alg_eq, B.fw.kap, B.fw.hv₀, B.fw.chiR, B.fw.x0⟩
  have hJ := GlobalTheory.CuspValues.jEvExists_and_jEvBar D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hI := GlobalTheory.MemberEvalInj.evInj_of_tieIn D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hU := GlobalTheory.ReadingSpan.jUnif hP D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp hJ.1 hJ.2 hI hn
  have hL := GlobalTheory.MemberLatFull.latFull_of_tieIn D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hG := GlobalTheory.geoAct_of_ties_of_equivAll T R B.κ B.v₀ B.O hC.lev hC.models.inf hC.models.HW ht hp B.pins B.equivAll
  have hx := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R B.κ B.v₀ B.O hC.lev ht hp B.pins
  refine ⟨⟨hJ.1, hJ.2, hI, hU, hG, hL, B.fw.dimMatch⟩, fun i σ => ?_, fun i => ?_⟩
  · exact ⟨(GlobalTheory.TiedUnif.indep_span_of_tie B.fw hC.models.HW B.bar hU i σ).1,
      (GlobalTheory.TiedUnif.indep_span_of_tie B.fw hC.models.HW B.bar hU i σ).2,
      GlobalTheory.TiedUnif.rhoIs_of_eqAt B.fw hC.models.HW hC.models.gW hχ B.bar B.rhoGeo hU i σ
        (fun h hV => B.equivAll i _ h hV (hx i _ h hV))
        fun h hV => B.equivAll i _ (good_resC T h) hV (hx i _ (good_resC T h) hV)⟩
  · exact ⟨B.fw.ks i, GlobalTheory.GoodLat.mkFull_of_tie B.fw hL i, mkStable_of_rhoGeo B.fw B.pins B.rhoGeo i⟩

end GlobalTheory.RealGeoIn
end
