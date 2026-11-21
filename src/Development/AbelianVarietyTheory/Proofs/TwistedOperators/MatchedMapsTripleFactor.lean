import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumPureMemAlgD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelEqStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsLocalIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZeroStatement

section
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKerFin

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem polZero_om_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, h) Φ) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v h hh Φ hΦ
  classical
  obtain ⟨T, hXT, m, f, φ, hf, rfl, hz⟩ := hΦ
  have hP := GlobalTheory.ThK.RealUniq.isPair_V hM.triple
  have h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := by
    intro u _
    show u • ((1 : UA σ G.V.J).1.1 - 1) = 0
    simp
  have hex : ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ₀ φ₁ :=
    fun φ₀ hφ₀ => GlobalTheory.ThK.LocalOps.acts_exists hP v (1, h) h1 hh φ₀ hφ₀
  choose D hDSB hDA using hex
  have hex' : ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ₀ φ₁ := fun φ₀ hφ₀ => ⟨D φ₀ hφ₀, hDSB φ₀ hφ₀, hDA φ₀ hφ₀⟩
  let Dl : SB (Fin a × Fin (a + a') → Fv F v) →ₗ[ℂ] SB (Fin a × Fin (a + a') → Fv F v) :=
    { toFun := fun x => ⟨D x.1 x.2, hDSB x.1 x.2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) hex' x.2 y.2 (hDA x.1 x.2) (hDA y.1 y.2) 1 1
        simp only [one_smul] at hl
        exact GlobalTheory.ThK.LocalOps.acts_unique v _ (x + y).2 (hDA _ (x + y).2) hl
      map_smul' := fun c x => by
        apply Subtype.ext
        have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) hex' x.2 x.2 (hDA x.1 x.2) (hDA x.1 x.2) c 0
        simp only [zero_smul, add_zero] at hl
        exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • x).2 (hDA _ (c • x).2) hl }
  let π : SB (Fin a × Fin (a + a') → Fv F v) →ₗ[ℂ] Rf.Pi v := (Rf.p v).comp (SB _).subtype
  have hsurj : Function.Surjective π := by
    intro y
    have hy : y ∈ (SB _).map (Rf.p v) := (hM.fin.onto v).symm ▸ Submodule.mem_top
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hA0 : Acts (evFin F v) (om' (1, h)) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) 0 := by
    intro r _
    have e : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext y; simp [tens]
    rw [e, map_zero]
  have hD : ∀ x, π x = 0 → π (Dl x) = 0 := by
    intro x hx
    have e := hM.fin.equiv v h hh x.1 x.2 0 (zero_mem _) (D x.1 x.2) (hDSB x.1 x.2) 0 (zero_mem _) (hDA x.1 x.2) hA0
      (by rw [map_zero]; exact hx)
    rw [map_zero] at e
    exact e
  let L : Rf.Pi v →ₗ[ℂ] Rf.Pi v := GlobalTheory.ThK.RealUniq.induced π hsurj Dl hD
  let ψ : Fin m → (Fin a × Fin (a + a') → Fv F v) → ℂ := fun i => D (φ i v) ((hf i).2.1 v)
  have hL : ∀ i, L (Rf.p v (φ i v)) = Rf.p v (ψ i) := fun i =>
    GlobalTheory.ThK.RealUniq.induced_apply π hsurj Dl hD ⟨φ i v, (hf i).2.1 v⟩
  let φ₂ : Fin m → ∀ w : Pl F, (Fin a × Fin (a + a') → Fv F w) → ℂ := fun i => Function.update (φ i) v (ψ i)
  have hstd : ∀ i, ∀ᶠ w in Filter.cofinite, φ i w = Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [hM.triple.geo.hM.std, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    rw [(hf i).2.2 w hwT, hw]
  have hpure : ∀ i, om (1, h) (pure (f i) (φ i)) = pure (f i) (φ₂ i) := fun i =>
    GlobalTheory.ThK.LocalOps.acts_pure v (om (1, h)) (f i) (φ i) (ψ i)
      (GlobalTheory.TensUniq.pure_mem_schA _ _ (hf i).2.1 (hstd i)) (fun x => GlobalTheory.PureFactor.mulSupport_finite _ (hstd i) x)
      (hDA _ _)
  have hv : v ∈ insert v T := Finset.mem_insert_self _ _
  have hTS : T ⊆ insert v T := Finset.subset_insert _ _
  refine ⟨insert v T, hXT.trans hTS, m, f, φ₂, fun i => ⟨(hf i).1, fun w => ?_, fun w hw => ?_⟩, ?_, ?_⟩
  · by_cases hwv : w = v
    · subst hwv
      simp only [φ₂, Function.update_self]
      exact hDSB _ _
    · simp only [φ₂, Function.update_of_ne hwv]
      exact (hf i).2.1 w
  · rw [Finset.mem_insert, not_or] at hw
    simp only [φ₂, Function.update_of_ne hw.1]
    exact (hf i).2.2 w hw.2
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hpure i
  · have hz' := GlobalTheory.PolMatchLin.transport Bs G Xc om om' R Rf hM.fin hXT hTS f φ
      (fun j : Fin 0 => j.elim0 : Fin 0 → SInf F (Fin a' × Fin (a + a')))
      (fun j : Fin 0 => j.elim0 : Fin 0 → ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ)
      (fun i => (hf i).2.2) (fun j => j.elim0) (by rw [hz]; simp)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hz'
    let Lw : ∀ u : (insert v T : Finset (Pl F)), Rf.Pi u →ₗ[ℂ] Rf.Pi u :=
      Function.update (fun _ => LinearMap.id) ⟨v, hv⟩ L
    have key := congrArg (LinearMap.lTensor R.Pi (PiTensorProduct.map Lw)) hz'
    rw [map_zero, map_sum] at key
    rw [← key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.lTensor_tmul, PiTensorProduct.map_tprod]
    congr 2
    funext u
    by_cases hu : u = ⟨v, hv⟩
    · subst hu
      simp only [Lw, φ₂, Function.update_self]
      exact (hL i).symm
    · have hu' : u.1 ≠ v := fun e => hu (Subtype.ext e)
      simp only [Lw, φ₂, Function.update_of_ne hu, Function.update_of_ne hu', LinearMap.id_apply]

end GlobalTheory.PolKerFin
end
end

open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePlace_unitaryPoint_keeps_zeroMatchedData : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, h) Φ) := by
  atlas_forward_decl GlobalTheory.PolKerFin.polZero_om_fin
end

section
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem RelV.exists_decomp_of_mem_algD {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
    ∃ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = M.vac v) ∧ Φ = ∑ i, pure (f i) (φ i) := by
  classical
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hx
    refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hSB, fun v hv => ?_⟩, ?_⟩
    · by_contra hc
      exact hv ((Set.Finite.mem_toFinset _).2 hc)
    · simp
  | zero => exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, m₁, f₁, φ₁, h₁, rfl⟩ := hx
    obtain ⟨T₂, m₂, f₂, φ₂, h₂, rfl⟩ := hy
    refine ⟨T₁ ∪ T₂, m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, fun k => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simp only [Fin.append_left]
        exact ⟨(h₁ i).1, (h₁ i).2.1, fun v hv => (h₁ i).2.2 v fun h => hv (Finset.mem_union_left _ h)⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ i).1, (h₂ i).2.1, fun v hv => (h₂ i).2.2 v fun h => hv (Finset.mem_union_right _ h)⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h, rfl⟩ := hx
    refine ⟨T, m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem c (h i).1, (h i).2.1, (h i).2.2⟩, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

theorem RelV.pure_neg {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure (-f) φ = -pure f φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.neg_apply, Pi.neg_apply, neg_mul]

theorem polZero_relV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (g, 1) Φ - Φ) := by
  classical
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v g hg Φ hΦ
  obtain ⟨T₀, m, f, φ, hφ, rfl⟩ := RelV.exists_decomp_of_mem_algD G.M Bs.ψ Bs.emb hΦ
  have hT := hM.triple
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := by
    intro u _
    show u • ((1 : Matrix _ _ _) - 1) = 0
    simp
  choose ψ hψ using fun i => GlobalTheory.ThK.LocalOps.acts_exists hP v (g, 1) hg h1W (φ i v) ((hφ i).2.1 v)
  have hpv : ∀ i, Rf.p v (ψ i) = Rf.p v (φ i v) := by
    intro i
    have hmem : ψ i - φ i v ∈ augAt om v :=
      Submodule.subset_span ⟨g, hg, φ i v, (hφ i).2.1 v, ψ i, (hψ i).1, (hψ i).2, rfl⟩
    have := hM.fin.inv v hmem
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  have hstd : ∀ i, ∀ᶠ w in Filter.cofinite, φ i w = Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 := by
    intro i
    have e0 : ∀ᶠ w in Filter.cofinite, φ i w = G.M.vac w :=
      Filter.eventually_cofinite.2 ((T₀.finite_toSet).subset fun w hw => by
        by_contra hc; exact hw ((hφ i).2.2 w hc))
    filter_upwards [e0, hT.geo.hM.std] with w e1 e2
    rw [e1, e2]
  set T : Finset (Pl F) := insert v (Xc.T ∪ T₀) with hTdef
  have hvT : ∀ w, w ∉ T → w ≠ v := fun w hw e => hw (e ▸ Finset.mem_insert_self _ _)
  have hT₀ : ∀ w, w ∉ T → w ∉ T₀ := fun w hw h =>
    hw (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
  refine ⟨T, fun w hw => Finset.mem_insert_of_mem (Finset.mem_union_left _ hw), m + m,
    Fin.append f fun i => -f i, Fin.append (fun i => Function.update (φ i) v (ψ i)) φ, fun k => ?_, ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left]
      refine ⟨(hφ i).1, fun w => ?_, fun w hw => ?_⟩
      · by_cases hw : w = v
        · subst hw; rw [Function.update_self]; exact (hψ i).1
        · rw [Function.update_of_ne hw]; exact (hφ i).2.1 w
      · rw [Function.update_of_ne (hvT w hw)]; exact (hφ i).2.2 w (hT₀ w hw)
    · simp only [Fin.append_right]
      exact ⟨neg_mem (hφ i).1, (hφ i).2.1, fun w hw => (hφ i).2.2 w (hT₀ w hw)⟩
  · rw [map_sum, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, RelV.pure_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact GlobalTheory.ThK.PolMatchStep.pure_update v (om (g, 1)) (f i) (φ i) (hφ i).2.1 (hstd i) (hψ i).2
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, map_neg, TensorProduct.neg_tmul, Finset.sum_neg_distrib]
    have e : ∀ i, (fun w : T => Rf.p w (Function.update (φ i) v (ψ i) w)) = fun w : T => Rf.p w (φ i w) := by
      intro i
      funext w
      obtain ⟨w, hw⟩ := w
      by_cases hwv : w = v
      · subst hwv
        simp only [Function.update_self]
        exact hpv i
      · simp only [Function.update_of_ne hwv]
    simp only [e, add_neg_cancel]

end GlobalTheory.PolKer

end
end

open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicData_unitaryRelations_finitePlace_polZero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (g, 1) Φ - Φ) := by
  atlas_forward_decl GlobalTheory.PolKer.polZero_relV
end

section
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem tprod_ne_zero_of_ne {κ : Type} [Fintype κ] {V : κ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {v : ∀ j, V j} (hv : ∀ j, v j ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose l hl using fun j => Module.Projective.exists_dual_eq_one ℂ (hv j)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap l)) h
  simp [hl] at this

theorem tmul_ne_zero_of_ne {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {x : P} {y : Q}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hy
  intro h0
  have := congrArg ((TensorProduct.rid ℂ P).toLinearMap ∘ₗ LinearMap.lTensor P l) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero, hl,
    one_smul] at this
  exact hx this

theorem pure_neg {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (-f) φ = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, neg_mul]

theorem exists_not_polZero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∃ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ¬ GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM
  classical
  haveI := hM.real.nontriv
  obtain ⟨y, hy⟩ := exists_ne (0 : R.Pi)
  obtain ⟨f, hfP, hfy⟩ : ∃ f ∈ G.M.Pol Bs.ψ Bs.emb, R.p f = y := by
    have : y ∈ (G.M.Pol Bs.ψ Bs.emb).map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    exact Submodule.mem_map.1 this
  have hloc : ∀ v, ∃ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Rf.p v φ ≠ 0 := fun v => by
    haveI := hM.fin.nontriv v
    obtain ⟨z, hz⟩ := exists_ne (0 : Rf.Pi v)
    have : z ∈ (GlobalTheory.WeilM.SB _).map (Rf.p v) := (hM.fin.onto v) ▸ Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 this
    exact ⟨φ, hφ, hz⟩
  choose ψ0 hψ0 hψ0ne using hloc
  have hvac := hM.triple.geo.hM.vac
  let φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := fun v => if v ∈ Xc.T then ψ0 v else G.M.vac v
  have hφSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _ := fun v => by
    by_cases h : v ∈ Xc.T
    · simp only [φ, h, if_true]; exact hψ0 v
    · simp only [φ, h, if_false]; exact (hvac v).1
  have hφout : ∀ v ∉ Xc.T, φ v = G.M.vac v := fun v h => by simp [φ, h]
  have hφne : ∀ v, Rf.p v (φ v) ≠ 0 := fun v => by
    by_cases h : v ∈ Xc.T
    · simp only [φ, h, if_true]; exact hψ0ne v
    · simp only [φ, h, if_false]; exact (hM.fin.sph v h).2
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ, ?_, ?_⟩
  · have := sum_pure_mem_algD G.M Bs.ψ Bs.emb Xc.T (m := 1) (fun _ => f) (fun _ => φ) (fun _ => ⟨hfP, hφSB, hφout⟩)
    simpa using this
  · rintro ⟨T, hT, m, f', φ', hf', hΦ, hsum⟩
    let g : Fin (m + 1) → SInf F (Fin a × Fin (a + a')) := Fin.cons (-f) f'
    let χ : Fin (m + 1) → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := Fin.cons φ φ'
    have h0 : ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (χ i) = 0 := by
      simp only [Fin.sum_univ_succ, g, χ, Fin.cons_zero, Fin.cons_succ, pure_neg, ← hΦ, neg_add_cancel]
    have hout : ∀ i, ∀ v ∉ T, χ i v = G.M.vac v := by
      intro i v hv
      induction i using Fin.cases with
      | zero => exact hφout v (fun h => hv (hT h))
      | succ j => exact (hf' j).2.2 v hv
    have key := GlobalTheory.T.tmul_sum_eq_zero_of_pureTensor_function_zero G.M.vac (fun v => (hvac v).2.1) hM.triple.geo.hM.std R.p Rf.Pi Rf.p T (m + 1) g χ hout h0
    simp only [Fin.sum_univ_succ, g, χ, Fin.cons_zero, Fin.cons_succ, map_neg, TensorProduct.neg_tmul, hsum, add_zero,
      neg_eq_zero] at key
    exact tmul_ne_zero_of_ne (hfy ▸ hy) (tprod_ne_zero_of_ne fun v : T => hφne v.1) key

end GlobalTheory.PolKer
end
end

open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicDatum_not_matched_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∃ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ¬ GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) := by
  atlas_forward_decl GlobalTheory.PolKer.exists_not_polZero
end

section
section
open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.PolKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

theorem polMatch_zero_iff_polZero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ Φ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0 ↔ GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM Φ
  constructor
  · rintro ⟨T, hX, m, m', f, φ, f', φ', h1, h1', hΦ, h0, he⟩
    refine ⟨T, hX, m, f, φ, h1, hΦ, ?_⟩
    rw [he]
    exact GlobalTheory.T.tmul_sum_eq_zero_of_pureTensor_function_zero G.M'.vac (fun v => (hM.triple.geo.hM'.vac v).2.1) hM.triple.geo.hM'.std R.p' Rf.Pi Rf.p' T m' f' φ'
      (fun j => (h1' j).2.2) h0.symm
  · rintro ⟨T, hX, m, f, φ, h1, hΦ, hz⟩
    refine ⟨T, hX, m, 0, f, φ, Fin.elim0, Fin.elim0, h1, fun j => j.elim0, hΦ, ?_, ?_⟩
    · simp
    · rw [hz]; simp

end GlobalTheory.PolKer
end

open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialMatch_zero_iff_pureTensor_image_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ Φ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0 ↔ GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) := by
  atlas_forward_decl GlobalTheory.PolKer.polMatch_zero_iff_polZero
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct

theorem GlobalTheory.PolKer.polMatch_zero_thetaSub : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∃ K, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) K ∧
      K ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb ∧
      ∀ ΦD ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, (ΦD ∈ K ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' _ R Rf hM
  have hiff := GlobalTheory.T.polynomialMatch_zero_iff_pureTensor_image_zero F E σ Bs a a' G Xc om om' R Rf hM
  obtain ⟨h00, hlin⟩ := GlobalTheory.PolMatchLin.polMatch_linear Bs G Xc om om' R Rf hM.fin
  let K : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) :=
    { carrier := {Φ | Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by
        simpa using hlin x y 0 0 1 hx.2 hy.2⟩
      zero_mem' := ⟨zero_mem _, h00⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, by
        simpa using hlin 0 x 0 0 c h00 hx.2⟩ }
  have memK : ∀ Φ, Φ ∈ K ↔ GlobalTheory.PolKer.PolZero Bs G Xc R Rf Φ := fun Φ =>
    ⟨fun h => (hiff Φ).1 h.2, fun h => ⟨GlobalTheory.PolKer.algD_of_polZero Bs G Xc R Rf Φ h, (hiff Φ).2 h⟩⟩
  have one_W : ∀ v, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v) := by
    intro v u _; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat]
  refine ⟨K, ⟨⟨fun Φ h => h.1, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro v h hh Φ hΦ
    exact (memK _).2 (GlobalTheory.T.finitePlace_unitaryPoint_keeps_zeroMatchedData F E σ Bs a a' G Xc om om' R Rf hM v h hh Φ ((memK Φ).1 hΦ))
  · intro k hk Φ hΦ
    exact (memK _).2 (GlobalTheory.T.matched_maps_orbit_sum hP F E σ Bs a a' G Xc om om' R Rf hM k hk Φ ((memK Φ).1 hΦ))
  · intro γ hγ Φ hΦ Φ₁ _ hd
    exact (memK _).2 (GlobalTheory.T.matched_maps_kernel_eq hP F E σ Bs a a' G Xc om om' R Rf hM γ hγ Φ Φ₁ ((memK Φ).1 hΦ) hd)
  · intro v g hg Φ hΦ
    exact (memK _).2 (GlobalTheory.T.algebraicData_unitaryRelations_finitePlace_polZero F E σ Bs a a' G Xc om om' R Rf hM v g hg Φ hΦ)
  · intro k hk Φ hΦ
    exact (memK _).2 (GlobalTheory.T.matched_maps_kernel_sum hP F E σ Bs a a' G Xc om om' R Rf hM k hk Φ hΦ)
  · intro γ hγ Φ hΦ Φ₁ _ hd
    exact (memK _).2 (GlobalTheory.T.matched_maps_kernel_integral hP F E σ Bs a a' G Xc om om' R Rf hM γ hγ Φ hΦ Φ₁ hd)
  · intro hK
    obtain ⟨Φ, hΦ, hn⟩ := GlobalTheory.T.exists_algebraicDatum_not_matched_zero F E σ Bs a a' G Xc om om' R Rf hM
    rw [← hK] at hΦ
    exact hn ((memK Φ).1 hΦ)
  · intro ΦD hΦD
    exact ⟨fun h => h.2, fun h => ⟨hΦD, h⟩⟩
end
