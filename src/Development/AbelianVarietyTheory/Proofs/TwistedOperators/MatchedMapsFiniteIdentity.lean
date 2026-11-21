import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsLocalIdentityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedFinprodPureTensorAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitIdentityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelProjectionFactorisationStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

open GlobalTheory.SmallThetaModules in

theorem exists_algD_not_polMatch_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∃ Φ ∈ GlobalTheory.SquareAgree.algD G.M' B.ψ B.emb, ¬ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf h
  classical
  let s : ∀ v, Rf.Pi v := fun v => Rf.p' v (G.M'.vac v)
  have hsph : ∀ v ∉ X.T, Rf.p v (G.M.vac v) = s v := fun v hv => (h.fin.sph v hv).1
  have hs0 : ∀ v ∉ X.T, s v ≠ 0 := fun v hv => by
    rw [← hsph v hv]; exact (h.fin.sph v hv).2
  have hXT : (X.T : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)).Finite := X.T.finite_toSet
  obtain ⟨q, hq⟩ := GlobalTheory.T.weil_model_projection_factorisation σ G.V G.W G.M B.ψ h.triple.geo.hM R.Pi R.p Rf.Pi Rf.p s
    (Filter.eventually_cofinite.2 (hXT.subset fun v hv => by by_contra hn; exact hv (hsph v hn)))
  obtain ⟨q', hq'⟩ := GlobalTheory.T.weil_model_projection_factorisation σ G.V' G.W G.M' B.ψ h.triple.geo.hM' R.Pi R.p' Rf.Pi Rf.p' s
    (Filter.Eventually.of_forall fun v => rfl)
  haveI := h.real.nontriv
  obtain ⟨x, hx⟩ := exists_ne (0 : R.Pi)
  have hx' : x ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by rw [h.real.quot'.onto]; trivial
  obtain ⟨f, hf, hfx⟩ := hx'
  have hloc : ∀ v, ∃ φv, φv ∈ GlobalTheory.WeilM.SB _ ∧ Rf.p' v φv ≠ 0 ∧ (v ∉ X.T → φv = G.M'.vac v) := by
    intro v
    by_cases hv : v ∈ X.T
    · haveI := h.fin.nontriv v
      obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
      have hy' : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [h.fin.onto' v]; trivial
      obtain ⟨φv, h1, h2⟩ := hy'
      exact ⟨φv, h1, h2 ▸ hy, fun hn => absurd hv hn⟩
    · exact ⟨G.M'.vac v, (h.triple.geo.hM'.vac v).1, hs0 v hv, fun _ => rfl⟩
  choose φ hφSB hφ0 hφvac using hloc
  have hφev : ∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v :=
    Filter.eventually_cofinite.2 (hXT.subset fun v hv => by by_contra hn; exact hv (hφvac v hn))
  have hΦ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ algD G.M' B.ψ B.emb :=
    Submodule.subset_span ⟨f, φ, hf, hφSB, hφev, rfl⟩
  obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  choose l hl using fun v => Module.Projective.exists_dual_eq_one ℂ (hφ0 v)
  have hls : ∀ v ∉ X.T, l v (s v) = 1 := fun v hv => by
    have := hl v
    rwa [hφvac v hv] at this
  have hadm : {v | l v (s v) ≠ 1}.Finite := hXT.subset fun v hv => by by_contra hn; exact hv (hls v hn)
  obtain ⟨Λ, hΛ⟩ := pureT_sep s (fun v => l v) hadm
  let LL : R.Pi ⊗[ℂ] RTens s →ₗ[ℂ] ℂ := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ l₀ Λ)
  have hLL : ∀ x y, LL (x ⊗ₜ y) = l₀ x * Λ y := fun x y => by simp [LL]
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ, hΦ, ?_⟩
  rintro ⟨T, hT, m, m', fs, φs, fs', φs', hfam, hfam', h0, hΦe, htens⟩
  let LT : (⨂[ℂ] v : T, Rf.Pi v) →ₗ[ℂ] ℂ := PiTensorProduct.dualDistrib (⨂ₜ[ℂ] v : T, l v)
  let Ltot : R.Pi ⊗[ℂ] (⨂[ℂ] v : T, Rf.Pi v) →ₗ[ℂ] ℂ := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ l₀ LT)
  have hLtot : ∀ x y, Ltot (x ⊗ₜ y) = l₀ x * LT y := fun x y => by simp [Ltot]
  have key : ∀ g : ∀ v, Rf.Pi v, (∀ v ∉ T, g v = s v) →
      Λ (pureT s g) = LT (PiTensorProduct.tprod ℂ fun v : T => g v) := by
    intro g hg
    have hr : Formalism.MainNotions.KudlaSiegelWeil.Restr s g := T.finite_toSet.subset fun v hv => by by_contra hn; exact hv (hg v hn)
    rw [hΛ g hr]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) (fun v hv => by
      by_contra hn
      exact hv (by show l v (g v) = 1; rw [hg v hn]; exact hls v fun h' => hn (hT h')))]
    simp only [LT, PiTensorProduct.dualDistrib_apply]
    exact (Finset.prod_coe_sort T fun v => l v (g v)).symm
  have hP : ∀ i, LL (q (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (fs i) (φs i))) =
      Ltot (R.p (fs i) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φs i v)) := by
    intro i
    have ev : ∀ᶠ v in Filter.cofinite, φs i v = G.M.vac v :=
      Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by by_contra hn; exact hv ((hfam i).2.2 v hn))
    rw [hq _ _ (hfam i).2.1 ev, hLL, hLtot]
    congr 1
    exact key _ fun v hv => by rw [(hfam i).2.2 v hv]; exact hsph v fun h' => hv (hT h')
  have hP' : ∀ j, LL (q' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (fs' j) (φs' j))) =
      Ltot (R.p' (fs' j) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φs' j v)) := by
    intro j
    have ev : ∀ᶠ v in Filter.cofinite, φs' j v = G.M'.vac v :=
      Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by by_contra hn; exact hv ((hfam' j).2.2 v hn))
    rw [hq' _ _ (hfam' j).2.1 ev, hLL, hLtot]
    congr 1
    exact key _ fun v hv => by rw [(hfam' j).2.2 v hv]
  have h1 : LL (q' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) = 1 := by
    rw [hq' _ _ hφSB hφev, hLL, hfx, hl₀, one_mul]
    have hr : Formalism.MainNotions.KudlaSiegelWeil.Restr s (fun v => Rf.p' v (φ v)) :=
      hXT.subset fun v hv => by by_contra hn; exact hv (congrArg (Rf.p' v) (hφvac v hn))
    rw [hΛ _ hr]
    exact finprod_eq_one_of_forall_eq_one fun v => hl v
  have h2 : LL (q' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) =
      Ltot (∑ j, R.p' (fs' j) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φs' j v)) := by
    rw [hΦe, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => hP' j
  have h3 : Ltot (∑ i, R.p (fs i) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φs i v)) = 0 := by
    rw [map_sum, ← Finset.sum_congr rfl fun i _ => hP i, ← map_sum, ← map_sum, ← h0, map_zero, map_zero]
  rw [htens, ← h2, h1] at h3
  exact one_ne_zero h3

end GlobalTheory.SquareAgree
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicDatum_not_matched_zero_by_localMaps : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∃ Φ ∈ GlobalTheory.SquareAgree.algD G.M' B.ψ B.emb, ¬ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 Φ := by
  atlas_forward_decl GlobalTheory.SquareAgree.exists_algD_not_polMatch_zero
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.KerDSub

open Filter GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

theorem polMatch_mem_algD (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') {Φ Φ'}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ') : Φ' ∈ algD G.M' B.ψ B.emb := by
  obtain ⟨T, -, m, m', f, φ, f', φ', -, hf', -, rfl, -⟩ := h
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, φ' j, (hf' j).1, (hf' j).2.1, ?_, rfl⟩
  exact Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => by
    by_contra h'
    exact hv ((hf' j).2.2 v h'))

theorem polMatch_zero_pure (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a')
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (hf : f ∈ G.M'.Pol B.ψ B.emb)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ SB _)
    (hv : ∀ᶠ v in cofinite, φ v = G.M'.vac v) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F))
    (hz : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), S ⊆ T →
      R.p' f ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ v)) = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  classical
  have hfin := Filter.eventually_cofinite.mp hv
  refine ⟨X.T ∪ S ∪ hfin.toFinset, fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx), 0, 1,
    Fin.elim0, Fin.elim0, fun _ => f, fun _ => φ, fun i => i.elim0, fun _ => ⟨hf, hφ, fun v hv' => ?_⟩, ?_, ?_, ?_⟩
  · by_contra h'
    exact hv' (Finset.mem_union_right _ (hfin.mem_toFinset.mpr h'))
  · simp
  · simp
  · rw [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_one, hz _ fun x hx =>
      Finset.mem_union_left _ (Finset.mem_union_right _ hx)]

theorem polMatch_kInf (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') (hMt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf)
    (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J) (hk : k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb) (Φ Φ')
    (hPM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ') :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf (om (1, k) Φ) (om' (1, k) Φ') := by
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a (a + a') G.V G.W G.M om _ _ hMt.triple.base hMt.triple.geo.hM hMt.triple.weil k hk
  obtain ⟨A', hA'⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a' (a + a') G.V' G.W G.M' om' _ _ hMt.triple.base hMt.triple.geo.hM'
    hMt.triple.weil' k hk
  have hpure : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (A f) φ := fun f φ h1 h2 =>
    hA f _ (GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz F _ φ h1 ((h2.and hMt.triple.geo.hM.std).mono fun v h => h.1.trans h.2) f)
  have hpure' : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      om' (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (A' f) φ := fun f φ h1 h2 =>
    hA' f _ (GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz F _ φ h1 ((h2.and hMt.triple.geo.hM'.std).mono fun v h => h.1.trans h.2) f)
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', rfl, rfl, heq⟩ := hPM
  have hR := hMt.real
  set P := G.M.Pol B.ψ B.emb with hP
  let pP : P →ₗ[ℂ] R.Pi := R.p ∘ₗ P.subtype
  have hsurj : Function.Surjective pP := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype]
    exact hR.quot.onto
  let g : P →ₗ[ℂ] R.Pi := R.p ∘ₗ A ∘ₗ P.subtype
  have hker : LinearMap.ker pP ≤ LinearMap.ker g := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have := hR.cpt k hk x.1 x.2 0 (zero_mem _) (A x.1) (A' 0) (hA x.1) (hA' 0)
      (by simpa [pP] using hx)
    simpa [g] using this
  let L : R.Pi →ₗ[ℂ] R.Pi :=
    (LinearMap.ker pP).liftQ g hker ∘ₗ (pP.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hL : ∀ x ∈ P, L (R.p x) = R.p (A x) := by
    intro x hx
    have e : (pP.quotKerEquivOfSurjective hsurj).symm (R.p x) = Submodule.Quotient.mk ⟨x, hx⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]
    rfl
  have hL' : ∀ x ∈ G.M'.Pol B.ψ B.emb, L (R.p' x) = R.p' (A' x) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (Submodule.eq_top_iff'.mp hR.quot.onto (R.p' x))
    rw [← hyx, hL y hy]
    exact hR.cpt k hk y hy x hx (A y) (A' x) (hA y) (hA' x) hyx
  have hcof : ∀ {κ : Type} (ψs vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ), (∀ v ∉ T, ψs v = vac v) →
      ∀ᶠ v in cofinite, ψs v = vac v := fun ψs vac h =>
    Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => by
      by_contra h'
      exact hv (h v h'))
  refine ⟨T, hT, m, m', fun i => A (f i), φ, fun j => A' (f' j), φ',
    fun i => ⟨GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B a (a + a') G.V G.W G.M om _ _ hMt.triple.base hMt.triple.geo.hM hMt.triple.weil k hk
      (f i) (hf i).1 (A (f i)) (hA (f i)), (hf i).2.1, (hf i).2.2⟩,
    fun j => ⟨GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B a' (a + a') G.V' G.W G.M' om' _ _ hMt.triple.base hMt.triple.geo.hM' hMt.triple.weil' k hk
      (f' j) (hf' j).1 (A' (f' j)) (hA' (f' j)), (hf' j).2.1, (hf' j).2.2⟩, ?_, ?_, ?_⟩
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hpure (f i) (φ i) (hf i).2.1 (hcof _ _ (hf i).2.2)
  · rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hpure' (f' j) (φ' j) (hf' j).2.1 (hcof _ _ (hf' j).2.2)
  · have := congrArg (LinearMap.rTensor _ L) heq
    simp only [map_sum, LinearMap.rTensor_tmul] at this
    simpa only [hL _ (hf _).1, hL' _ (hf' _).1] using this

theorem pure_sub {κ : Type} [Fintype κ] (f g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, sub_mul]

theorem kerD_isThetaSubG : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∃ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ),
      (∀ Φ, Φ ∈ N ↔ Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ) ∧
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N ∧ N ≠ algD Γ.M' Bs.ψ Bs.emb := by
  intro hP F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM
  obtain ⟨h0, hlin⟩ := GlobalTheory.PolMatchLin.polMatch_linear Bs Γ Xc om om' R Rf hM.fin
  let N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ) :=
    { carrier := {Φ | Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by simpa using hlin 0 0 x y 1 hx.2 hy.2⟩
      zero_mem' := ⟨zero_mem _, h0⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, by simpa using hlin 0 0 0 x c h0 hx.2⟩ }
  have hN : ∀ Φ, Φ ∈ N ↔ Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ := fun _ => Iff.rfl
  have hmem : ∀ Φ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ → Φ ∈ N := fun Φ h =>
    ⟨polMatch_mem_algD Bs Γ Xc R Rf h, h⟩
  have hpa : ∀ f φ, f ∈ Γ.M'.Pol Bs.ψ Bs.emb → (∀ w, φ w ∈ SB _) → (∀ᶠ w in cofinite, φ w = Γ.M'.vac w) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ algD Γ.M' Bs.ψ Bs.emb := fun f φ hf hφ hv =>
    Submodule.subset_span ⟨f, φ, hf, hφ, hv, rfl⟩
  obtain ⟨Φp, hΦp, hnot⟩ := GlobalTheory.T.exists_algebraicDatum_not_matched_zero_by_localMaps Bs Γ Xc om om' R Rf hM
  refine ⟨N, hN, ⟨fun Φ h => h.1, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun e => hnot ((hN Φp).mp (e ▸ hΦp)).2⟩
  ·
    intro v f φ hf hφ hv hφv
    have hz : Rf.p' v (φ v) = 0 := hM.fin.inv' v hφv
    refine hmem _ (polMatch_zero_pure Bs Γ Xc R Rf f hf φ hφ hv {v} fun T hT => ?_)
    rw [MultilinearMap.map_coord_zero _ (⟨v, hT (Finset.mem_singleton_self v)⟩ : T) hz, TensorProduct.tmul_zero]
  ·
    intro γ hγ f hf f₁ hf₁ hact φ hφ hv
    have hz : R.p' f₁ = 0 := hM.real.quot'.lie γ hγ f hf f₁ hact
    exact hmem _ (polMatch_zero_pure Bs Γ Xc R Rf f₁ hf₁ φ hφ hv ∅ fun T _ => by rw [hz, TensorProduct.zero_tmul])
  ·
    intro k hk f hf f₁ hf₁ hact φ hφ hv
    have hz : R.p' (f₁ - f) = 0 := by rw [map_sub, hM.real.quot'.cpt k hk f hf f₁ hact, sub_self]
    rw [← pure_sub]
    exact hmem _ (polMatch_zero_pure Bs Γ Xc R Rf (f₁ - f) (sub_mem hf₁ hf) φ hφ hv ∅ fun T _ => by
      rw [hz, TensorProduct.zero_tmul])
  ·
    classical
    intro v h hh Φ hΦ
    obtain ⟨T, hXT, hOn⟩ := (GlobalTheory.ThK.PolynomialMatching.polMatch_iff Bs Γ Xc R Rf 0 Φ).mp hΦ.2
    have hOn' : GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf (insert v T) 0 Φ := by
      by_cases hvT : v ∈ T
      · rwa [Finset.insert_eq_of_mem hvT]
      · exact GlobalTheory.ThK.PolynomialMatching.polMatchOn_insert F E σ Bs a a' Γ Xc R Rf v
          (hM.fin.sph v fun h' => hvT (hXT h')).1 T 0 Φ hOn
    have := GlobalTheory.T.matched_maps_local_identity hP F E σ Bs a a' Γ Xc om om' R Rf hM (insert v T) v (Finset.mem_insert_self v T) h hh 0 Φ hOn'
    rw [map_zero] at this
    exact hmem _ ((GlobalTheory.ThK.PolynomialMatching.polMatch_iff Bs Γ Xc R Rf 0 _).mpr
      ⟨insert v T, hXT.trans (Finset.subset_insert v T), this⟩)
  ·
    intro γ hγ Φ hΦ Φ₁ _ hd
    refine hmem _ (GlobalTheory.T.matched_maps_orbit_identity hP Bs Γ Xc om om' R Rf hM γ hγ 0 Φ hΦ.2 0 Φ₁ (fun x => ?_) hd)
    simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const 0 (0 : ℂ)
  ·
    intro k hk Φ hΦ
    have := polMatch_kInf Bs Γ Xc om om' R Rf hM k hk 0 Φ hΦ.2
    rw [map_zero] at this
    exact hmem _ this

end GlobalTheory.KerDSub
end
end
