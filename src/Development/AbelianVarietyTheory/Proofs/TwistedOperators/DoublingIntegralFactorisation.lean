import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzDatumEqOfThetaFunctionEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDatumLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchKapX
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchDer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingMeasureStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsTripleFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleGeometryUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsRealFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFiniteIdentityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPiLeAleph0

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem polMatch_onto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ algD G.M B.ψ B.emb, ∃ Φ' ∈ algD G.M' B.ψ B.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hM Φ hΦ
  classical
  obtain ⟨n, c, g, rfl⟩ := (Submodule.mem_span_set').1 hΦ
  choose f φ hf hφ hfin hg using fun i => (g i).2
  have hfin' : ∀ i, {v | ¬ φ i v = G.M.vac v}.Finite := fun i => Filter.eventually_cofinite.1 (hfin i)
  set T : Finset (Pl F) := X.T ∪ Finset.univ.biUnion (fun i => (hfin' i).toFinset) with hT
  have hout : ∀ i, ∀ v ∉ T, φ i v = G.M.vac v := by
    intro i v hv
    by_contra h
    exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (hfin' i).mem_toFinset.2 h⟩))
  have hreal : ∀ i, ∃ f' ∈ G.M'.Pol B.ψ B.emb, R.p' f' = R.p (c i • f i) := by
    intro i
    have : R.p (c i • f i) ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by rw [hM.real.quot'.onto]; trivial
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 this
    exact ⟨y, hy, e⟩
  choose f' hf' hf'eq using hreal
  have hloc : ∀ i v, ∃ y ∈ GlobalTheory.WeilM.SB _, Rf.p' v y = Rf.p v (φ i v) := by
    intro i v
    have : Rf.p v (φ i v) ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [hM.fin.onto' v]; trivial
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 this
    exact ⟨y, hy, e⟩
  choose φ₀ hφ₀ hφ₀eq using hloc
  let φ' : Fin n → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ :=
    fun i v => if v ∈ T then φ₀ i v else G.M'.vac v
  have hvac' : ∀ v, G.M'.vac v ∈ GlobalTheory.WeilM.SB _ := fun v => (hM.triple.geo.hM'.vac v).1
  have hφ'SB : ∀ i v, φ' i v ∈ GlobalTheory.WeilM.SB _ := by
    intro i v
    by_cases hv : v ∈ T
    · simp only [φ', if_pos hv]; exact hφ₀ i v
    · simp only [φ', if_neg hv]; exact hvac' v
  have hφ'out : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := by
    intro i v hv; simp only [φ', if_neg hv]
  have hpure : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c i • f i) (φ i) = c i • (g i : (Fin a × Fin (a + a') → AF F) → ℂ) := by
    intro i
    rw [hg i]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
  refine ⟨∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f' i) (φ' i), ?_, T, Finset.subset_union_left, n, n, fun i => c i • f i, φ, f', φ', ?_, ?_, ?_, rfl, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, φ' i, hf' i, hφ'SB i, ?_, rfl⟩
    exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hφ'out i v h))
  · exact fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hout i⟩
  · exact fun i => ⟨hf' i, hφ'SB i, hφ'out i⟩
  · exact Finset.sum_congr rfl fun i _ => (hpure i).symm
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf'eq i]
    congr 2
    funext v
    simp only [φ', if_pos v.2]
    exact (hφ₀eq i v).symm

end GlobalTheory.SquareAgree
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

namespace GlobalTheory.SquareAgree.PolMatchConst

def finProd {F : Type} [Field F] [NumberField F] {κ : Type} (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)

theorem match_of_polMatch : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' → Φ' ∈ G.M'.So B.ψ B.τ₁ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Match B G X R Rf Φ Φ' := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hT Φ Φ' hP hSo
  have hP0 := hP
  obtain ⟨T, hXT, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', _⟩ := hP
  have hstd : ∀ (κ : Type) (ψ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ),
      (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      (∀ v ∉ T, ψ v = vac v) →
      ∀ᶠ v in Filter.cofinite, ψ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    intro κ ψ vac hvac hψ
    filter_upwards [hvac, T.finite_toSet.compl_mem_cofinite] with v hv hvT
    rw [hψ v hvT, hv]
  have hg : ∀ i, finProd (φ i) ∈ GlobalTheory.WeilM.SB _ := fun i =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (φ i) (hf i).2.1 (hstd _ _ _ hT.geo.hM.std (hf i).2.2),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (φ i) (hf i).2.1 (hstd _ _ _ hT.geo.hM.std (hf i).2.2)⟩
  have hg' : ∀ j, finProd (φ' j) ∈ GlobalTheory.WeilM.SB _ := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (φ' j) (hf' j).2.1 (hstd _ _ _ hT.geo.hM'.std (hf' j).2.2),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (φ' j) (hf' j).2.1 (hstd _ _ _ hT.geo.hM'.std (hf' j).2.2)⟩
  have e : Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (finProd (φ i)) := hΦ
  have e' : Φ' = ∑ j, GlobalTheory.WeilM.pureA F (f' j) (finProd (φ' j)) := hΦ'
  refine ⟨hSo, m, m', fun i => finProd (φ i), f, fun _ => f, fun j => finProd (φ' j), f', fun _ => f',
    fun i => ⟨hg i, tendsto_const_nhds⟩, fun j => ⟨hg' j, tendsto_const_nhds⟩, e, e', fun _ => ?_⟩
  rw [← e, ← e']
  exact ⟨hSo, hP0⟩

end GlobalTheory.SquareAgree.PolMatchConst
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem eq_smul_of_stable_graph : ∀ (D : D7) (X : HSp D) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi), IsIrred X Pi rf rl → Module.rank ℂ Pi ≤ Cardinal.aleph0 → ∀ S : Submodule ℂ (Pi × Pi), (∀ g ∈ GfC X, ∀ x ∈ S, (rf g x.1, rf g x.2) ∈ S) → (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, (rl τ Y x.1, rl τ Y x.2) ∈ S) → (∀ x : Pi, ((x, 0) : Pi × Pi) ∈ S → x = 0) → (∀ y : Pi, ((0, y) : Pi × Pi) ∈ S → y = 0) → (∀ x : Pi, ∃ y : Pi, ((x, y) : Pi × Pi) ∈ S) → ∃ c : ℂ, c ≠ 0 ∧ ∀ x y : Pi, ((x, y) : Pi × Pi) ∈ S → y = c • x := by
  intro D X Pi rf rl hirr hrank S hf hl h1 h2 hon
  classical
  haveI : Nontrivial Pi := hirr.1
  choose t ht using hon
  have huniq : ∀ x y, ((x, y) : Pi × Pi) ∈ S → t x = y := by
    intro x y hxy
    have h0 : (((0 : Pi), t x - y) : Pi × Pi) ∈ S := by
      have := S.sub_mem (ht x) hxy
      simpa using this
    exact sub_eq_zero.1 (h2 _ h0)
  let T : Module.End ℂ Pi :=
    { toFun := t
      map_add' := fun a b => huniq _ _ (by simpa using S.add_mem (ht a) (ht b))
      map_smul' := fun r a => by
        simp only [RingHom.id_apply]
        exact huniq _ _ (by simpa using S.smul_mem r (ht a)) }
  have hTf : ∀ g ∈ GfC X, ∀ x, T (rf g x) = rf g (T x) := fun g hg x => huniq _ _ (hf g hg _ (ht x))
  have hTl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x, T (rl τ Y x) = rl τ Y (T x) := fun τ Y hY x => huniq _ _ (hl τ Y hY _ (ht x))
  obtain ⟨c, hc⟩ := GlobalTheory.LocGL.exists_not_isUnit_sub hrank T
  set A := T - algebraMap ℂ (Module.End ℂ Pi) c with hA
  have hAx : ∀ x, A x = T x - c • x := fun x => by simp [hA]
  have hAf : ∀ g ∈ GfC X, ∀ x, A (rf g x) = rf g (A x) := by
    intro g hg x; rw [hAx, hAx, hTf g hg, map_sub, map_smul]
  have hAl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x, A (rl τ Y x) = rl τ Y (A x) := by
    intro τ Y hY x; rw [hAx, hAx, hTl τ Y hY, map_sub, map_smul]
  have hA0 : A = 0 := by
    rcases hirr.2 (LinearMap.ker A)
        (fun g hg x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hAf g hg, hx, map_zero])
        (fun τ Y hY x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hAl τ Y hY, hx, map_zero]) with hk | hk
    · rcases hirr.2 (LinearMap.range A)
          (fun g hg x hx => by obtain ⟨z, rfl⟩ := hx; exact ⟨rf g z, hAf g hg z⟩)
          (fun τ Y hY x hx => by obtain ⟨z, rfl⟩ := hx; exact ⟨rl τ Y z, hAl τ Y hY z⟩) with hr | hr
      · exact LinearMap.range_eq_bot.1 hr
      · exact absurd ((Module.End.isUnit_iff _).2 ⟨LinearMap.ker_eq_bot.1 hk, LinearMap.range_eq_top.1 hr⟩) hc
    · exact LinearMap.ker_eq_top.1 hk
  have hTc : ∀ x, t x = c • x := fun x => by
    have := congrArg (fun f : Module.End ℂ Pi => f x) hA0
    simp only [hAx, LinearMap.zero_apply] at this
    exact sub_eq_zero.1 this
  refine ⟨c, ?_, fun x y hxy => by rw [← huniq x y hxy, hTc]⟩
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : Pi)
  exact hx (h1 x (by simpa [hTc] using ht x))

end GlobalTheory.SquareAgree
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

namespace GlobalTheory.SquareAgree

theorem matchKerP : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ ∈ algF ψ θ true A B, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → (p Φ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD 0) := by
  intro hU hR hM hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hRf Pi rf rl p p' hm
    Φ hΦ ΦD hΦD hD
  obtain ⟨K₁, g₁, ne₁, max₁, h₁⟩ := GlobalTheory.T.seesaw_unfolding_measure hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨K₂, g₂, ne₂, h₂⟩ := GlobalTheory.T.matched_maps_triple_factor hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf
  have hle : K₁ ≤ K₂ := fun x hx =>
    (h₂ x (g₁.1.1 hx)).2 (GlobalTheory.T.triple_geometry_unitary hU hR hM hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf K₁ g₁ ne₁ x hx)
  rcases max₁ K₂ g₂ hle with h | h
  · rw [← h₁ Φ hΦ ΦD hΦD hD, ← h, h₂ ΦD hΦD]
  · exact absurd h ne₂

theorem matchKerPPrime : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → (p' Φ₀ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ₀D) := by
  intro hU hR hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hM Pi rf rl p p' hm
    Φ₀ hΦ₀ Φ₀D hΦ₀D hD
  obtain ⟨K, hK, hKs, hKne⟩ := GlobalTheory.T.seesaw_unfolding_fundamental_domain hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨KD, hKD, hKDs, hKDne⟩ := GlobalTheory.T.matched_maps_finite_identity hP Bs Γ Xc om om' R Rf hM
  have h1 : K ≤ KD := fun Φ hΦ => (hKD Φ).2 ⟨hKs.le hΦ, GlobalTheory.T.matched_maps_real_finite hU hR hMi hP Bs Γ Xc om om' R Rf hM K hKs hKne Φ hΦ⟩
  have h2 : KD = K := (GlobalTheory.T.seesaw_unfolding_integrable hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm K KD hK hKDs h1).resolve_right hKDne
  constructor
  · intro h0
    have hm : Φ₀D ∈ K := (hK Φ₀D).2 ⟨hΦ₀D, Φ₀, hΦ₀, hD, h0⟩
    rw [← h2] at hm
    exact ((hKD _).1 hm).2
  · intro hpm
    have hm : Φ₀D ∈ KD := (hKD _).2 ⟨hΦ₀D, hpm⟩
    rw [h2] at hm
    obtain ⟨_, Φ₁, _, hD₁, h0⟩ := (hK _).1 hm
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact h0

theorem matchUpToScalar : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ Φ ∈ algF ψ θ true A B, ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ ΦD Φ₀D,
      IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M' ψ cB Φ₀D Φ₀ → Φ₀D ∈ Γ.M'.So Bs.ψ Bs.τ₁ → p Φ = p' Φ₀ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Match Bs Γ Xc R Rf ΦD (s • Φ₀D) := by
  intro hU hRe hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hTD.base.std
  have dA := GlobalTheory.SquareAgree.isDatum_linear Γ.M ψ hstd cA
  have dB := GlobalTheory.SquareAgree.isDatum_linear Γ.M' ψ hstd cB
  have lin := GlobalTheory.PolMatchLin.polMatch_linear Bs Γ Xc om om' R Rf hR.fin
  let G : Set (Pi × Pi) := {x | ∃ Φ ∈ algF ψ θ true A B, ∃ Φ₀ ∈ algF ψ θ false A₁ B, ∃ ΦD ∈ algD Γ.M Bs.ψ Bs.emb,
      ∃ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ ∧ IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD Φ₀D ∧ x = (p Φ, p' Φ₀)}
  have G0 : (0 : Pi × Pi) ∈ G :=
    ⟨0, zero_mem _, 0, zero_mem _, 0, zero_mem _, 0, zero_mem _, dA.1, dB.1, lin.1, Prod.ext (map_zero p).symm (map_zero p').symm⟩
  have Glin : ∀ x ∈ G, ∀ y ∈ G, ∀ c : ℂ, x + c • y ∈ G := by
    rintro _ ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩ _ ⟨Ψ, hΨ, Ψ₀, hΨ₀, ΨD, hΨD, Ψ₀D, hΨ₀D, k1, k2, k3, rfl⟩ c
    exact ⟨Φ + c • Ψ, add_mem hΦ (Submodule.smul_mem _ c hΨ), Φ₀ + c • Ψ₀, add_mem hΦ₀ (Submodule.smul_mem _ c hΨ₀),
      ΦD + c • ΨD, add_mem hΦD (Submodule.smul_mem _ c hΨD), Φ₀D + c • Ψ₀D, add_mem hΦ₀D (Submodule.smul_mem _ c hΨ₀D),
      dA.2 _ _ _ _ c h1 k1, dB.2 _ _ _ _ c h2 k2, lin.2 _ _ _ _ c h3 k3, by ext <;> simp⟩
  let S : Submodule ℂ (Pi × Pi) :=
    { carrier := G
      add_mem' := fun {x y} hx hy => by simpa using Glin x hx y hy 1
      zero_mem' := G0
      smul_mem' := fun c x hx => by simpa using Glin 0 G0 x hx c }
  have stf : ∀ g ∈ GfC X, ∀ x ∈ S, (rf g x.1, rf g x.2) ∈ S := by
    rintro g hg _ ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩
    have a1 := hM.mapA.stabX.1 g hg Φ hΦ
    have b1 := hM.mapB.stabX.1 g hg Φ₀ hΦ₀
    obtain ⟨ΨD, hΨD, hΨ⟩ := hO.algA _ a1
    obtain ⟨Ψ₀D, hΨ₀D, hΨ₀⟩ := hO.algB _ b1
    have e1 := GlobalTheory.ThetaInj.theta_inj Γ.M ψ hstd cA _ _ _ hΨ (hO.weilA ΦD Φ h1 1 g)
    have e2 := GlobalTheory.ThetaInj.theta_inj Γ.M' ψ hstd cB _ _ _ hΨ₀ (hO.weilB Φ₀D Φ₀ h2 1 g)
    refine ⟨_, a1, _, b1, ΨD, hΨD, Ψ₀D, hΨ₀D, hΨ, hΨ₀, ?_, ?_⟩
    · rw [e1, e2]
      exact GlobalTheory.SquareAgree.polMatch_kapX hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM g hg ΦD hΦD Φ₀D hΦ₀D h3
    · rw [hM.mapA.eqf g hg Φ hΦ, hM.mapB.eqf g hg Φ₀ hΦ₀]
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, (rl τ Y x.1, rl τ Y x.2) ∈ S := by
    rintro τ Y hY _ ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩
    obtain ⟨Φ', hΦ', hd⟩ := hM.mapA.stabX.2 τ Y hY Φ hΦ
    obtain ⟨Φ₀', hΦ₀', hd₀⟩ := hM.mapB.stabX.2 τ Y hY Φ₀ hΦ₀
    obtain ⟨ΨD, hΨD, hΨ⟩ := hO.algA _ hΦ'
    obtain ⟨Ψ₀D, hΨ₀D, hΨ₀⟩ := hO.algB _ hΦ₀'
    refine ⟨Φ', hΦ', Φ₀', hΦ₀', ΨD, hΨD, Ψ₀D, hΨ₀D, hΨ, hΨ₀,
      GlobalTheory.SquareAgree.LieEq.polMatch_der hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM τ Y hY Φ hΦ Φ' hΦ' Φ₀ hΦ₀ Φ₀' hΦ₀' hd hd₀ ΦD hΦD ΨD hΨD Φ₀D hΦ₀D Ψ₀D hΨ₀D h1 hΨ h2 hΨ₀ h3, ?_⟩
    rw [hM.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd, hM.mapB.eql τ Y hY Φ₀ hΦ₀ Φ₀' hΦ₀' hd₀]
  have k1 : ∀ x : Pi, ((x, 0) : Pi × Pi) ∈ S → x = 0 := by
    rintro x ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, hx⟩
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, h0⟩ := hx
    have m0 := (matchKerPPrime hU hRe hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ₀ hΦ₀ Φ₀D hΦ₀D h2).1 h0.symm
    have m1 := lin.2 _ _ _ _ (-1) h3 m0
    rw [smul_zero, add_zero, neg_one_smul, add_neg_cancel] at m1
    exact (matchKerP hU hRe hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ hΦ ΦD hΦD h1).2 m1
  have k2 : ∀ y : Pi, ((0, y) : Pi × Pi) ∈ S → y = 0 := by
    rintro y ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, hy⟩
    simp only [Prod.mk.injEq] at hy
    obtain ⟨h0, rfl⟩ := hy
    have m0 := (matchKerP hU hRe hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ hΦ ΦD hΦD h1).1 h0.symm
    have m1 := lin.2 _ _ _ _ (-1) h3 m0
    rw [smul_zero, add_zero, neg_one_smul, add_neg_cancel] at m1
    exact (matchKerPPrime hU hRe hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ₀ hΦ₀ Φ₀D hΦ₀D h2).2 m1
  have on : ∀ x : Pi, ∃ y : Pi, ((x, y) : Pi × Pi) ∈ S := by
    intro x
    have hx : x ∈ (algF ψ θ true A B).map p := hM.mapA.onto ▸ Submodule.mem_top
    obtain ⟨Φ, hΦ, rfl⟩ := hx
    obtain ⟨ΦD, hΦD, h1⟩ := hO.algA Φ hΦ
    obtain ⟨Φ₀D, hΦ₀D, h3⟩ := GlobalTheory.SquareAgree.polMatch_onto Bs Γ Xc om om' R Rf hR ΦD hΦD
    obtain ⟨Φ₀, hΦ₀, h2⟩ := hO.algB' Φ₀D hΦ₀D
    exact ⟨p' Φ₀, Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.SquareAgree.eq_smul_of_stable_graph D X Pi rf rl hM.irred (GlobalTheory.SquareAgree.rank_pi_le_aleph0 hU hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM) S stf stl k1 k2 on
  refine ⟨c, hc0, ?_⟩
  intro Φ hΦ Φ₀ hΦ₀ ΦD Φ₀D hD hD₀ hSo hp
  obtain ⟨ΦD', hΦD', h1⟩ := hO.algA Φ hΦ
  have hΦD : ΦD ∈ algD Γ.M Bs.ψ Bs.emb := (GlobalTheory.ThetaInj.theta_inj Γ.M ψ hstd cA _ _ _ hD h1) ▸ hΦD'
  obtain ⟨Φ₀D', hΦ₀D', h2⟩ := hO.algB Φ₀ hΦ₀
  have hΦ₀D : Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb := (GlobalTheory.ThetaInj.theta_inj Γ.M' ψ hstd cB _ _ _ hD₀ h2) ▸ hΦ₀D'
  obtain ⟨Φ₁D, hΦ₁D, m1⟩ := GlobalTheory.SquareAgree.polMatch_onto Bs Γ Xc om om' R Rf hR ΦD hΦD
  obtain ⟨Φ₁, hΦ₁, h4⟩ := hO.algB' Φ₁D hΦ₁D
  have hy := hc (p Φ) (p' Φ₁) ⟨Φ, hΦ, Φ₁, hΦ₁, ΦD, hΦD, Φ₁D, hΦ₁D, hD, h4, m1, rfl⟩
  have h5 := dB.2 _ _ _ _ (-c) h4 hD₀
  have hz : p' (Φ₁ + (-c) • Φ₀) = 0 := by rw [map_add, map_smul, hy, hp, neg_smul, add_neg_cancel]
  have m2 := (matchKerPPrime hU hRe hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM _ (add_mem hΦ₁ (Submodule.smul_mem _ _ hΦ₀)) _
    (add_mem hΦ₁D (Submodule.smul_mem _ _ hΦ₀D)) h5).1 hz
  have m3 := lin.2 _ _ _ _ (-1) m1 m2
  have e3 : Φ₁D + (-1 : ℂ) • (Φ₁D + (-c) • Φ₀D) = c • Φ₀D := by module
  rw [smul_zero, add_zero, e3] at m3
  exact GlobalTheory.SquareAgree.PolMatchConst.match_of_polMatch Bs Γ Xc om om' R Rf hTD _ _ m3 (Submodule.smul_mem _ c hSo)

end GlobalTheory.SquareAgree

end
end
