import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsBeta
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Development.WeilBound.ThetaLifts.CartanFactorisation.ActsComp
import Development.WeilBound.ThetaLifts.CartanFactorisation.RinfZero
import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsMaximalCompactInfinite
import Development.WeilBound.ThetaLifts.LocalTheory.SplitInv

section
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

def upd {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x : (κ → Fv F v) → ℂ) : ∀ u : Pl F, (κ → Fv F u) → ℂ := by
  classical exact Function.update φ v x

theorem upd_self {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x) : upd φ v x v = x := by
  classical exact Function.update_self ..

theorem upd_ne {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x) {u} (h : u ≠ v) : upd φ v x u = φ u := by
  classical exact Function.update_of_ne h ..

theorem upd_eq {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) : upd φ v (φ v) = φ := by
  classical exact Function.update_eq_self ..

theorem upd_upd {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x y) : upd (upd φ v x) v y = upd φ v y := by
  classical exact Function.update_idem ..

theorem upd_sb {κ : Type} [Fintype κ] {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {v : Pl F} {x} (hx : x ∈ SB _) (u) :
    upd φ v x u ∈ SB _ := by
  by_cases e : u = v
  · subst e; rwa [upd_self]
  · rw [upd_ne _ _ _ e]; exact h u

theorem upd_cof {κ : Type} {φ ψ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = ψ u) (v : Pl F) (x) :
    ∀ᶠ u in cofinite, upd φ v x u = ψ u :=
  (h.and (Filter.eventually_cofinite_ne v)).mono fun _ hu => (upd_ne _ _ _ hu.2).trans hu.1

theorem intersection_update_fsHerm_neg_one (hP : PureAct) (hp : IsPair B M χX χW om r s r' s') (f : SInf F (Fin n × Fin d)) {φ} (h1 : ∀ u, φ u ∈ SB _)
    (h2 : ∀ᶠ u in cofinite, φ u = M.vac u) (v : Pl F) :
    ∃ j : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Fn F n d, (∀ x, j x = pure f (upd φ v x)) ∧
      ∀ S, ∀ x ∈ SB _, ∀ y, Acts (evFin F v) S x y → S (j x) = j y := by
  have h3 := (h2.and hp.good.std).mono fun _ h => h.1.trans h.2
  have l : ∀ x y (a : ℂ), pure f (upd φ v (x + a • y)) = pure f (upd φ v x) + a • pure f (upd φ v y) :=
    (hP F _ v id f φ h1 h3).2.1
  have z : pure f (upd φ v 0) = 0 := by
    have := l 0 0 1
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  refine ⟨{ toFun := fun x => pure f (upd φ v x)
            map_add' := fun x y => by simpa using l x y 1
            map_smul' := fun c x => by
              have := l 0 x c
              rwa [zero_add, z, zero_add] at this },
    fun _ => rfl, fun S x hx y hxy => ?_⟩
  have := (hP F _ v S f (upd φ v x) (upd_sb h1 hx) (upd_cof h3 v x)).2.2 y (by rwa [upd_self])
  exact this.trans (congrArg (pure f) (upd_upd φ v x y))


end PositivityTheory.ThKF

end
end

section
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem so_leK {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} (hM : M.IsGood B.ψ) : M.So B.ψ B.τ₁ ≤ schA F _ :=
  Submodule.span_le.2 (by
    rintro _ ⟨f, φ, h1, h2, -, rfl⟩
    obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hM φ h1 h2
    rw [e]
    exact PositivityTheory.ThKG.pureA_mem f hg)

theorem clsV (hW : WeilConv) (hC : ICont) (hS : SqInt) (t : IsTriple B G X om om') : Cls B G.M om (schA F _) :=
  have p := PositivityTheory.ThKG.pairV t
  have w := hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p (PositivityTheory.ThKG.weilCondV t)
  ⟨le_rfl, fun Φ h => (w.1 Φ h).1, (hC F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).1 (PositivityTheory.ThKG.weilCondV t), fun ψ hψ _ => w.2 ψ hψ,
    fun μ 𝓕 h1 h2 Φ _ h => (hS F E σ B a a' G X om om' t μ 𝓕 h1 h2).1 Φ h⟩

theorem clsV' (hD : KDecay) (hK : KCoinv) (hc : SoCont) (hC : ICont) (hS : SqInt) (m : IsMatched B G X om om' R Rf) :
    Cls B G.M' om' (G.M'.So B.ψ B.τ₁) := by
  have p := PositivityTheory.ThKG.pairV' m.triple
  refine ⟨so_leK p.good, fun Φ h => ((hD F E σ B a a' G X om om' m.triple).2 Φ h).2.1,
    (hC F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).2 (hK F E σ B a a' G X om om' R Rf m).2, fun ψ hψ hf h => ?_,
    fun μ 𝓕 h1 h2 Φ h' h => (hS F E σ B a a' G X om om' m.triple μ 𝓕 h1 h2).2 Φ ⟨h, h'⟩⟩
  refine SeqContinuous.continuous fun u f hu => ?_
  have := hc F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p 1 (fun _ => ψ) (fun _ => f) (fun k _ => u k) (fun _ => ⟨hψ, hu⟩)
    (fun k => by simpa using hf (u k)) (by simpa using hf f) h
  simp only [Finset.univ_unique, Finset.sum_singleton] at this
  exact this

theorem pure_soK (m : IsTriple B G X om om') (f : SInf F _) {φ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = G.M'.vac u)
    {x} (hx : x ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁)) : pure f (upd φ B.v₁ x) ∈ G.M'.So B.ψ B.τ₁ := by
  obtain ⟨j, hj, -⟩ := intersection_update_fsHerm_neg_one pureAct (PositivityTheory.ThKG.pairV' m) f h1 h2 B.v₁
  rw [← hj]
  refine (Submodule.span_le (p := (G.M'.So B.ψ B.τ₁).comap j)).2 (fun y hy => ?_) hx
  show j y ∈ G.M'.So B.ψ B.τ₁
  rw [hj]
  exact Submodule.subset_span ⟨f, _, upd_sb h1 hy.1, upd_cof h2 _ _, by rwa [upd_self], rfl⟩

theorem kills0_of (hT : ThetaBasic) (hW : WeilConv) (hK : KCoinv) (h : Kills) : PositivityTheory.ThKG.Loc.Kills0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf m q0 f hf φ h1 h2 h3
  have p2 := PositivityTheory.ThKG.pairV' m.triple
  have cv := fun Φ hΦ => ((hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p2 (Or.inr (by simp [q0]))).1 Φ hΦ).1
  obtain ⟨-, k2, k3, -⟩ := (hK F E σ B a a' G X om om' R Rf m).1 _ m.triple.chars.good
  obtain ⟨x, hx, e⟩ := k3 B.τ₁ (Rf.p' _ (φ B.v₁))
  have ha : φ B.v₁ - x ∈ augAt om' B.v₁ := (k2 _ (sub_mem (h1 _) hx.1)).1 (by rw [map_sub, e, sub_self])
  obtain ⟨j, hj, hjS⟩ := intersection_update_fsHerm_neg_one pureAct p2 f h1 h2 B.v₁
  have js : ∀ y ∈ SB _, j y ∈ schA F _ := fun y hy => by
    obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA p2.good _ (upd_sb h1 hy) (upd_cof h2 B.v₁ y)
    rw [hj, e]
    exact PositivityTheory.ThKG.pureA_mem f hg
  have add : ∀ y ∈ SB _, ∀ z ∈ SB _, G.M'.I om' (j (y + z)) = G.M'.I om' (j y) + G.M'.I om' (j z) := fun y hy z hz =>
    funext fun g => by rw [map_add]; exact PositivityTheory.ThKG.I_add p2.weil cv (js y hy) (js z hz) g
  have key : ∀ z ∈ augAt om' B.v₁, G.M'.I om' (j z) = 0 := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨g, hg, x, hx, y, hy, hxy, rfl⟩ := h
      have e2 := add _ (sub_mem hy hx) _ hx
      rw [sub_add_cancel, ← hjS _ x hx y hxy, I_left unimodularity_holds hT p2 (js x hx)] at e2
      exact left_eq_add.1 (e2.trans (add_comm _ _))
    | zero => rw [map_zero]; exact PositivityTheory.ThKG.I_zero _ _
    | add a b ha hb iha ihb => rw [add a (augAt_le _ ha) b (augAt_le _ hb), iha, ihb, add_zero]
    | smul c a _ iha => funext h; rw [map_smul, PositivityTheory.ThKG.I_smul, iha]; simp
  have e3 := add _ (augAt_le _ ha) x hx.1
  rw [sub_add_cancel, key _ ha, zero_add, hj, hj, upd_eq] at e3
  rw [e3]
  refine (h F E σ B a a' G X om om' R Rf m).2 f hf _ (upd_sb h1 hx.1) (upd_cof h2 _ _)
    (by rw [upd_self]; exact Submodule.subset_span hx) (h3.imp id fun ⟨v, hv⟩ => ⟨v, ?_⟩)
  by_cases ev : v = B.v₁
  · subst ev; rw [upd_self, e, hv]
  · rwa [upd_ne _ _ _ ev]

end PositivityTheory.ThKF

end
end
