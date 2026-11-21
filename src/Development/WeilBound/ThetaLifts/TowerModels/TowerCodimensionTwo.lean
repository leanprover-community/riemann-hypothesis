import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration
import Development.WeilBound.ThetaLifts.TowerModels.LeviEx
import Development.WeilBound.ThetaLifts.TowerModels.PlaneMain
import Development.WeilBound.ThetaLifts.TowerModels.StabEx
import Development.WeilBound.ThetaLifts.TowerModels.ModelEx
import Development.WeilBound.ThetaLifts.TowerModels.DetHerm
import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardTraceAdelicAddCharLocalComponentNeOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem resEtaPow_of_add_two {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ : Eˣ →* Circle} {n : ℕ} (h : ResEtaPow K χ (n + 2)) : ResEtaPow K χ n := by
  intro a
  rw [h a]
  simp [pow_add]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) :
    ResEtaPow K (χ / χ') (n + m) := by
  intro a
  rw [MonoidHom.div_apply, Circle.coe_div, h a, h' a]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg, inv_one, ← pow_add]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem towerB_of (hP : PlaneEx) (hM : ModelEx) (hW : WeilEx) : TowerB := by
  intro F E _ _ _ _ _ σ B a b G X om om' hT hq
  have g := hT.geo
  have c := hT.chars
  have hb := g.aBig
  have hl := g.lt
  obtain ⟨Y', V₁, H, hY', hV₁, hH⟩ := hP.1 F E σ B hT.base (b + 2) b rfl (by omega) G.V' G.q (b + 2 - G.q)
    hq (by omega) g.hV' 0 (b + 1) (by omega) (by omega)
  obtain ⟨W', W₁, H', hW', hW₁, hH'⟩ := hP.2 F E σ B hT.base (a + (b + 2)) (a + b) (by omega) (by omega) G.W
    (a + (b + 2) - (G.p + G.q)) (G.p + G.q) (by omega) (by omega) g.hW a (a + b + 1) (by omega) (by omega)
  have hV0 : (reS G.V G.V).IsHerm σ B (a - G.p) G.p := g.hV
  obtain ⟨M₁, hM₁⟩ := hM F E σ B hT.base a (a + b) (reS G.V G.V) W₁ _ _ _ _ hV0 hW₁
  obtain ⟨M₁', hM₁'⟩ := hM F E σ B hT.base b (a + b) V₁ W₁ _ _ _ _ hV₁ hW₁
  have rα : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.α b := resEtaPow_of_add_two c.resα
  obtain ⟨om₁, hom₁⟩ := hW F E σ B hT.base a (a + b) (reS G.V G.V) W₁ _ _ _ _ hV0 hW₁ M₁ hM₁ X.β (X.β / X.α)
    c.heckeβ (isHecke_div c.heckeβ c.heckeα) c.resβ (resEtaPow_div c.resβ rα)
  obtain ⟨om₁', hom₁'⟩ := hW F E σ B hT.base b (a + b) V₁ W₁ _ _ _ _ hV₁ hW₁ M₁' hM₁' X.α (X.α / X.β)
    c.heckeα (isHecke_div c.heckeα c.heckeβ) rα (by rw [Nat.add_comm]; exact resEtaPow_div rα c.resβ)
  refine ⟨G.V, Y', W', ⟨hT.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV0, hY', hW', ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
      ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩, c, hT.weil, hT.weil'⟩,
    ⟨G.p, G.q - 1, reS G.V G.V, V₁, W₁, M₁, M₁'⟩, H, H', ⟨rfl, rfl, ?_, hH, hH'⟩, om₁, om₁', ⟨hT.base, ?_, ?_, hom₁, hom₁'⟩⟩
  · show G.q - 1 + 1 = G.q
    omega
  · have he := g.eBig
    refine ⟨by omega, ?_, fun w => ?_, ?_, ?_, hV0, ?_, ?_, hM₁, hM₁'⟩
    · obtain ⟨k, hk⟩ := g.even
      exact ⟨k - 1, by omega⟩
    · have := g.kappa w
      push_cast at this ⊢
      omega
    · show 2 * (G.p + (G.q - 1)) + 1 < (a - b) / 2
      omega
    · show 2 * (G.p + (G.q - 1)) + 1 < b
      omega
    · show V₁.IsHerm σ B (G.q - 1) (b - (G.q - 1))
      rw [show b - (G.q - 1) = b + 2 - G.q - 1 by omega]
      exact hV₁
    · show W₁.IsSkew σ B (a + b - (G.p + (G.q - 1))) (G.p + (G.q - 1))
      rw [show a + b - (G.p + (G.q - 1)) = a + (b + 2) - (G.p + G.q) - 1 by omega,
        show G.p + (G.q - 1) = G.p + G.q - 1 by omega]
      exact hW₁
  · exact ⟨c.heckeα, c.heckeβ, rα, c.resβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩

theorem towerA_of (hP : PlaneEx) (hM : ModelEx) (hW : WeilEx) : TowerA := by
  intro F E _ _ _ _ _ σ B b a' G X om om' hT hq0 hp
  have g := hT.geo
  have c := hT.chars
  have hb := g.aBig
  have hl := g.lt
  have he := g.eBig
  rw [hq0] at hb he
  obtain ⟨Y', V₁, H, hY', hV₁, hH⟩ := hP.1 F E σ B hT.base (b + 2) b rfl (by omega) G.V (b + 2 - G.p) G.p
    (by omega) hp g.hV 0 (b + 1) (by omega) (by omega)
  have hW0 := g.hW
  rw [hq0] at hW0
  obtain ⟨W', W₁, H', hW', hW₁, hH'⟩ := hP.2 F E σ B hT.base (b + 2 + a') (b + a') (by omega) (by omega) G.W
    (b + 2 + a' - (G.p + 0)) (G.p + 0) (by omega) (by omega) hW0 0 (b + 1) (by omega) (by omega)
  have hV0' : (reS G.V' G.V').IsHerm σ B 0 (a' - 0) := by
    have := g.hV'
    rw [hq0] at this
    exact this
  obtain ⟨M₁, hM₁⟩ := hM F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁
  obtain ⟨M₁', hM₁'⟩ := hM F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁
  have rβ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β b := resEtaPow_of_add_two c.resβ
  obtain ⟨om₁, hom₁⟩ := hW F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁ M₁ hM₁ X.β (X.β / X.α)
    c.heckeβ (isHecke_div c.heckeβ c.heckeα) rβ (resEtaPow_div rβ c.resα)
  obtain ⟨om₁', hom₁'⟩ := hW F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁ M₁' hM₁' X.α (X.α / X.β)
    c.heckeα (isHecke_div c.heckeα c.heckeβ) c.resα (by rw [Nat.add_comm]; exact resEtaPow_div c.resα rβ)
  refine ⟨Y', G.V', W', ⟨hT.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hY', g.hV',
      (by show (reS G.W W').IsSkew σ B (b + 2 + a' - (G.p + G.q)) (G.p + G.q); rw [hq0]; exact hW'),
      ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩, ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩,
      c, hT.weil, hT.weil'⟩,
    ⟨G.p - 1, 0, V₁, reS G.V' G.V', W₁, M₁, M₁'⟩, H, H', ⟨rfl, hq0, rfl, ?_, hH, hH'⟩, om₁, om₁', ⟨hT.base, ?_, ?_, hom₁, hom₁'⟩⟩
  · show G.p - 1 + 1 = G.p
    omega
  · refine ⟨?_, ?_, fun w => ?_, ?_, ?_, ?_, hV0', ?_, hM₁, hM₁'⟩
    · show a' < b
      omega
    · obtain ⟨k, hk⟩ := g.even
      exact ⟨k - 1, by omega⟩
    · have := g.kappa w
      push_cast at this ⊢
      omega
    · show 2 * (G.p - 1 + 0) + 1 < (b - a') / 2
      omega
    · show 2 * (G.p - 1 + 0) + 1 < a'
      omega
    · show V₁.IsHerm σ B (b - (G.p - 1)) (G.p - 1)
      rw [show b - (G.p - 1) = b + 2 - G.p - 1 by omega]
      exact hV₁
    · show W₁.IsSkew σ B (b + a' - (G.p - 1 + 0)) (G.p - 1 + 0)
      rw [show b + a' - (G.p - 1 + 0) = b + 2 + a' - (G.p + 0) - 1 by omega,
        show G.p - 1 + 0 = G.p + 0 - 1 by omega]
      exact hW₁
  · exact ⟨c.heckeα, c.heckeβ, c.resα, rβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩

theorem towerCodimensionTwo_of (hP : PlaneEx) (hM : ModelEx) (hW : WeilEx) : PositivityTheory.ThKEnd.TowerCodimensionTwo := by
  intro F E _ _ _ _ _ σ B b a' G X om om' hT hp
  have g := hT.geo
  have c := hT.chars
  have hb := g.aBig
  have hl := g.lt
  have he := g.eBig
  obtain ⟨Y', V₁, H, hY', hV₁, hH⟩ := hP.1 F E σ B hT.base (b + 2) b rfl (by omega) G.V (b + 2 - G.p) G.p
    (by omega) hp g.hV 0 (b + 1) (by omega) (by omega)
  obtain ⟨W', W₁, H', hW', hW₁, hH'⟩ := hP.2 F E σ B hT.base (b + 2 + a') (b + a') (by omega) (by omega) G.W
    (b + 2 + a' - (G.p + G.q)) (G.p + G.q) (by omega) (by omega) g.hW 0 (b + 1) (by omega) (by omega)
  have hV0' : (reS G.V' G.V').IsHerm σ B G.q (a' - G.q) := g.hV'
  obtain ⟨M₁, hM₁⟩ := hM F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁
  obtain ⟨M₁', hM₁'⟩ := hM F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁
  have rβ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β b := resEtaPow_of_add_two c.resβ
  obtain ⟨om₁, hom₁⟩ := hW F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁ M₁ hM₁ X.β (X.β / X.α)
    c.heckeβ (isHecke_div c.heckeβ c.heckeα) rβ (resEtaPow_div rβ c.resα)
  obtain ⟨om₁', hom₁'⟩ := hW F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁ M₁' hM₁' X.α (X.α / X.β)
    c.heckeα (isHecke_div c.heckeα c.heckeβ) c.resα (by rw [Nat.add_comm]; exact resEtaPow_div c.resα rβ)
  refine ⟨Y', G.V', W', ⟨hT.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hY', g.hV', hW',
      ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩, ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩,
      c, hT.weil, hT.weil'⟩,
    ⟨G.p - 1, G.q, V₁, reS G.V' G.V', W₁, M₁, M₁'⟩, H, H', ⟨rfl, rfl, ?_, hH, hH'⟩, om₁, om₁', ⟨hT.base, ?_, ?_, hom₁, hom₁'⟩⟩
  · show G.p - 1 + 1 = G.p
    omega
  · refine ⟨?_, ?_, fun w => ?_, ?_, ?_, ?_, hV0', ?_, hM₁, hM₁'⟩
    · show a' < b
      omega
    · obtain ⟨k, hk⟩ := g.even
      exact ⟨k - 1, by omega⟩
    · have := g.kappa w
      push_cast at this ⊢
      omega
    · show 2 * (G.p - 1 + G.q) + 1 < (b - a') / 2
      omega
    · show 2 * (G.p - 1 + G.q) + 1 < a'
      omega
    · show V₁.IsHerm σ B (b - (G.p - 1)) (G.p - 1)
      rw [show b - (G.p - 1) = b + 2 - G.p - 1 by omega]
      exact hV₁
    · show W₁.IsSkew σ B (b + a' - (G.p - 1 + G.q)) (G.p - 1 + G.q)
      rw [show b + a' - (G.p - 1 + G.q) = b + 2 + a' - (G.p + G.q) - 1 by omega,
        show G.p - 1 + G.q = G.p + G.q - 1 by omega]
      exact hW₁
  · exact ⟨c.heckeα, c.heckeβ, c.resα, rβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩

end PositivityTheory.ThKG.Tow

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem planeHerm : PlaneHerm := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  simp only [Pln.isHerm_iff] at hY ⊢
  exact Pln.exists_plane hB (Or.inl rfl) (by simp) (fun e => by simp) _ isIntegral_one
    (fun v => Pln.val_le_one_of_intE (B.τ v)) n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n

theorem planeSkew : PlaneSkew := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  simp only [Pln.isSkew_iff] at hY ⊢
  exact Pln.exists_plane hB (Or.inr rfl) (by simp) (fun e => by simp) _ Pln.one_mem_codE
    (fun v => Pln.val_le_one_of_codE hB.cm hB.std (hB.psiP v v.2) (B.τ v)) n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n

end PositivityTheory.ThKG.Tow

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def WeilPairExists : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ ψ : AddChar (AF F) ℂ, Continuous ψ → (∀ x : F, ψ (algebraMap F (AF F) x) = 1) → ψ ≠ 1 →
    ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E),
      (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 →
      ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d),
        (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
        ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
          ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
          ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d →
          ∃ om, IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JW) co χX χW om

end PositivityTheory.ThKG.Tow

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem weilEx_of (h : WeilPairExists) : WeilEx := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW M hM χX χW hχX hχW hrX hrW
  have hdX := det_herm hX
  have hdW := det_skew hW
  obtain ⟨hherm, -, -, -, -, -⟩ := hX
  obtain ⟨hskew, -, -, -, -, -⟩ := hW
  obtain ⟨hcm, -, -, hstd, -, -⟩ := hB
  obtain ⟨hrat, -, -, -, -⟩ := hM
  have hψ : B.ψ ≠ 1 := by
    intro h1
    apply Tw.PsiNontriv.psiV_ne_one B.ψ hstd B.v₁
    rw [GlobalTheory.VacAny.psiV, h1]
    ext x
    simp
  exact h F E σ hcm B.ψ hstd.1 hstd.2.1 hψ n d X.J W.J hherm hdX hskew hdW M.co hrat χX χW hχX hχW
    hrX hrW

end PositivityTheory.ThKG.Tow

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem planeEx : PlaneEx := ⟨planeHerm, planeSkew⟩

theorem pairEx (h : WeilPairExists) : PairEx := pairEx_of modelEx (weilEx_of h)

end PositivityTheory.ThKG.Tow

end
end
