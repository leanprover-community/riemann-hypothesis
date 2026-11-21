import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapSquareSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareBaseIntersection
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsPenFrame
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorElementaryColumnOp
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsBlockMapInitialVertex
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagDiv
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrdOne
import Development.WeilBound.CoreStatements.PluriharmonicCharts.PullDegSome
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleFibre
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MapAevalInt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsMultiHomogIdealMap
import Development.WeilBound.CoreStatements.PluriharmonicCharts.BlockFnFieldCompLe
import Development.WeilBound.CoreStatements.PluriharmonicCharts.LognormOrbit

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_swap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → ∃ (k₀ : K) (ca cb : Fin N), M.blk (τ, a) = some k₀ ∧ (ca : ℕ) = lastCol N j a ∧ (cb : ℕ) = ca + 1 ∧ ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) ∧ (∑ p, xiCoef τ a p * M.dy p k₀) = -2 ∧ ∀ p, p ≠ (τ, a) → M.dy p k₀ = 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b hab hcase
  have hjN := M.j_le
  have hbN := b.isLt
  have ha1 : (a : ℕ) + 1 ≠ j := by omega
  have ha2 : (a : ℕ) + 1 ≠ N := by omega
  have hprop : IsProperStep N j a := ⟨ha1, ha2⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, M.blk (τ, a) = some k₀ := by
    cases h : M.blk (τ, a) with
    | none => exact ((M.blk_none (τ, a)).1 h hprop).elim
    | some k => exact ⟨k, rfl⟩
  have hdy : ∀ p, M.dy p k₀ = if p = (τ, a) then 1 else 0 := by
    intro p
    unfold FlagModel.dy
    have hnot : ¬ ∀ p' : Ψ × Fin N, M.blk p' ≠ some k₀ := fun h => h (τ, a) hk₀
    rw [dif_neg hnot]
    by_cases hp : p = (τ, a)
    · subst hp
      simp [hk₀]
    · rw [if_neg hp, if_neg]
      intro h
      exact hp (M.blk_inj p (τ, a) k₀ h hk₀)
  have hlast : lastCol N j a < N ∧ lastCol N j a + 1 < N ∧
      (lastCol N j a < N - j ↔ lastCol N j a + 1 < N - j) := by
    unfold lastCol
    split_ifs with h <;> omega
  refine ⟨k₀, ⟨lastCol N j a, hlast.1⟩, ⟨lastCol N j a + 1, hlast.2.1⟩, hk₀, rfl, rfl, hlast.2.2, ?_, ?_⟩
  · simp only [hdy, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [xiCoef]
  · intro p hp
    rw [hdy p, if_neg hp]
end

section
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

local instance (priority := 2000) intAlg5 {Φ : Type} [Field Φ] : Algebra ℤ (RatFunc Φ) := Ring.toIntAlgebra _

open GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]

open GroundTheory.Heights₂.Heights.Inter

theorem div_eq_of_local {P Δ : Ideal (MRing ι)} (hPp : P.IsPrime) (hΔp : Δ.IsPrime) (hrel : IsRelevant Δ)
    (hPΔ : P ≤ Δ) {g h : MRing ι} (hgP : g ∉ P) (hhΔ : h ∉ Δ) (hgΔ : g ∈ Δ)
    (hsat : ∀ d ∈ Δ, ∃ u ∉ Δ, u * d ∈ P ⊔ Ideal.span {g})
    (key : ∀ W : Ideal (MRing ι), W.IsPrime → IsRelevant W → P ≤ W → ¬ Δ ≤ W →
      ∃ u v, u ∉ W ∧ v ∉ W ∧ u * g - v * h ∈ P) :
    divCycle P g = divCycle P h + Finsupp.single Δ 1 := by
  have hP : h ∉ P := fun hh => hhΔ (hPΔ hh)
  have hone : multAt (P ⊔ Ideal.span {g}) Δ = 1 := by
    unfold multAt
    rw [dif_pos hΔp, DiagonalOrderOne.length_eq_one_of_sat _ Δ
      (sup_le hPΔ ((Ideal.span_singleton_le_iff_mem _).2 hgΔ)) hsat]
    rfl
  have hJΔ : P ⊔ Ideal.span {g * h} ≤ Δ :=
    sup_le hPΔ ((Ideal.span_singleton_le_iff_mem _).mpr (Δ.mul_mem_right h hgΔ))
  have hΔ : Δ ∈ divSupp P (g * h) := by
    refine ⟨⟨⟨hΔp, hJΔ⟩, fun Q hQ hQΔ => ?_⟩, hrel⟩
    by_contra hΔQ
    have hPQ : P ≤ Q := le_sup_left.trans hQ.2
    obtain ⟨u, v, huQ, hvQ, hm⟩ :=
      key Q hQ.1 (fun k => (hrel k).imp fun _ hi hq' => hi (hQΔ hq')) hPQ hΔQ
    have hhQ : h ∉ Q := fun hh' => hhΔ (hQΔ hh')
    have hgQ : g ∈ Q :=
      (hQ.1.mem_or_mem (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))).resolve_right hhQ
    have hvh : v * h ∈ Q := by
      have e : v * h = u * g - (u * g - v * h) := by ring
      rw [e]
      exact Q.sub_mem (Q.mul_mem_left u hgQ) (hPQ hm)
    rcases hQ.1.mem_or_mem hvh with h1 | h1
    exacts [hvQ h1, hhQ h1]
  ext W
  have hcg := DiagonalDivisor.divCycle_eq_ite (s := g) hP W
  have hch := DiagonalDivisor.divCycle_eq_ite (s := h) hgP W
  rw [mul_comm h g] at hch
  rw [Finsupp.add_apply, hcg, hch, Finsupp.single_apply]
  by_cases hW : W ∈ divSupp P (g * h)
  · rw [if_pos hW, if_pos hW]
    have hWp : W.IsPrime := hW.1.1.1
    by_cases hWΔ : Δ = W
    · rw [if_pos hWΔ, ← hWΔ, hone, DiagonalOrder.multAt_eq_zero_of_not_le hΔp
        (fun hle => hhΔ (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))))]
    · rw [if_neg hWΔ, add_zero]
      have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
      have hΔW : ¬ Δ ≤ W := fun hle => hWΔ (le_antisymm hle (hW.1.2 ⟨hΔp, hJΔ⟩ hle))
      obtain ⟨u, v, hu, hv, hm⟩ := key W hWp hW.2 hPW hΔW
      exact DiagonalOrder.multAt_sup_span_eq hWp hPW hu hv hm
  · rw [if_neg hW, if_neg hW, if_neg (fun h' : Δ = W => hW (h' ▸ hΔ)), add_zero]

theorem exists_point (W : Ideal (MRing ι)) (hW : W.IsPrime) :
    ∃ (E : Type) (_ : Field E) (z : (Σ k, ι k) → E), ∀ f : MRing ι, aeval z f = 0 ↔ f ∈ W := by
  have gen : ∀ (E : Type) [Field E] (ρ : MRing ι →+* E) (f : MRing ι), aeval (fun q => ρ (X q)) f = ρ f := by
    intro E _ ρ f
    have e : (aeval (fun q => ρ (X q)) : MRing ι →ₐ[ℤ] E).toRingHom = ρ :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun p => by simp
    exact RingHom.congr_fun e f
  let E := FractionRing (MRing ι ⧸ W)
  let ρ : MRing ι →+* E := (algebraMap (MRing ι ⧸ W) E).comp (Ideal.Quotient.mk W)
  refine ⟨E, inferInstance, fun q => ρ (X q), fun f => ?_⟩
  rw [gen E ρ f]
  exact (map_eq_zero_iff (algebraMap (MRing ι ⧸ W) E) (IsFractionRing.injective _ _)).trans
    Ideal.Quotient.eq_zero_iff_mem

def monoX (c : ∀ k, ι k) (d : K → ℕ) : MRing ι := ∏ k, X ⟨k, c k⟩ ^ d k

theorem isMultiHomog_monoX (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (monoX c d) d := by
  rw [← Bridge.isMultiHomog_iff]
  have := IsWeightedHomogeneous.prod (w := NumbersDVR.blockWeight ι) Finset.univ
    (fun k => (X ⟨k, c k⟩ : MRing ι) ^ d k) (fun k => d k • NumbersDVR.blockWeight ι ⟨k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X ℤ _ _).pow (d k))
  have e : ∑ k, d k • NumbersDVR.blockWeight ι ⟨k, c k⟩ = d := by
    funext k
    simp [NumbersDVR.blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [e] at this
  exact this

theorem aeval_monoX (z : (Σ k, ι k) → L) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval z (monoX c d) = ∏ k, z ⟨k, c k⟩ ^ d k := by
  simp [monoX]

theorem aeval_monoX_ne {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    aeval z (monoX c d) ≠ 0 := by
  rw [aeval_monoX]
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)

theorem chartMono_mul {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) {dg dh : K → ℕ} {e : K → ℤ}
    (he : ∀ k, (dg k : ℤ) - dh k = e k) : chartMono z c e * aeval z (monoX c dh) = aeval z (monoX c dg) := by
  rw [aeval_monoX, aeval_monoX, chartMono, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← he, ← zpow_natCast, ← zpow_add₀ (hc k), sub_add_cancel, zpow_natCast]

theorem chartMono_ne {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (e : K → ℤ) :
    chartMono z c e ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)

theorem exists_rel {w : (Σ k, ι k) → Φ} {z : (Σ k, ι k) → L} (hz : IsPt w z) {c : ∀ k, ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) {σ : Φ} {e : K → ℤ} {v : L} (hv : HasVal w z (σ / chartMono w c e) v)
    {g h : MRing ι} {dg dh : K → ℕ} (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh)
    (he : ∀ k, (dg k : ℤ) - dh k = e k) (hq : aeval w g = σ * aeval w h) :
    ∃ u u' : MRing ι, aeval z u ≠ 0 ∧ aeval z u' = v * chartMono z c e * aeval z u ∧
      u * g - u' * h ∈ mCoordIdeal w := by
  have hcw : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => hz.coord_ne (hc k)
  obtain ⟨d, n, m, hn, hm, h0, e1, e2⟩ := hv
  refine ⟨m * monoX c dh, n * monoX c dg, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero h0 (aeval_monoX_ne hc _)
  · rw [map_mul, map_mul, e2, ← chartMono_mul hc he]; ring
  · have hd : IsMultiHomog (m * monoX c dh * g - n * monoX c dg * h) (d + dh + dg) := by
      refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hm (isMultiHomog_monoX _ _)) hg) ?_
      rw [add_right_comm]
      exact isMultiHomog_mul (isMultiHomog_mul hn (isMultiHomog_monoX _ _)) hh
    rw [mem_iff_of_homog hd]
    simp only [map_sub, map_mul, e1, hq, ← chartMono_mul hcw he]
    have := chartMono_ne hcw e
    field_simp
    ring

theorem congr_aeval {σ : Type} (O : Subring Φ) (a b : σ → Φ) (V : Φ) (ha : ∀ q, a q ∈ O) (hb : ∀ q, b q ∈ O)
    (hab : ∀ q, ∃ ρ ∈ O, a q - b q = ρ * V) (f : MvPolynomial σ ℤ) :
    aeval a f ∈ O ∧ ∃ ρ ∈ O, aeval a f - aeval b f = ρ * V := by
  induction f using MvPolynomial.induction_on with
  | C n => exact ⟨by simp, 0, zero_mem _, by simp⟩
  | add f g hf hg =>
    obtain ⟨h1, ρ, h2, h3⟩ := hf
    obtain ⟨h1', ρ', h2', h3'⟩ := hg
    exact ⟨by rw [map_add]; exact add_mem h1 h1', ρ + ρ', add_mem h2 h2', by
      rw [map_add, map_add]; linear_combination h3 + h3'⟩
  | mul_X f q hf =>
    obtain ⟨h1, ρ, h2, h3⟩ := hf
    obtain ⟨ρ', h2', h3'⟩ := hab q
    refine ⟨by rw [map_mul, aeval_X]; exact mul_mem h1 (ha q), aeval a f * ρ' + ρ * b q,
      add_mem (mul_mem h1 h2') (mul_mem h2 (hb q)), ?_⟩
    rw [map_mul, map_mul, aeval_X, aeval_X]
    linear_combination (aeval a f) * h3' + b q * h3

variable {y : (Σ k, ι k) → Φ} {k₀ : K} {B : ι k₀ → Φ} {cf : Φ} {e : K → ℤ}

def totDeg (k₀ : K) (e : K → ℤ) : Option K → ℤ := fun o => o.elim 1 fun k => e k + if k = k₀ then 1 else 0

namespace PenFrame

variable {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e z c)

theorem αA : ∑ m, Fr.α m * y ⟨k₀, m⟩ = Fr.ε⁻¹ := by
  have h := Fr.αp
  simp only [Fr.p_eq, mul_left_comm _ Fr.ε, ← Finset.mul_sum] at h
  exact eq_inv_of_mul_eq_one_right h

theorem βA : ∑ m, Fr.β m * y ⟨k₀, m⟩ = 0 := by
  have h := Fr.βp
  simp only [Fr.p_eq, mul_left_comm _ Fr.ε, ← Finset.mul_sum] at h
  exact (mul_eq_zero.1 h).resolve_left Fr.ε_ne

theorem αB : ∑ m, Fr.α m * B m = -(Fr.δ * Fr.ε⁻¹ * Fr.γ⁻¹) := by
  have h := Fr.αr
  simp only [Fr.r_eq, mul_add, Finset.sum_add_distrib, mul_left_comm _ Fr.γ, mul_left_comm _ Fr.δ, ← Finset.mul_sum,
    Fr.αA] at h
  have := Fr.γ_ne
  have h' : ∑ m, Fr.α m * B m = Fr.γ⁻¹ * (Fr.γ * ∑ m, Fr.α m * B m) := by rw [inv_mul_cancel_left₀ this]
  rw [h', eq_neg_of_add_eq_zero_left h]; ring

theorem βB : ∑ m, Fr.β m * B m = Fr.γ⁻¹ := by
  have h := Fr.βr
  simp only [Fr.r_eq, mul_add, Finset.sum_add_distrib, mul_left_comm _ Fr.γ, mul_left_comm _ Fr.δ, ← Finset.mul_sum,
    Fr.βA, mul_zero, add_zero] at h
  exact eq_inv_of_mul_eq_one_right h

end PenFrame

theorem pen_lin (μ : ι k₀ → Φ) (A : ι k₀ → Φ) (t : RatFunc Φ) :
    ∑ m, algebraMap Φ (RatFunc Φ) (μ m) * penCo y k₀ A B t ⟨none, m⟩ =
      algebraMap Φ (RatFunc Φ) (∑ m, μ m * A m) + t * algebraMap Φ (RatFunc Φ) (∑ m, μ m * B m) := by
  simp only [penCo, mul_add, Finset.sum_add_distrib, mul_left_comm _ t, ← Finset.mul_sum, ← map_mul, ← map_sum]

theorem local_data {z : (Σ o : Option K, ι (o.getD k₀)) → L}
    (hz : IsPt (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) z) {c : ∀ o, iW ι k₀ o} (hc : ∀ o, z ⟨o, c o⟩ ≠ 0)
    (Fr : PenFrame y k₀ B cf e (z ∘ v₀ k₀) fun k => c (some k)) :
    ∃ (η U V : RatFunc Φ) (Uv : L),
      HasVal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) z η
        (Fr.sv * ∑ m, Fr.αv m * (z ⟨some k₀, m⟩ / z ⟨some k₀, c (some k₀)⟩)) ∧
      (∀ m, z ⟨some k₀, m⟩ / z ⟨some k₀, c (some k₀)⟩ =
        Fr.pv m * ∑ m, Fr.αv m * (z ⟨some k₀, m⟩ / z ⟨some k₀, c (some k₀)⟩)) ∧
      HasVal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) z U Uv ∧
      HasVal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) z V (∑ m, Fr.βv m * (z ⟨none, m⟩ / z ⟨none, c none⟩)) ∧
      (∀ m, penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X ⟨none, m⟩ /
          penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X ⟨none, c none⟩ =
        algebraMap Φ (RatFunc Φ) (Fr.p m) * U + algebraMap Φ (RatFunc Φ) (Fr.r m) * V) ∧
      RatFunc.X * algebraMap Φ (RatFunc Φ) cf /
        chartMono (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) c (totDeg k₀ e) = η * V := by
  set w := penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X with hw
  let φ := algebraMap Φ (RatFunc Φ)
  have hz0 : IsPt y (z ∘ v₀ k₀) := hz.comp (isBlockMap_initial_vertex k₀) φ rfl
  have pull : ∀ {s v}, HasVal y (z ∘ v₀ k₀) s v → HasVal w z (φ s) v := fun h => h.pull (isBlockMap_initial_vertex k₀) φ rfl
  have hcy : ∀ k, y ⟨k, c (some k)⟩ ≠ 0 := fun k => hz0.coord_ne (q := ⟨k, c (some k)⟩) (hc (some k))
  have hcw : w ⟨none, c none⟩ ≠ 0 := hz.coord_ne (hc none)
  have hε := Fr.ε_ne
  have hγ := Fr.γ_ne
  have hU₀ : HasVal y (z ∘ v₀ k₀) (∑ m, Fr.α m * (y ⟨k₀, m⟩ / y ⟨k₀, c (some k₀)⟩))
      (∑ m, Fr.αv m * (z ⟨some k₀, m⟩ / z ⟨some k₀, c (some k₀)⟩)) :=
    HasVal.sum _ fun m _ => (Fr.hα m).mul (hasVal_ratio hz0 m (c (some k₀)) (hc (some k₀)))
  have eU₀ : (∑ m, Fr.α m * (y ⟨k₀, m⟩ / y ⟨k₀, c (some k₀)⟩)) = Fr.ε⁻¹ / y ⟨k₀, c (some k₀)⟩ := by
    rw [← Fr.αA, Finset.sum_div]
    simp only [mul_div_assoc]
  rw [eU₀] at hU₀
  have lin : ∀ (μ : ι k₀ → Φ) (μv : ι k₀ → L), (∀ m, HasVal y (z ∘ v₀ k₀) (μ m) (μv m)) →
      HasVal w z ((φ (∑ m, μ m * y ⟨k₀, m⟩) + RatFunc.X * φ (∑ m, μ m * B m)) / w ⟨none, c none⟩)
        (∑ m, μv m * (z ⟨none, m⟩ / z ⟨none, c none⟩)) := fun μ μv h => by
    rw [← pen_lin (y := y), Finset.sum_div]
    simp only [mul_div_assoc]
    exact HasVal.sum _ fun m _ => (pull (h m)).mul (hasVal_ratio hz (k := none) m (c none) (hc none))
  have hU := lin _ _ Fr.hα
  have hV := lin _ _ Fr.hβ
  rw [Fr.αA, Fr.αB] at hU
  rw [Fr.βA, Fr.βB] at hV
  have hφε : φ Fr.ε ≠ 0 := (map_ne_zero φ).2 hε
  have hφγ : φ Fr.γ ≠ 0 := (map_ne_zero φ).2 hγ
  refine ⟨_, _, _, _, pull (Fr.hs.mul hU₀), fun m => ?_, hU, hV, fun m => ?_, ?_⟩
  · refine (hasVal_ratio hz0 m (c (some k₀)) (hc (some k₀))).unique hz0 ?_
    have := (Fr.hp m).mul hU₀
    rwa [Fr.p_eq, show Fr.ε * y ⟨k₀, m⟩ * (Fr.ε⁻¹ / y ⟨k₀, c (some k₀)⟩) = y ⟨k₀, m⟩ / y ⟨k₀, c (some k₀)⟩ by
      field_simp] at this
  · rw [Fr.p_eq, Fr.r_eq, show w ⟨none, m⟩ = φ (y ⟨k₀, m⟩) + RatFunc.X * φ (B m) from rfl]
    simp only [map_mul, map_add, map_neg, map_inv₀, map_zero]
    change _ = φ _ * φ _ * _ + (φ _ * φ _ + φ _ * φ _) * _
    field_simp
    ring
  · have e1 : chartMono w c (totDeg k₀ e) = w ⟨none, c none⟩ *
        (φ (chartMono y (fun k => c (some k)) e) * φ (y ⟨k₀, c (some k₀)⟩)) := by
      rw [chartMono, Fintype.prod_option, chartMono, map_prod]
      congr 1
      · exact zpow_one _
      · have : ∀ k, w ⟨some k, c (some k)⟩ ^ totDeg k₀ e (some k) = φ (y ⟨k, c (some k)⟩ ^ e k) *
            if k = k₀ then φ (y ⟨k₀, c (some k₀)⟩) else 1 := fun k => by
          show φ (y ⟨k, c (some k)⟩) ^ (e k + if k = k₀ then 1 else 0) = _
          rw [zpow_add₀ ((map_ne_zero φ).2 (hcy k)), map_zpow₀]
          split_ifs with h
          · subst h; rw [zpow_one]
          · rw [zpow_zero]
        simp only [this, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    have h1 : φ (chartMono y (fun k => c (some k)) e) ≠ 0 := (map_ne_zero φ).2 (chartMono_ne hcy e)
    have h2 : φ (y ⟨k₀, c (some k₀)⟩) ≠ 0 := (map_ne_zero φ).2 (hcy k₀)
    rw [e1]
    simp only [map_mul, map_div₀, map_inv₀, map_zero]
    change RatFunc.X * φ cf / _ = _
    field_simp
    ring

theorem isPt_diag {z : (Σ k, ι k) → L} (hz : IsPt y z) :
    IsPt (ext2 y k₀ fun m => y ⟨k₀, m⟩) (ext2 z k₀ fun m => z ⟨k₀, m⟩) := by
  let fold : (Σ o : Option K, ι (o.getD k₀)) → Σ k, ι k := fun q => ⟨q.1.getD k₀, q.2⟩
  have e1 : (ext2 y k₀ fun m => y ⟨k₀, m⟩) = y ∘ fold := by
    funext q
    rcases q with ⟨_ | k, m⟩ <;> rfl
  have e2 : (ext2 z k₀ fun m => z ⟨k₀, m⟩) = z ∘ fold := by
    funext q
    rcases q with ⟨_ | k, m⟩ <;> rfl
  rw [e1, e2]
  refine ⟨fun o => hz.1 (o.getD k₀), fun f hf => ?_⟩
  rw [← aeval_rename]
  refine hz.2 _ ?_
  have hf' : mConeMap (y ∘ fold) f = 0 := hf
  have e : (mConeMap y).comp (rename fold) = ((rename fun o : Option K => o.getD k₀).restrictScalars ℤ).comp
      (mConeMap (y ∘ fold)) := MvPolynomial.algHom_ext fun q => by simp [mConeMap, fold]
  have := DFunLike.congr_fun e f
  simp only [AlgHom.comp_apply, hf', map_zero] at this
  exact this

theorem sec_pen (h0 : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (hFr : ∀ (E : Type) [Field E] (z : (Σ k, ι k) → E), IsPt y z → ∀ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) →
      Nonempty (PenFrame y k₀ B cf e z c)) :
    ∃ (g h : MRing (iW ι k₀)) (dg dh : Option K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
      g ∉ mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) ∧
      h ∉ mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) ∧
      (∀ o, (dg o : ℤ) - dh o = totDeg k₀ e o) ∧
      aeval (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) g =
        RatFunc.X * algebraMap Φ (RatFunc Φ) cf * aeval (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) h ∧
      divCycle (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X)) g =
        divCycle (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X)) h +
          Finsupp.single (mCoordIdeal (ext2 y k₀ fun m => y ⟨k₀, m⟩)) 1 := by
  set w := penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X with hw
  set δ := ext2 y k₀ fun m => y ⟨k₀, m⟩ with hδ
  let φ := algebraMap Φ (RatFunc Φ)
  choose c₀ hc₀ using h0
  let c : ∀ o, iW ι k₀ o := fun o => c₀ (o.getD k₀)
  have hc : ∀ o, δ ⟨o, c o⟩ ≠ 0 := by
    rintro (_ | k)
    · exact hc₀ k₀
    · exact hc₀ k
  have hle : mCoordIdeal w ≤ mCoordIdeal δ := pen_le_zero _ _ _ _
  have hpt : IsPt w δ := ⟨fun o => ⟨c o, hc o⟩, fun f hf => aeval_eq_zero_of_mem (hle hf)⟩
  have hcw : ∀ o, w ⟨o, c o⟩ ≠ 0 := fun o => hpt.coord_ne (hc o)
  obtain ⟨Fr⟩ := hFr Φ y (isPt_self fun k => ⟨c₀ k, hc₀ k⟩) c₀ hc₀
  obtain ⟨η, U, V, Uv, hη, hp, hU, hV, hrel, hσ⟩ := local_data (cf := cf) (e := e) hpt hc Fr
  rw [← hw] at hη hU hV hrel hσ
  have hηv : (Fr.sv * ∑ m, Fr.αv m * (δ ⟨some k₀, m⟩ / δ ⟨some k₀, c (some k₀)⟩)) ≠ 0 := by
    refine mul_ne_zero Fr.sv_ne fun h => ?_
    have := hp (c (some k₀))
    rw [h, mul_zero, div_self (hc _)] at this
    exact one_ne_zero this
  have hV0 : (∑ m, Fr.βv m * (δ ⟨none, m⟩ / δ ⟨none, c none⟩)) = 0 := by
    simp only [← mul_div_assoc, ← Finset.sum_div, hasVal_self_eq (Fr.hβ _)]
    rw [show (∑ m, Fr.β m * δ ⟨none, m⟩) = 0 from Fr.βA, zero_div]
  rw [hV0] at hV
  have hcf : cf ≠ 0 := by
    rintro rfl
    exact Fr.hs.ne_zero (isPt_self fun k => ⟨c₀ k, hc₀ k⟩) Fr.sv_ne (by simp)
  have hσ0 : RatFunc.X * φ cf ≠ 0 := mul_ne_zero RatFunc.X_ne_zero ((map_ne_zero φ).2 hcf)
  obtain ⟨d, n, m, hn, hm, hm0, e1, e2⟩ := hη.mul hV
  let dp : Option K → ℕ := fun o => (totDeg k₀ e o).toNat
  let dm : Option K → ℕ := fun o => (-totDeg k₀ e o).toNat
  have hpm : ∀ o, (dp o : ℤ) - dm o = totDeg k₀ e o := fun o => Int.toNat_sub_toNat_neg _
  have hg := isMultiHomog_mul hn (isMultiHomog_monoX c dp)
  have hh := isMultiHomog_mul hm (isMultiHomog_monoX c dm)
  have hdeg : ∀ o, ((d + dp) o : ℤ) - (d + dm) o = totDeg k₀ e o := fun o => by
    rw [← hpm]; simp
  have hhδ : aeval δ (m * monoX c dm) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hm0 (aeval_monoX_ne hc _)
  have hhw : aeval w (m * monoX c dm) ≠ 0 := hpt.aeval_ne hh hhδ
  have hmono := chartMono_ne hcw (totDeg k₀ e)
  have hq : aeval w (n * monoX c dp) = RatFunc.X * φ cf * aeval w (m * monoX c dm) := by
    rw [map_mul, map_mul, e1, ← hσ, ← chartMono_mul hcw hpm]
    change RatFunc.X * φ cf / _ * _ * _ = _
    field_simp
  set g := n * monoX c dp
  set h := m * monoX c dm
  have hgw : g ∉ mCoordIdeal w := fun hh' => mul_ne_zero hσ0 hhw (hq ▸ aeval_eq_zero_of_mem hh')
  have hΔp : (mCoordIdeal δ).IsPrime := RingHom.ker_isPrime _
  refine ⟨g, h, d + dp, d + dm, hg, hh, hgw, fun hh' => hhw (aeval_eq_zero_of_mem hh'), hdeg, hq, ?_⟩
  refine div_eq_of_local (RingHom.ker_isPrime _) hΔp (CoordinateConeArithVar.relevant δ c hc) hle hgw
    (fun hh' => hhδ (aeval_eq_zero_of_mem hh')) ((mem_iff_of_homog hg).2 (by
      rw [map_mul, e2, mul_zero, zero_mul, zero_mul])) ?_ ?_
  · let J : Ideal (MRing (iW ι k₀)) :=
      { carrier := {f | ∃ u ∉ mCoordIdeal δ, u * f ∈ mCoordIdeal w ⊔ Ideal.span {g}}
        add_mem' := by
          rintro a b ⟨u, hu, hua⟩ ⟨v, hv, hvb⟩
          refine ⟨u * v, fun hm => (hΔp.mem_or_mem hm).elim hu hv, ?_⟩
          have e' : u * v * (a + b) = v * (u * a) + u * (v * b) := by ring
          rw [e']
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hua) (Ideal.mul_mem_left _ _ hvb)
        zero_mem' := ⟨1, fun h1 => hΔp.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simp⟩
        smul_mem' := by
          rintro a b ⟨u, hu, hub⟩
          refine ⟨u, hu, ?_⟩
          rw [smul_eq_mul, mul_left_comm]
          exact Ideal.mul_mem_left _ _ hub }
    refine mCoordIdeal_le_of_homog (J := J) fun f a hf hf0 => ?_
    have pull : ∀ {s v}, HasVal y y s v → φ s ∈ regO w δ := fun h =>
      ⟨_, HasVal.pull (isBlockMap_initial_vertex k₀) φ (y' := w) (z' := δ) rfl h⟩
    let sc : Option K → RatFunc Φ := fun o => o.elim (φ Fr.ε * U) fun k => (φ (y ⟨k, c₀ k⟩))⁻¹
    have hrat : ∀ q, CoordinateConeArithVar.ratioPt w c q ∈ regO w δ := fun q =>
      ⟨_, hasVal_ratio hpt q.2 (c q.1) (hc q.1)⟩
    have hb1 : ∀ m, sc none * (φ ∘ δ) ⟨none, m⟩ = φ (Fr.p m) * U := fun m => by
      rw [Fr.p_eq, map_mul]
      show φ Fr.ε * U * φ (y ⟨k₀, m⟩) = _
      ring
    have hb2 : ∀ k m, sc (some k) * (φ ∘ δ) ⟨some k, m⟩ = CoordinateConeArithVar.ratioPt w c ⟨some k, m⟩ := fun k m => by
      show (φ (y ⟨k, c₀ k⟩))⁻¹ * φ (y ⟨k, m⟩) = φ (y ⟨k, m⟩) / φ (y ⟨k, c₀ k⟩)
      rw [div_eq_mul_inv, mul_comm]
    obtain ⟨-, ρ, hρ, hρe⟩ := congr_aeval (regO w δ) (CoordinateConeArithVar.ratioPt w c)
      (fun q => sc q.1 * (φ ∘ δ) q) V hrat (by
        rintro ⟨_ | k, m⟩
        · exact hb1 m ▸ mul_mem (pull (Fr.hp m)) ⟨_, hU⟩
        · exact hb2 k m ▸ hrat _) (by
        rintro ⟨_ | k, m⟩
        · refine ⟨φ (Fr.r m), pull (Fr.hr m), ?_⟩
          rw [hb1 m, show CoordinateConeArithVar.ratioPt w c ⟨none, m⟩ = _ from hrel m]
          exact add_sub_cancel_left _ _
        · exact ⟨0, zero_mem _, by rw [hb2 k m, sub_self, zero_mul]⟩) f
    rw [aeval_scale' sc _ hf, CPts.aeval_comp_ringHom, hf0, map_zero, mul_zero, sub_zero, aeval_ratioPt hf] at hρe
    obtain ⟨ρv, hρ⟩ := hρ
    obtain ⟨d', n', m', hn', hm', hm0', e1', -⟩ := hρ.mul (hη.inv hpt hηv)
    have hη0 : η ≠ 0 := hη.ne_zero hpt hηv
    refine ⟨m' * monoX c (d + dp) * h, fun hh' => ?_, ?_⟩
    · have := aeval_eq_zero_of_mem hh'
      rw [map_mul, map_mul] at this
      exact mul_ne_zero (mul_ne_zero hm0' (aeval_monoX_ne hc _)) hhδ this
    · have hd : IsMultiHomog (m' * monoX c (d + dp) * h * f - n' * monoX c a * monoX c (d + dm) * g)
          (d' + (d + dp) + (d + dm) + a) := by
        refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul
          (isMultiHomog_mul hm' (isMultiHomog_monoX _ _)) hh) hf) ?_
        rw [show d' + (d + dp) + (d + dm) + a = d' + a + (d + dm) + (d + dp) by ring]
        exact isMultiHomog_mul (isMultiHomog_mul (isMultiHomog_mul hn' (isMultiHomog_monoX _ _))
          (isMultiHomog_monoX _ _)) hg
      have hP : m' * monoX c (d + dp) * h * f - n' * monoX c a * monoX c (d + dm) * g ∈ mCoordIdeal w := by
        rw [mem_iff_of_homog hd]
        have h1 : aeval w f = aeval w (monoX c a) * (ρ * V) := by
          rw [← hρe, aeval_monoX, ← mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one fun k _ => by
            rw [← mul_pow, mul_inv_cancel₀ (hcw k), one_pow], one_mul]
        have h2 : RatFunc.X * φ cf = η * V * chartMono w c (totDeg k₀ e) := by
          rw [← hσ]; exact (div_mul_cancel₀ _ hmono).symm
        rw [map_sub, map_mul _ _ f, map_mul _ _ g, map_mul _ _ h, map_mul _ m', map_mul _ (n' * _), map_mul _ n', h1, hq, h2, e1',
          ← chartMono_mul hcw hdeg]
        field_simp
        ring
      have e' : m' * monoX c (d + dp) * h * f = (m' * monoX c (d + dp) * h * f - n' * monoX c a * monoX c (d + dm) * g)
          + n' * monoX c a * monoX c (d + dm) * g := by ring
      rw [e']
      exact Ideal.add_mem _ (Ideal.mem_sup_left hP)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))
  · intro W hW hWr hPW hΔW
    obtain ⟨E, _, z, hz⟩ := exists_point W hW
    choose c' hc' using hWr
    have hc'' : ∀ o, z ⟨o, c' o⟩ ≠ 0 := fun o h => hc' o ((hz _).1 (by rwa [aeval_X]))
    have hzp : IsPt w z := ⟨fun o => ⟨c' o, hc'' o⟩, fun f hf => (hz f).2 (hPW hf)⟩
    have hz0 : IsPt y (z ∘ v₀ k₀) := hzp.comp (isBlockMap_initial_vertex k₀) φ rfl
    obtain ⟨Fr'⟩ := hFr E (z ∘ v₀ k₀) hz0 (fun k => c' (some k)) fun k => hc'' (some k)
    obtain ⟨η', U', V', Uv', hη', hp', hU', hV', hrel', hσ'⟩ := local_data (cf := cf) (e := e) hzp hc'' Fr'
    rw [← hw] at hη' hU' hV' hrel' hσ'
    set U₀ := ∑ m, Fr'.αv m * (z ⟨some k₀, m⟩ / z ⟨some k₀, c' (some k₀)⟩)
    set Vv := ∑ m, Fr'.βv m * (z ⟨none, m⟩ / z ⟨none, c' none⟩)
    have hU₀ : U₀ ≠ 0 := fun h => by
      have := hp' (c' (some k₀))
      rw [h, mul_zero, div_self (hc'' _)] at this
      exact one_ne_zero this
    have hVv : Vv ≠ 0 := fun h => hΔW <| by
      rw [h] at hV'
      have h1 : ∀ m, z ⟨none, m⟩ / z ⟨none, c' none⟩ = Fr'.pv m * Uv' := fun m => by
        refine (hasVal_ratio hzp (k := none) m (c' none) (hc'' none)).unique hzp ?_
        rw [hrel' m]
        simpa only [mul_zero, add_zero] using (((Fr'.hp m).pull (isBlockMap_initial_vertex k₀) φ (y' := w) rfl).mul hU').add
          (((Fr'.hr m).pull (isBlockMap_initial_vertex k₀) φ (y' := w) rfl).mul hV')
      let sc : Option K → E := fun o => o.elim (z ⟨none, c' none⟩ * Uv' / (U₀ * z ⟨some k₀, c' (some k₀)⟩)) fun _ => 1
      have h2 : z = fun q => sc q.1 * ext2 (z ∘ v₀ k₀) k₀ (fun m => (z ∘ v₀ k₀) ⟨k₀, m⟩) q := by
        funext q
        rcases q with ⟨_ | k, m⟩
        · show z ⟨none, m⟩ = z ⟨none, c' none⟩ * Uv' / (U₀ * z ⟨some k₀, c' (some k₀)⟩) * z ⟨some k₀, m⟩
          have a1 := (div_eq_iff (hc'' none)).1 (h1 m)
          have a2 := (div_eq_iff (hc'' (some k₀))).1 (hp' m)
          have a3 := hc'' (some k₀)
          rw [a1, a2]
          field_simp
        · exact (one_mul _).symm
      refine mCoordIdeal_le_of_homog fun f a hf hf0 => (hz f).1 ?_
      rw [h2, aeval_scale' sc _ hf, (isPt_diag hz0).2 f ((mem_iff_of_homog hf).2 hf0), mul_zero]
    obtain ⟨u, u', hu, hu', hm⟩ := exists_rel hzp hc'' (hσ' ▸ hη'.mul hV') hg hh hdeg hq
    refine ⟨u, u', fun h => hu ((hz _).2 h), fun h => ?_, hm⟩
    rw [(hz _).2 h] at hu'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero Fr'.sv_ne hU₀) hVv) (chartMono_ne hc'' _)) hu hu'.symm

end PositivityTheory.Xgp.W
end
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_w_sec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∃ (g h : MRing fun o : Option K => ι (o.getD k₀)) (dg dh : Option K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ g ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ∧ h ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ∧ (∀ o : Option K, (dg o : ℤ) - dh o = o.elim 1 fun k => -(fun k => ∑ p, xiCoef τ a p * M.dy p k) k - (if M.blk (τ, a) = some k then 1 else 0)) ∧ aeval (M.wCo (τ, a) k₀ ca cb RatFunc.X) g = RatFunc.X * algebraMap Φ (RatFunc Φ) (∏ p, (if IsProperStep N j p.2 then 1 else algebraMap M.Ω Φ (M.lam p) * (if (p.2 : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (M.g p.1) (wIdx N j) (wIdx N j) else 1) else minorIJ (M.g p.1) (omIdx N j) (omIdx N j))) ^ xiCoef τ a p) * aeval (M.wCo (τ, a) k₀ ca cb RatFunc.X) h ∧ divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) g = divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) h + Finsupp.single (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) 1 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M d τ a b k₀ ca cb hb hab hk hca hcb _
  have hne : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := PositivityTheory.Xgp.W.blocks_of_model M
  obtain ⟨g, h, dg, dh, hg, hh, hgn, hhn, hdeg, haev, hdiv⟩ :=
    PositivityTheory.Xgp.W.sec_pen (B := PositivityTheory.Xgp.W.vecB M τ a k₀ ca cb) (cf := PositivityTheory.Xgp.W.cFac M τ a)
      (e := PositivityTheory.Xgp.W.eDeg M τ a k₀) hne
      (fun E _ z hz c hc => PositivityTheory.Xgp.W.exists_penFrame M hb hab hk hca hcb hz c hc)
  refine ⟨g, h, dg, dh, hg, hh, ?_⟩
  rw [PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb, PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb,
    PositivityTheory.Xgp.W.ideal_pen_zero]
  refine ⟨hgn, hhn, ?_, ?_, hdiv⟩
  · intro o
    rw [hdeg o]
    cases o with
    | none => rfl
    | some k =>
      simp only [PositivityTheory.Xgp.W.totDeg, PositivityTheory.Xgp.W.eDeg, Option.elim, hk, Option.some.injEq]
      by_cases hkk : k = k₀
      · subst hkk
        simp
        ring
      · simp [hkk, Ne.symm hkk]
  · have hI : (PositivityTheory.Xgp.W.intAlg5 : Algebra ℤ (RatFunc Φ)) = RatFunc.instAlgebraOfPolynomial Φ ℤ :=
      Subsingleton.elim _ _
    have key : ∀ f : MRing (PositivityTheory.Xgp.W.iW ι k₀),
        @aeval ℤ (RatFunc Φ) _ _ _ PositivityTheory.Xgp.W.intAlg5
          (PositivityTheory.Xgp.W.penCo y k₀ (fun m => y ⟨k₀, m⟩) (PositivityTheory.Xgp.W.vecB M τ a k₀ ca cb) RatFunc.X) f =
        @aeval ℤ (RatFunc Φ) _ _ _ (RatFunc.instAlgebraOfPolynomial Φ ℤ)
          (PositivityTheory.Xgp.W.penCo y k₀ (fun m => y ⟨k₀, m⟩) (PositivityTheory.Xgp.W.vecB M τ a k₀ ca cb) RatFunc.X) f := by
      intro f
      rw [hI]
    rw [key g, key h] at haev
    exact haev
end

section
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

local instance (priority := 2000) intAlg4 {Φ : Type} [Field Φ] : Algebra ℤ (RatFunc Φ) := Ring.toIntAlgebra _

open GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem exists_lift_gen {A F E : Type} [CommRing A] [Field F] [Field E] (a : A →+* F) (b : A →+* E)
    (hk : RingHom.ker a = RingHom.ker b) (gen : ∀ c, ∃ f g, c = a f / a g) : ∃ ψ : F →+* E, ∀ f, ψ (a f) = b f := by
  letI : Algebra (A ⧸ RingHom.ker a) F := (RingHom.kerLift a).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker a) F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective a)
  haveI : IsFractionRing (A ⧸ RingHom.ker a) F := IsFractionRing.of_field _ _ fun c => by
    obtain ⟨f, g, e⟩ := gen c
    exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, e⟩
  let b' : A ⧸ RingHom.ker a →+* E := Ideal.Quotient.lift _ b fun f hf => by rwa [hk] at hf
  have hb' : Function.Injective b' := RingHom.lift_injective_of_ker_le_ideal _ _ hk.ge
  exact ⟨IsFractionRing.lift hb', fun f => IsFractionRing.lift_algebraMap hb' (Ideal.Quotient.mk _ f)⟩

def fibEquiv (ι : K → Type) (k₀ : K) :
    (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) ≃ ι k₀ where
  toFun
    | ⟨⟨some k, h⟩, _⟩ => absurd ⟨k, rfl⟩ h
    | ⟨⟨none, _⟩, m⟩ => m
  invFun m := ⟨⟨none, by rintro ⟨k, hk⟩; cases hk⟩, m⟩
  left_inv := by
    rintro ⟨⟨_ | k, h⟩, m⟩
    · rfl
    · exact absurd ⟨k, rfl⟩ h
  right_inv _ := rfl

theorem fibreBlock_subsingleton (k k' : FibreBlock (some : K → Option K)) : k = k' := by
  rcases k with ⟨_ | k, hk⟩
  · rcases k' with ⟨_ | k', hk'⟩
    · rfl
    · exact absurd ⟨k', rfl⟩ hk'
  · exact absurd ⟨k, rfl⟩ hk

theorem isMultiHomog_lin {F : Type} [Field F] (k₀ : K)
    (μ : (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) → F) :
    IsMultiHomog (∑ q, C (μ q) * X q : MRingOver F (fibreIdx (iW ι k₀) some)) fun _ => 1 := by
  intro s hs k
  obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (support_sum hs)
  rw [C_mul_X_eq_monomial] at hq
  have hs' := support_monomial_subset hq
  rw [Finset.mem_singleton] at hs'
  subst hs'
  obtain ⟨qk, qi⟩ := q
  obtain rfl : qk = k := fibreBlock_subsingleton _ _
  simp [Finsupp.single_apply]

variable {y : (Σ k, ι k) → Φ} {k₀ : K} {B : ι k₀ → Φ}

theorem cone_homog {E : Type} [Field E] (i₀ : MvPolynomial K Φ →+* E) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) : i₀ (mConeMap y g) = (∏ k, i₀ (X k) ^ d k) * i₀ (C (aeval y g)) := by
  have e : i₀.comp (mConeMap y).toRingHom =
      (aeval (fun p : Σ k, ι k => i₀ (X p.1) * ((i₀.comp C) ∘ y) p) : MRing ι →ₐ[ℤ] E).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) fun p => by simp [mConeMap, mul_comm]
  have := RingHom.congr_fun e g
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this, aeval_scale' (fun k => i₀ (X k)) _ hg, CPts.aeval_comp_ringHom]
  rfl

theorem exists_positive_period_line {E : Type} [Field E] (i₀ : MvPolynomial K Φ →+* E) (hi : Function.Injective i₀)
    {cf : Φ} {e : K → ℤ} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e y c)
    (G : GenFibre (v₀ k₀) (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X))) :
    ∃ T : Set (MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K))),
      (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T := by
  let a : MRing ι →+* G.Φ := (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom
  have hka : RingHom.ker a = mCoordIdeal y := G.ker_x.trans (image_pen _ _ _ _ _)
  obtain ⟨ψ, hψ⟩ := exists_lift_gen a (i₀.comp (mConeMap y).toRingHom)
    (by rw [hka, RingHom.ker_comp_of_injective _ hi]; rfl)
    (fun c => by obtain ⟨f, g, -, e⟩ := G.gen c; exact ⟨f, g, e⟩)
  have lift : ∀ s v, HasVal y y s v → ∃ s', ψ s' = i₀ (C s) := by
    rintro s v ⟨d, g, h, hg, hh, h0, e, -⟩
    refine ⟨a g / a h, ?_⟩
    rw [map_div₀, hψ, hψ]
    show i₀ (mConeMap y g) / i₀ (mConeMap y h) = _
    have hp : (∏ k, i₀ (X k) ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ ((map_ne_zero_iff _ hi).2 (X_ne_zero _))
    have h1 : i₀ (C (aeval y h)) ≠ 0 := (map_ne_zero_iff _ hi).2 (by rwa [Ne, C_eq_zero])
    rw [cone_homog i₀ hg, cone_homog i₀ hh, mul_div_mul_left _ _ hp, e, map_mul, map_mul,
      mul_div_cancel_right₀ _ h1]
  choose p hp using fun m => lift _ _ (Fr.hp m)
  choose r hr using fun m => lift _ _ (Fr.hr m)
  choose α hα using fun m => lift _ _ (Fr.hα m)
  choose β hβ using fun m => lift _ _ (Fr.hβ m)
  let eF := fibEquiv ι k₀
  let ℓ : (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) → Fin 2 → G.Φ :=
    fun q => ![p (eF q), r (eF q)]
  have hν : ∀ a b : Fin 2, ∑ q, ![fun q => α (eF q), fun q => β (eF q)] a q * ℓ q b = if a = b then 1 else 0 := by
    have key : ∀ (u w : ι k₀ → G.Φ) (u' w' : ι k₀ → Φ) (s : G.Φ) (s' : Φ), (∀ m, ψ (u m) = i₀ (C (u' m))) →
        (∀ m, ψ (w m) = i₀ (C (w' m))) → ψ s = i₀ (C s') → ∑ m, u' m * w' m = s' →
        ∑ q, u (eF q) * w (eF q) = s := fun u w u' w' s s' hu hw hs h => by
      rw [Equiv.sum_comp eF fun m => u m * w m]
      apply ψ.injective
      rw [hs, ← h]
      simp only [map_sum, map_mul, hu, hw]
    intro a b
    fin_cases a <;> fin_cases b
    · exact key α p _ _ 1 1 hα hp (by simp) Fr.αp
    · exact key α r _ _ 0 0 hα hr (by simp) Fr.αr
    · exact key β p _ _ 0 0 hβ hp (by simp) Fr.βp
    · exact key β r _ _ 1 1 hβ hr (by simp) Fr.βr
  refine ⟨linKerForms ℓ, ?_, ?_⟩
  · rintro f ⟨μ, -, rfl⟩
    exact isMultiHomog_lin k₀ μ
  rw [← ker_linSubst ℓ _ hν]
  let W' : MRing (iW ι k₀) →+* MvPolynomial (Fin 2) E := (MvPolynomial.map i₀).comp (planeMap y k₀ Fr.p Fr.r)
  let x' : MRing (iW ι k₀) →+* G.Φ' := (aeval G.x' : MRing (iW ι k₀) →ₐ[ℤ] G.Φ').toRingHom
  have hker : RingHom.ker x' = RingHom.ker W' := by
    rw [RingHom.ker_comp_of_injective _ (MvPolynomial.map_injective _ hi), ← Fr.ker_eq, ← ideal_pen_plane]
    exact G.genericFibre_ker_target
  have r1 : ∀ f, x' (rename (v₀ k₀) f) = algebraMap G.Φ G.Φ' (a f) := fun f => by
    have e : x'.comp (rename (v₀ k₀) : MRing ι →ₐ[ℤ] MRing (iW ι k₀)).toRingHom = (algebraMap G.Φ G.Φ').comp a :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun q => by simpa [x', a] using G.compat q
    exact RingHom.congr_fun e f
  have r2 : ∀ f, W' (rename (v₀ k₀) f) = C (ψ (a f)) := fun f => by
    rw [hψ]
    have e : W'.comp (rename (v₀ k₀) : MRing ι →ₐ[ℤ] MRing (iW ι k₀)).toRingHom =
        (C : E →+* _).comp (i₀.comp (mConeMap y).toRingHom) :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun q => by simp [W', planeMap, ext2, v₀, mConeMap]
    exact RingHom.congr_fun e f
  have main : ∀ f : MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K)), ∃ (Dn : MRing ι) (f' : MRing (iW ι k₀)),
      a Dn ≠ 0 ∧ x' f' = algebraMap G.Φ G.Φ' (a Dn) *
        aeval (fun q : Σ k : FibreBlock (some : K → Option K), iW ι k₀ k.1 => G.x' ⟨q.1.1, q.2⟩) f ∧
      W' f' = C (ψ (a Dn)) * MvPolynomial.map ψ (linSubst ℓ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C s =>
      obtain ⟨f, g, hg, e⟩ := G.gen s
      have e' : a f = a g * s := by rw [e]; exact (mul_div_cancel₀ _ hg).symm
      refine ⟨g, rename (v₀ k₀) f, hg, ?_, ?_⟩
      · rw [r1, e', map_mul, aeval_C]
      · rw [r2, e', map_mul, map_mul, algHom_C, algebraMap_eq, map_C]
    | add f g hf hg =>
      obtain ⟨D₁, f₁, h₁, a₁, b₁⟩ := hf
      obtain ⟨D₂, f₂, h₂, a₂, b₂⟩ := hg
      refine ⟨D₁ * D₂, f₁ * rename (v₀ k₀) D₂ + f₂ * rename (v₀ k₀) D₁, by rw [map_mul]; exact mul_ne_zero h₁ h₂,
        ?_, ?_⟩
      · simp only [map_add, map_mul, r1, a₁, a₂]; ring
      · simp only [map_add, map_mul, r2, b₁, b₂]; ring
    | mul_X f q hf =>
      obtain ⟨D₁, f₁, h₁, a₁, b₁⟩ := hf
      refine ⟨D₁, f₁ * X ⟨q.1.1, q.2⟩, h₁, ?_, ?_⟩
      · rw [map_mul, map_mul, a₁, aeval_X, mul_assoc]
        congr 2
        exact aeval_X _ _
      · rw [map_mul, map_mul, map_mul, b₁, mul_assoc]
        congr 2
        obtain ⟨m, rfl⟩ := eF.symm.surjective q
        have : W' (X ⟨none, m⟩) = C (i₀ (C (Fr.p m))) * X 0 + C (i₀ (C (Fr.r m))) * X 1 := by
          simp [W', planeMap, ext2]
        refine this.trans ?_
        simp [linSubst, ℓ, Fin.sum_univ_two, hp, hr]
  ext f
  obtain ⟨Dn, f', h0, h1, h2⟩ := main f
  have h3 : x' f' = 0 ↔ W' f' = 0 := SetLike.ext_iff.1 hker f'
  rw [h1, h2, mul_eq_zero, mul_eq_zero, or_iff_right ((map_ne_zero _).2 h0),
    or_iff_right (by rw [C_eq_zero]; exact (map_ne_zero _).2 h0),
    map_eq_zero_iff _ (MvPolynomial.map_injective _ ψ.injective)] at h3
  exact h3

theorem line_pen {cf : Φ} {e : K → ℤ} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e y c)
    (G : GenFibre (v₀ k₀) (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X))) :
    ∃ T : Set (MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K))),
      (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T :=
  exists_positive_period_line (algebraMap _ (FractionRing (MvPolynomial K Φ))) (IsFractionRing.injective _ _) Fr G

end PositivityTheory.Xgp.W
end
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_w_line : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ G : GenFibre (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), ∃ T : Set (MRingOver G.Φ (fibreIdx (fun o : Option K => ι (o.getD k₀)) (some : K → Option K))), (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hb hab hk hca hcb
  choose c hc using PositivityTheory.Xgp.W.blocks_of_model M
  obtain ⟨Fr⟩ := PositivityTheory.Xgp.W.exists_penFrame M hb hab hk hca hcb (PositivityTheory.Xgp.W.isPt_self fun k => ⟨c k, hc k⟩) c hc
  rw [PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb]
  exact fun G => PositivityTheory.Xgp.W.line_pen Fr G
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section
namespace PositivityTheory.Xgp.c_algsq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem wCo_zero (M : FlagModel y Ψ N j) {p : Ψ × Fin N} {k₀ : K} (hk : M.blk p = some k₀) (ca cb : Fin N)
    (m : ι k₀) : M.wCo p k₀ ca cb 0 ⟨none, m⟩ = M.wCo p k₀ ca cb 0 ⟨some k₀, m⟩ := by
  simp only [FlagModel.wCo, Matrix.single_zero, add_zero, mul_one]
  rw [M.y_step p k₀ hk m, map_sum]
  exact Finset.sum_congr rfl fun I _ => by rw [map_mul, CPts.minorIJ_map]

def mkAlg (M : FlagModel y Ψ N j) {d : ℕ} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N} (hb : (b : ℕ) = a + 1)
    (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀) (hca : (ca : ℕ) = lastCol N j a)
    (hcb : (cb : ℕ) = ca + 1) (hy : IsArithVar (mCoordIdeal y) (d + 2)) (xi2 : K → ℤ) (hxi : xi2 k₀ = -2)
    (g h : MRing fun o : Option K => ι (o.getD k₀)) (dg dh : Option K → ℕ) (hg : IsMultiHomog g dg)
    (hh : IsMultiHomog h dh) (hgn : g ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))
    (hhn : h ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))
    (hdeg : ∀ o : Option K, (dg o : ℤ) - dh o = o.elim 1 fun k => -xi2 k - (if M.blk (τ, a) = some k then 1 else 0))
    (hdiv : divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) g =
      divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) h +
        Finsupp.single (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) 1) :
    AlgSq (mCoordIdeal y) d k₀ xi2 where
  arithY := hy
  xi_two_base_eq_neg_two := hxi
  KW := Option K
  ιW := fun o => ι (o.getD k₀)
  PW := mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)
  arithW := (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).1
  κ := ![some, κ₁ k₀]
  v := ![v₀ k₀, v₁ k₀]
  block := Fin.forall_fin_two.2 ⟨Pts.isBlockMap_v₀ k₀, isBlockMap_v₁ k₀⟩
  image := Fin.forall_fin_two.2 ⟨(t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.2.1,
    (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.2.2 (v₁ k₀) (fun _ h => v₁_ne h)
      (v₁_self k₀)⟩
  same p hp := (v₁_ne hp).symm
  new := by
    rintro ⟨k, hk'⟩
    have : some k = κ₁ k₀ k₀ := hk'
    rw [κ₁_self] at this
    cases this
  all k' := by
    cases k' with
    | none => exact Or.inr (κ₁_self k₀).symm
    | some k => exact Or.inl ⟨k, rfl⟩
  fibre_line := t_c_w_line K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hk hca hcb
  Δ := mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)
  arithΔ := (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.1
  PW_le := (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.1
  diag i i' := by
    show mConeMap _ (X (v₀ k₀ ⟨k₀, i⟩) * X (v₁ k₀ ⟨k₀, i'⟩) - X (v₀ k₀ ⟨k₀, i'⟩) * X (v₁ k₀ ⟨k₀, i⟩)) = 0
    rw [v₁_self, v₁_self]
    simp only [mConeMap, map_sub, map_mul, aeval_X, v₀, wCo_zero M hk]
    ring
  g := g
  h := h
  dg := dg
  dh := dh
  g_deg := hg
  h_deg := hh
  g_nmem := hgn
  h_nmem := hhn
  deg_eq o := by
    show _ = -(pullDeg some xi2 o + pullDeg (κ₁ k₀) xi2 o)
    rw [hdeg, pullDeg_some, pullDeg_κ₁]
    cases o with
    | none => simp [hxi]
    | some k =>
      simp only [Option.elim, hk, Option.some.injEq]
      by_cases e : k = k₀
      · subst e; simp [hxi]
      · rw [if_neg e, if_neg (Ne.symm e)]; ring
  div_eq := hdiv

end PositivityTheory.Xgp.c_algsq
end
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap GlobalTheory.CompanionTheory.Ar.PB.CovGraph PositivityTheory.Xgp.c_algsq

noncomputable section
namespace PositivityTheory.Xgp.c_sqsys

theorem elim_gen {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] {P : Ideal (MRing ι)} {P' : Ideal (MRing ι')} {n : ℕ} (Pt : Ideal (MRing (Sum.elim ι ι')))
    (hPt : IsArithVar Pt (n + 1)) (hP : IsArithVar P (n + 1)) (h1 : imageZ inlV Pt = P) (h2 : imageZ inrV Pt = P')
    (J : Ideal (MRing ι')) (hJ : IsMultiHomogIdeal J) (hn : ¬ J ≤ P') :
    ∃ (g : MRing ι) (dg : K → ℕ), IsMultiHomog g dg ∧ g ∉ P ∧
      ∀ z w, z ∈ mcPts J → pairV w z ∈ mcPts Pt → eval w (map (Int.castRingHom ℂ) g) = 0 := by
  have hle : ¬ J.map (rename inrV : MRing ι' →ₐ[ℤ] MRing (Sum.elim ι ι')).toRingHom ≤ Pt := by
    rw [Ideal.map_le_iff_le_comap]
    intro h
    exact hn (h2 ▸ h)
  obtain ⟨g, a, hg, hgP, hv⟩ := GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.proof K ι (K ⊕ K') (Sum.elim ι ι') Sum.inl inlV Pt
    (J.map (rename inrV : MRing ι' →ₐ[ℤ] MRing (Sum.elim ι ι')).toRingHom) n isBlockMap_inl hPt
    (by rw [h1]; exact hP) (isMultiHomogIdeal_map isBlockMap_inr hJ) hle
  refine ⟨g, a, hg, h1 ▸ hgP, fun z w hzJ hzt => ?_⟩
  have := hv (pairV w z) hzt (mem_mcPts_map hzt.1 fun f hf => by
    have e : (fun p => pairV w z (inrV p)) = z := funext fun p => pairV_inr w z p
    rw [e]
    exact hzJ.2 f hf)
  have e : (fun p => pairV w z (inlV p)) = w := funext fun p => pairV_inl w z p
  rwa [e] at this

theorem pull_gen {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] {P : Ideal (MRing ι)} {P' : Ideal (MRing ι')} {n : ℕ} (Pt : Ideal (MRing (Sum.elim ι ι')))
    (hPt : IsArithVar Pt (n + 1)) (hP' : IsArithVar P' (n + 1)) (h1 : imageZ inlV Pt = P) (h2 : imageZ inrV Pt = P')
    (G : MRing ι) (a : K → ℕ) (hG : IsMultiHomog G a) (hn : G ∉ P) :
    ∃ (g : MRing ι') (dg : K' → ℕ), IsMultiHomog g dg ∧ g ∉ P' ∧
      ∀ z w, pairV w z ∈ mcPts Pt → eval w (map (Int.castRingHom ℂ) G) = 0 →
        eval z (map (Int.castRingHom ℂ) g) = 0 := by
  have hJ : IsMultiHomogIdeal (Ideal.span {G}) :=
    ⟨{G}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hG⟩, rfl⟩
  have hle : ¬ (Ideal.span {G}).map (rename inlV : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι')).toRingHom ≤ Pt := by
    rw [Ideal.map_le_iff_le_comap]
    intro h
    exact hn (h1 ▸ h (Ideal.subset_span rfl))
  obtain ⟨g, a', hg, hgP, hv⟩ := GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.proof K' ι' (K ⊕ K') (Sum.elim ι ι') Sum.inr inrV Pt
    ((Ideal.span {G}).map (rename inlV : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι')).toRingHom) n isBlockMap_inr hPt
    (by rw [h2]; exact hP') (isMultiHomogIdeal_map isBlockMap_inl hJ) hle
  refine ⟨g, a', hg, h2 ▸ hgP, fun z w hzt h0 => ?_⟩
  have := hv (pairV w z) hzt (mem_mcPts_map hzt.1 fun f hf => by
    have e : (fun p => pairV w z (inlV p)) = w := funext fun p => pairV_inl w z p
    rw [e]
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, h0, mul_zero])
  have e : (fun p => pairV w z (inrV p)) = z := funext fun p => pairV_inr w z p
  rwa [e] at this

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

variable {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {τ : Ψ} {a b : Fin N} {k₀ : K} {k₀' : K'} {ca cb : Fin N}
  {d : ℕ}

theorem exists_homog_eval_eq_zero_of_relW (Cv : FlagCover M' M) (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    (J : Ideal (MRing fun o : Option K' => ι' (o.getD k₀'))) (hJ : IsMultiHomogIdeal J)
    (hn : ¬ J ≤ mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)) :
    ∃ (g : MRing fun o : Option K => ι (o.getD k₀)) (dg : Option K → ℕ), IsMultiHomog g dg ∧
      g ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ∧
      ∀ z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)), z ∈ mcPts J →
        ∀ w ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), RelW Cv k₀ k₀' z w →
        eval w (map (Int.castRingHom ℂ) g) = 0 := by
  obtain ⟨Pt, hPt, h1, h2, h3⟩ := graph_alt Cv S S' hy hy'
  obtain ⟨g, dg, hg, hgP, hv⟩ := elim_gen Pt hPt (S.arith hy) h1 h2 J hJ hn
  exact ⟨g, dg, hg, hgP, fun z hz hzJ w hw hi => hv z w hzJ (h3 z hz w hw hi)⟩

theorem pull_alt (Cv : FlagCover M' M) (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    (G : MRing fun o : Option K => ι (o.getD k₀)) (dG : Option K → ℕ) (hG : IsMultiHomog G dG)
    (hn : G ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) :
    ∃ (g : MRing fun o : Option K' => ι' (o.getD k₀')) (dg : Option K' → ℕ), IsMultiHomog g dg ∧
      g ∉ mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X) ∧
      ∀ z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)),
        ∀ w ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), RelW Cv k₀ k₀' z w →
        eval w (map (Int.castRingHom ℂ) G) = 0 → eval z (map (Int.castRingHom ℂ) g) = 0 := by
  obtain ⟨Pt, hPt, h1, h2, h3⟩ := graph_alt Cv S S' hy hy'
  obtain ⟨g, dg, hg, hgP, hv⟩ := pull_gen Pt hPt (S'.arith hy') h1 h2 G dG hG hn
  exact ⟨g, dg, hg, hgP, fun z hz w hw hi h0 => hv z w (h3 z hz w hw hi) h0⟩

theorem sameOrbit_of_relW_relW (Cv : FlagCover M' M) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {z : (Σ o : Option K', ι' (o.getD k₀')) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)))
    {w w' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : RelW Cv k₀ k₀' z w) (h' : RelW Cv k₀ k₀' z w') :
    SameOrbit w w' :=
  sameOrbit_of_sameOrbit_fstPt_sndPt (GlobalTheory.T.flag_cover_arithmetic_second K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _ (fst_mem hz) _ _ h.1 h'.1)
    (GlobalTheory.T.flag_cover_arithmetic_second K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _ (S'.snd_mem hy' hz) _ _ h.2 h'.2)

theorem pull_form (S : Sw M τ a b k₀ ca cb) (hy : IsArithVar (mCoordIdeal y) (d + 2)) {G : MRing ι} {dG : K → ℕ}
    (hG : IsMultiHomog G dG) (hn : G ∉ mCoordIdeal y) :
    ∃ (g : MRing fun o : Option K => ι (o.getD k₀)) (dg : Option K → ℕ), IsMultiHomog g dg ∧
      g ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ∧
      ∀ w, eval w (map (Int.castRingHom ℂ) g) = eval (fstPt k₀ w) (map (Int.castRingHom ℂ) G) :=
  ⟨rename (v₀ k₀) G, _, CPts.isMultiHomog_rename_block (Pts.isBlockMap_v₀ k₀) hG,
    fun h => hn (by rw [← S.im₀ hy]; exact h), fun w => CPts.eval_rename_block _ w G⟩

theorem mapsTo_twoFlagFramesOrthogonal_of_isometry (hRes : ResExistsStatement) (Cv : FlagCover M' M) (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas (d + 2) X)
    (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (e : RW.X → X)
    (he : HoloMap RW.A A e) (hdeg : IsDegreeOff A RW.A e 1 ∅) :
    ∃ (J : Ideal (MRing fun o : Option K' => ι' (o.getD k₀')))
      (R' : AnLogRes (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)) J (d + 2)) (g : R'.X → RW.X) (br : Set X),
      HoloMap R'.A RW.A g ∧ IsDegreeOff A R'.A (e ∘ g) Cv.deg br ∧
        ∀ x, RelW Cv k₀ k₀' (R'.lift x x) (RW.lift (g x) (g x)) := by
  have hP := S.arith hy
  have hP' := S'.arith hy'
  have heinj : Function.Injective e := by
    intro u v huv
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hdeg.2.2.2.2.1 (e u) (by simp))
    have hu : u ∈ e ⁻¹' {e u} := rfl
    have hv : v ∈ e ⁻¹' {e u} := huv.symm
    rw [hc] at hu hv
    exact hu.trans hv.symm
  have hnot : ∀ z : (Σ o : Option K, ι (o.getD k₀)) → ℂ, z ∉ mcPts ⊤ := by
    intro z h
    have := h.2 1 trivial
    simp at this
  have htop : IsMultiHomogIdeal (⊤ : Ideal (MRing fun o : Option K' => ι' (o.getD k₀'))) := by
    refine ⟨{1}, fun f hf => ⟨0, ?_⟩, by simp⟩
    rw [Set.mem_singleton_iff.mp hf]
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    simp [hm]
  obtain ⟨J', -, hJ'h, hJ'n, ⟨R'⟩⟩ := hRes _ _ _ ⊤ (d + 2) hP' htop fun h => hP'.2.1.1.ne_top (top_le_iff.mp h)
  have hmem' : ∀ x, R'.lift x x ∈ mcPts _ := fun x => R'.mem x x (R'.mem_U x)
  have hmem : ∀ x, RW.lift x x ∈ mcPts _ := fun x => RW.mem x x (RW.mem_U x)
  have himg : ∀ x, ∃ x₀, RelW Cv k₀ k₀' (R'.lift x x) (RW.lift x₀ x₀) := by
    intro x
    obtain ⟨V, f, -, hzV, -, hf⟩ := local_analytic_section_coords Cv S S' hy' (hmem' x)
    obtain ⟨h1, h2⟩ := hf _ ⟨hzV, hmem' x⟩
    obtain ⟨x₀, hx⟩ := RW.surj _ h1 (hnot _)
    exact ⟨x₀, h2.orbit (Cj.sameOrbit_refl _) hx⟩
  choose g hg using himg
  have hgholo : HoloMap R'.A RW.A g := by
    refine GlobalTheory.T.log_resolution_map_locally_analytic _ _ _ _ _ ⊤ _ J' (d + 2) (d + 2) RW R' g rfl fun x => ?_
    obtain ⟨V, f, hV, hzV, hf, hff⟩ := local_analytic_section_coords Cv S S' hy' (hmem' x)
    refine ⟨V, f, hV, hzV, hf, fun z' hz' x' hx' => ?_⟩
    exact sameOrbit_of_relW_relW Cv S' hy hy' hz'.2 (hff z' hz').2 ((hg x').orbit hx' (Cj.sameOrbit_refl _))
  have hholo : HoloMap R'.A A (e ∘ g) := holoMap_comp hgholo he
  have hbase := GlobalTheory.T.flag_cover_arithmetic_third K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy'
  obtain ⟨D₁, a₁, hD₁, hD₁n, hcount⟩ := GlobalTheory.T.flag_cover_arithmetic_fourth K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy'
  obtain ⟨E₁, b₁, hE₁, hE₁n, hE₁e⟩ := GlobalTheory.T.flag_cover_arithmetic_sixth K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' D₁ a₁ hD₁ hD₁n
  obtain ⟨G₁, c₁, hG₁, hG₁n, hG₁e⟩ := pull_form S hy hE₁ hE₁n
  obtain ⟨D₂, a₂, hD₂, hD₂n, het⟩ := GlobalTheory.T.flag_cover_arithmetic_seventh K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy'
  obtain ⟨E₂, b₂, hE₂, hE₂n, hE₂e⟩ := GlobalTheory.T.flag_cover_arithmetic_sixth K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' D₂ a₂ hD₂ hD₂n
  obtain ⟨G₂, c₂, hG₂, hG₂n, hG₂e⟩ := pull_form S hy hE₂ hE₂n
  obtain ⟨G₃, c₃, hG₃, hG₃n, hG₃e⟩ := exists_homog_eval_eq_zero_of_relW Cv S S' hy hy' J' hJ'h hJ'n
  have hprime := hP.2.1.1
  have hGn : G₁ * G₂ * G₃ ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) := fun h => by
    rcases hprime.mem_or_mem h with h | h
    · rcases hprime.mem_or_mem h with h | h
      · exact hG₁n h
      · exact hG₂n h
    · exact hG₃n h
  have hGh : IsMultiHomog (G₁ * G₂ * G₃) (c₁ + c₂ + c₃) :=
    CovMap.isMultiHomog_mul (CovMap.isMultiHomog_mul hG₁ hG₂) hG₃
  obtain ⟨G₄, c₄, hG₄, hG₄n, hG₄e⟩ := pull_alt Cv S S' hy hy' _ _ hGh hGn
  have hev : ∀ w : (Σ o : Option K, ι (o.getD k₀)) → ℂ, eval w (map (Int.castRingHom ℂ) (G₁ * G₂ * G₃)) ≠ 0 →
      eval w (map (Int.castRingHom ℂ) G₁) ≠ 0 ∧ eval w (map (Int.castRingHom ℂ) G₂) ≠ 0 := by
    intro w hw
    simp only [map_mul] at hw
    exact ⟨fun h => hw (by rw [h]; simp), fun h => hw (by rw [h]; simp)⟩
  refine ⟨J', R', g, _, hgholo, GlobalTheory.T.log_resolution_compatible_pullback _ _ _ _ _ ⊤ _ J' (d + 2) X A RW e R' _ (RelW Cv k₀ k₀')
    (G₁ * G₂ * G₃) G₄ _ c₄ Cv.deg rfl hP hP' he hdeg hholo hGh hGn hG₄ hG₄n
    (fun z z₁ w w₁ h h1 h2 => h.orbit h1 h2) ?_ ?_ ?_ ?_ (fun z hz w hw hi h0 => hG₄e z hz w hw hi h0) ?_, hg⟩
  · intro x x₀ h
    rw [heinj h]
    exact hg x
  · intro x x₀ h
    rw [RW.inj x₀ (g x) (hnot _) (sameOrbit_of_relW_relW Cv S' hy hy' (hmem' x) h (hg x))]
    rfl
  · intro w hw h0
    rw [ncard_orbits_relW_eq_ncard_orbits_isImg Cv S S' hy hy' hw, GlobalTheory.T.flag_cover_arithmetic_fifth K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _ (fst_mem hw)]
    refine hcount _ (CPts.base_mem M (fst_mem hw)) ?_
    rw [← hE₁e, ← hG₁e]
    exact (hev w h0).1
  · intro z hz hzJ w hw hi
    have := hG₃e z hz hzJ w hw hi
    simp only [map_mul, this, mul_zero]
  · intro z hz w₀ hw₀ hi h0
    have hs := hbase _ (fst_mem hz) _ hi.1
    have h2 : eval (basePart M.blk (fstPt k₀ w₀)) (map (Int.castRingHom ℂ) D₂) ≠ 0 := by
      rw [← hE₂e, ← hG₂e]
      exact (hev w₀ h0).2
    obtain ⟨V, V', s, hV, hwV, hV', hbV, hs1, hs2⟩ := het _ (CPts.base_mem M' (fst_mem hz)) _ hs h2
    obtain ⟨U₀, U₀', f₀, hU₀, hw0, hU₀', hz0, hf₀, r₀⟩ := GlobalTheory.T.flag_cover_arithmetic_eighth K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _
      (fst_mem hz) _ (fst_mem hw₀) hi.1 V V' s hV hwV hV' hbV hs1 hs2
    obtain ⟨U₁, U₁', f₁, hU₁, hw1, hU₁', hz1, hf₁, r₁⟩ := GlobalTheory.T.flag_cover_arithmetic_eighth K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _
      (S'.snd_mem hy' hz) _ (S.snd_mem hy hw₀) hi.2 V V' s hV (by rw [Pts.basePart_snd M S.hk]; exact hwV) hV'
      (by rw [Pts.basePart_snd M' S'.hk]; exact hbV) hs1 hs2
    refine ⟨fstPt k₀ ⁻¹' U₀ ∩ sndPt k₀ ⁻¹' U₁, fstPt k₀' ⁻¹' U₀' ∩ sndPt k₀' ⁻¹' U₁',
      fun u => joinPt k₀' (f₀ (fstPt k₀ u)) (f₁ (sndPt k₀ u)),
      (hU₀.preimage (continuous_comp_idx _)).inter (hU₁.preimage (continuous_comp_idx _)), ⟨hw0, hw1⟩,
      (hU₀'.preimage (continuous_comp_idx _)).inter (hU₁'.preimage (continuous_comp_idx _)), ⟨hz0, hz1⟩,
      fun u hu => analytic_join k₀' ((hf₀ _ hu.1).comp (analytic_comp_idx _ u))
        ((hf₁ _ hu.2).comp (analytic_comp_idx _ u)), fun z'' hz'' w hw hr => ?_⟩
    exact join_orbit (r₀ _ ⟨hz''.1.1, fst_mem hz''.2⟩ _ ⟨hw.1.1, fst_mem hw.2⟩ hr.1)
      (r₁ _ ⟨hz''.1.2, S'.snd_mem hy' hz''.2⟩ _ ⟨hw.1.2, S.snd_mem hy hw.2⟩ hr.2)

end PositivityTheory.Xgp.c_sqsys
end
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace PositivityTheory.Xgp.c_sqsys

open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap PositivityTheory.Xgp.c_algsq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

variable {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {n d : ℕ} {BM : BaseMetric M n} {FA : FlagAn BM d}
  {Cv : FlagCover M' M}

theorem lift_inj (FA : FlagAn BM d) {x x' : FA.Re.R.X} (h : SameOrbit (FA.Re.R.lift x x) (FA.Re.R.lift x' x')) :
    x = x' :=
  FA.Re.R.inj x x' (fun h => by
    have := h.2 1 (by rw [FA.J_top]; trivial)
    simp at this) h

theorem varpi_eq (CR : CovReal FA Cv) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    (hy' : IsArithVar (mCoordIdeal y') (d + 2)) {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y'))
    {x₀ : FA.Re.R.X} (hi : IsImg Cv z (FA.Re.R.lift x₀ x₀)) : CR.ϖ z = FA.Re.π x₀ := by
  obtain ⟨x₁, hx₁⟩ := (GlobalTheory.T.flag_analytic_projection_bijective K ι Φ y Ψ N j M n d BM FA).2 (CR.ϖ z)
  have h1 : IsImg Cv z (FA.Re.R.lift x₁ x₁) := fun z₁ o F' F hF' hF hg' hg h hfl =>
    CR.flags z₁ (mem_mcPts_of_sameOrbit hy'.2.1.2.1 o hz) F' F hF' hF hg' hg h hfl x₁
      (hx₁.trans (CR.ϖ_torus z z₁ hz o).symm)
  rw [← hx₁, lift_inj FA (GlobalTheory.T.flag_cover_arithmetic_second K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' z hz _ _ h1 hi)]

theorem pot_pull (CR : CovReal FA Cv) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    (hy' : IsArithVar (mCoordIdeal y') (d + 2)) {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    {P J : Ideal (MRing ι₂)} {e : ℕ} (R : AnLogRes P J e) {κ : K' → K₂} {v : (Σ k, ι' k) → Σ k, ι₂ k}
    (hv : IsBlockMap κ v) (hP : ∀ z ∈ mcPts P, z ∘ v ∈ mcPts (mCoordIdeal y')) (g₀ : R.X → FA.Re.R.X)
    (hi : ∀ x, IsImg Cv (R.lift x x ∘ v) (FA.Re.R.lift (g₀ x) (g₀ x))) (p : Ψ × Fin N) (x : R.X) :
    LocRe R.A x fun u => Real.log ((CR.Re.ref p).h (R.lift x u ∘ v)) -
      (FA.S.th (some p)).φ (FA.Re.π (g₀ x)) (FA.Re.π (g₀ u)) := by
  have hg₀ : HoloMap R.A FA.Re.R.A g₀ := by
    refine GlobalTheory.T.log_resolution_map_locally_analytic _ _ _ _ _ _ _ _ _ _ FA.Re.R R g₀ FA.J_top fun x => ?_
    obtain ⟨V, f, hV, hzV, hf, hff⟩ := GlobalTheory.T.flag_cover_arithmetic_first K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _
      (hP _ (R.mem x x (R.mem_U x)))
    refine ⟨(fun z => z ∘ v) ⁻¹' V, fun z => f (z ∘ v), hV.preimage (continuous_comp_idx v), hzV,
      fun z hz => (hf _ hz).comp (f := fun z => z ∘ v) (analytic_comp_idx v z), fun z' hz' x' hx' => ?_⟩
    exact GlobalTheory.T.flag_cover_arithmetic_second K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _ (hP _ hz'.2) _ _ (hff _ ⟨hz'.1, hP _ hz'.2⟩).2
      ((hi x').orbit (FibreCount.comp_orbit hv hx') (Cj.sameOrbit_refl _))
  have hW : IsOpen (R.U x ∩ g₀ ⁻¹' FA.Re.R.U (g₀ x)) := (R.isOpen_U x).inter ((FA.Re.R.isOpen_U _).preimage hg₀.1)
  have L1 := pot_loc CR hy hy' (A := R.A) hW ⟨R.mem_U x, FA.Re.R.mem_U _⟩ (Z := fun u => R.lift x u ∘ v)
    (fun q => holo_mono (R.holo x (v q)) Set.inter_subset_left) (fun u hu => hP _ (R.mem x u hu.1))
    (Y := fun u => FA.Re.R.lift (g₀ x) (g₀ u))
    (fun q => holo_mono (GlobalTheory.CompanionTheory.Ar.PB.FA.BlockPot.holoOn_comp hg₀ (FA.Re.R.holo (g₀ x) q)) Set.inter_subset_right)
    (fun u hu => (FA.Re.R.mem _ _ hu.2).1)
    (fun u hu => (hi u).orbit (FibreCount.comp_orbit hv (R.compat x u u ⟨hu.1, R.mem_U u⟩))
      (FA.Re.R.compat _ _ _ ⟨hu.2, FA.Re.R.mem_U _⟩)) p
  have L2 : LocRe FA.Re.R.A (g₀ x) fun u => Real.log ((fsHerm ι (M.dy p)).h (FA.Re.R.lift (g₀ x) u)) -
      (FA.S.th (some p)).φ (FA.Re.π (g₀ x)) (FA.Re.π u) := by
    have := FA.Re.ref_pot (some p) (g₀ x) trivial
    rw [FA.ref_some] at this
    exact this
  exact (L1.add (L2.comp hg₀)).congr isOpen_univ trivial fun u _ => by ring

theorem log_comb {σ : Type} [Fintype σ] (A : σ → HermLine ι) (ε : σ → ℤ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : Real.log ((combLine A ε).h z) = ∑ p, (ε p : ℝ) * Real.log ((A p).h z) := by
  rw [combLine_h, Real.log_prod fun p _ => zpow_ne_zero _ ((A p).pos z hz).ne']
  simp only [Real.log_zpow]

end PositivityTheory.Xgp.c_sqsys

open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap PositivityTheory.Xgp.c_algsq PositivityTheory.Xgp.c_sqsys GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter in
theorem PositivityTheory.Xgp.t_c_sqsys : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (CR : CovReal FA Cv), IsArithVar (mCoordIdeal y) (d + 2) → ∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → Nonempty (SqSys CR.Re (τ, a) (xiCoef τ a)) := by
  intro hI K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA K' _ ι' _ Φ' _ y' M' Cv CR hy τ a b hb hab
  have hy' : IsArithVar (mCoordIdeal y') (d + 2) := CR.Re.arith
  obtain ⟨k₀, ca, cb, hk, hca, hcb, -, -, -⟩ := PositivityTheory.Xgp.t_c_swap K ι Φ y Ψ N j M τ a b hb hab
  obtain ⟨k₀', ca', cb', hk', hca', hcb', -, hxi', hdy'⟩ := PositivityTheory.Xgp.t_c_swap K' ι' Φ' y' Ψ N j M' τ a b hb hab
  obtain rfl : ca = ca' := Fin.ext (hca.trans hca'.symm)
  obtain rfl : cb = cb' := Fin.ext (hcb.trans hcb'.symm)
  have S : Sw M τ a b k₀ ca cb := ⟨hb, hab, hk, hca, hcb, PositivityTheory.Xgp.t_c_w_arith⟩
  have S' : Sw M' τ a b k₀' ca cb := ⟨hb, hab, hk', hca, hcb, PositivityTheory.Xgp.t_c_w_arith⟩
  obtain ⟨Q, RW, e, he, hde, hq0, hq1, -, hnorm⟩ :=
    GlobalTheory.T.flag_adjacent_swap_square_system hI K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hab hk hca hcb hy
  obtain ⟨g, h, dg, dh, hg, hh, hgn, hhn, hdeg, hq, hdiv⟩ :=
    PositivityTheory.Xgp.t_c_w_sec K' ι' Φ' y' Ψ N j M' d τ a b k₀' ca cb hb hab hk' hca hcb hy'
  have LC := PositivityTheory.Xgp.c_algsq.lc K' ι' Φ' y' Ψ N j M' d τ a b k₀' ca cb hb hab hk' hca hcb hy' g h dg dh hg hh hdeg hq
  obtain ⟨J, R', γ, br, hγ, hdegW, hrel⟩ := mapsTo_twoFlagFramesOrthogonal_of_isometry hI.2.1.1 Cv S S' hy hy' Q.SW.A RW e he hde
  have hxi : ∑ p, xiCoef τ a p * (CR.Re.ref p).a k₀' = -2 := by simpa only [CR.ref_deg] using hxi'
  have hdeg₁ : ∀ o : Option K', (dg o : ℤ) - dh o = o.elim 1 fun k => -(combLine CR.Re.ref (xiCoef τ a)).a k -
      (if M'.blk (τ, a) = some k then 1 else 0) := by simpa only [combLine_a, CR.ref_deg] using hdeg
  have hdeg₂ : ∀ o : Option K', (dg o : ℤ) - dh o =
      o.elim 1 fun k => -(∑ p, xiCoef τ a p * (CR.Re.ref p).a k) - if k₀' = k then 1 else 0 := by
    simpa only [combLine_a, hk', Option.some.injEq] using hdeg₁
  have hv₀ := Pts.isBlockMap_v₀ (ι := ι') k₀'
  have hv₁ := isBlockMap_v₁ (ι := ι') k₀'
  have hsurj := (GlobalTheory.T.flag_analytic_projection_bijective K ι Φ y Ψ N j M n d BM FA).2
  have o₀ : ∀ x x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x)) := hq0
  have o₁ : ∀ x x₀, FA.Re.π x₀ = Q.q 1 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x)) := by
    intro x x₀ hx
    obtain ⟨z₁, h1, h2, h3⟩ := hq1 x x₀ hx
    have : z₁ = sndPt k₀ (RW.lift x x) := by
      funext ⟨k, m⟩
      by_cases ek : k = k₀
      · subst ek
        rw [h3, Pts.snd_self]
      · rw [h2 ⟨k, m⟩ ek, Pts.snd_fst_ne ek]
        rfl
    exact this ▸ h1
  choose g₀ hg₀ using fun x => hsurj (Q.q 0 (e (γ x)))
  choose g₁ hg₁ using fun x => hsurj (Q.q 1 (e (γ x)))
  have i₀ : ∀ x, IsImg Cv (fstPt k₀' (R'.lift x x)) (FA.Re.R.lift (g₀ x) (g₀ x)) := fun x =>
    (hrel x).1.orbit (Cj.sameOrbit_refl _) (o₀ _ _ (hg₀ x))
  have i₁ : ∀ x, IsImg Cv (sndPt k₀' (R'.lift x x)) (FA.Re.R.lift (g₁ x) (g₁ x)) := fun x =>
    (hrel x).2.orbit (Cj.sameOrbit_refl _) (o₁ _ _ (hg₁ x))
  have mem : ∀ x, R'.lift x x ∈ mcPts _ := fun x => R'.mem x x (R'.mem_U x)
  have m₀ := fun x => fst_mem (mem x)
  have m₁ := fun x => S'.snd_mem hy' (mem x)
  have w₀ : ∀ x, CR.ϖ (fstPt k₀' (R'.lift x x)) = Q.q 0 (e (γ x)) := fun x =>
    (varpi_eq CR hy hy' (m₀ x) (i₀ x)).trans (hg₀ x)
  have w₁ : ∀ x, CR.ϖ (sndPt k₀' (R'.lift x x)) = Q.q 1 (e (γ x)) := fun x =>
    (varpi_eq CR hy hy' (m₁ x) (i₁ x)).trans (hg₁ x)
  have hπ : HoloMap R'.A Q.SW.A (e ∘ γ) := holoMap_comp hγ he
  let ReW : Realis Q.SW (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)) :=
    { arith := S'.arith hy'
      J := J
      R := R'
      π := e ∘ γ
      holo := hπ
      deg := CR.Re.deg
      deg_pos := CR.Re.deg_pos
      br := br
      degree := by rw [CR.deg_eq]; exact hdegW
      ref := fun o => o.elim (pullHerm hv₁ (CR.Re.ref (τ, a))) fun p => pullHerm hv₀ (CR.Re.ref p)
      ref_smooth := fun o => by
        cases o with
        | none =>
          exact SqFirst.isSmoothHerm_of_pull hv₁ (CR.Re.ref_smooth _)
            (isPullHerm_pullHerm hv₁ _)
        | some p =>
          exact SqFirst.isSmoothHerm_of_pull hv₀ (CR.Re.ref_smooth _)
            (isPullHerm_pullHerm hv₀ _)
      ref_pot := fun o x _ => by
        cases o with
        | none =>
          have L1 := pot_pull CR hy hy' R' hv₁ (fun z hz => S'.snd_mem hy' hz) g₁ i₁ (τ, a) x
          have L2 := LocRe.comp hπ (show LocRe Q.SW.A ((e ∘ γ) x) _ from Q.th1 _ trivial)
          simp only [hg₁] at L1
          exact (L1.sub L2).congr isOpen_univ trivial fun u _ => by
            show _ - _ = _ - _ - (_ - _)
            exact (sub_sub_sub_cancel_right _ _ _).symm
        | some p =>
          have L1 := pot_pull CR hy hy' R' hv₀ (fun z hz => fst_mem hz) g₀ i₀ p x
          have L2 := LocRe.comp hπ (show LocRe Q.SW.A ((e ∘ γ) x) _ from Q.th0 p _ trivial)
          simp only [hg₀] at L1
          exact (L1.sub L2).congr isOpen_univ trivial fun u _ => by
            show _ - _ = _ - _ - (_ - _)
            exact (sub_sub_sub_cancel_right _ _ _).symm
      line := fun o t => o.elim (pullHerm hv₁ (CR.Re.line (τ, a) t)) fun p => pullHerm hv₀ (CR.Re.line p t)
      line_deg := fun o t => by
        cases o with
        | none => exact congrArg (pullDeg _) (CR.Re.line_deg _ t)
        | some p => exact congrArg (pullDeg _) (CR.Re.line_deg _ t)
      line_smooth := fun o t h0 h1 => by
        cases o with
        | none =>
          exact SqFirst.isSmoothHerm_of_pull hv₁ (CR.Re.line_smooth _ t h0 (h1.trans Q.t₀_le))
            (isPullHerm_pullHerm hv₁ _)
        | some p =>
          exact SqFirst.isSmoothHerm_of_pull hv₀ (CR.Re.line_smooth _ t h0 (h1.trans Q.t₀_le))
            (isPullHerm_pullHerm hv₀ _)
      line_eq := fun o t h0 h1 x => by
        cases o with
        | none =>
          have := CR.line_pt (τ, a) t h0 (h1.trans Q.t₀_le) _ (m₁ x)
          rw [w₁] at this
          rw [Q.phase_none_eq_comp_second_projection]
          exact this
        | some p =>
          have := CR.line_pt p t h0 (h1.trans Q.t₀_le) _ (m₀ x)
          rw [w₀] at this
          rw [Q.phase_some_eq_comp_first_projection]
          exact this }
  refine ⟨⟨k₀', Q, mkAlg M' hb hab hk' hca hcb hy' _ hxi g h dg dh hg hh hgn hhn hdeg₁ hdiv, ReW, rfl, ?_,
    fun p t => isPullHerm_pullHerm hv₀ _, fun t => isPullHerm_pullHerm hv₁ _,
    {x | eval (R'.lift x x) (map (Int.castRingHom ℂ) (g * h)) = 0}, ?_, ?_⟩⟩
  · intro p hp t
    refine ⟨by rw [CR.Re.line_deg, CR.ref_deg]; exact hdy' p hp, fun z z' hzz => CR.step p t z z' ?_ ?_⟩
    · exact funext fun q => hzz _ fun e => q.1.2 (τ, a) (hk'.trans (congrArg some e.symm))
    · exact fun k hk m => hzz _ fun e => hp (M'.blk_inj _ _ k hk (hk'.trans (congrArg some e.symm)))
  · exact HilbertSamuel.AnResNullForm.proof HilbertSamuel.NonvanishingDense.full _ _ _ _ _ R'.toAnRes (g * h) _
      (S'.arith hy') (CovMap.isMultiHomog_mul hg hh) fun hm => ((S'.arith hy').2.1.1.mem_or_mem hm).elim hgn hhn
  · intro t h0 h1 x hx
    have hx' : eval (R'.lift x x) (map (Int.castRingHom ℂ) g) * eval (R'.lift x x) (map (Int.castRingHom ℂ) h) ≠ 0 := by
      rw [← map_mul, ← map_mul]; exact hx
    have g0 := left_ne_zero_of_mul hx'
    have h0' := right_ne_zero_of_mul hx'
    obtain ⟨z₀, z₁, F, hm, s, hF, hG, oz₀, oz₁, hmb, hmd, hs, ex₀, ex₁, heq⟩ := norm_pt CR S' hy' hg hh hxi hdeg₂ LC
      (mem x) g0 h0' (fst_mem (RW.mem _ _ (RW.mem_U (γ x)))) (S.snd_mem hy (RW.mem _ _ (RW.mem_U (γ x))))
      (hrel x).1 (hrel x).2
    have hn : _ = normRhs M τ a F z₀ z₁ hm s := hnorm (γ x) z₀ z₁ F hm s hF hG
      (fun x₀ h => orbit_trans (o₀ _ _ h) (orbit_symm oz₀))
      (fun x₀ h => orbit_trans (o₁ _ _ h) (orbit_symm oz₁)) hmb hmd hs ex₀ ex₁
    show Real.log (‖eval (R'.lift x x) (map (Int.castRingHom ℂ) g)‖ / ‖eval (R'.lift x x) (map (Int.castRingHom ℂ) h)‖) +
      (Real.log ((combLine (fun p => CR.Re.line p t) (xiCoef τ a)).h (fstPt k₀' (R'.lift x x))) +
        Real.log ((combLine (fun p => CR.Re.line p t) (xiCoef τ a)).h (sndPt k₀' (R'.lift x x)))) / 2 =
      logNormSec Q.L' Q.v (e (γ x)) + Q.cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) *
        (FA.S.phT (some p) t (Q.q 0 (e (γ x))) + FA.S.phT (some p) t (Q.q 1 (e (γ x))))
    rw [hn, ← heq, lognorm, Real.log_div (norm_ne_zero_iff.2 g0) (norm_ne_zero_iff.2 h0'), log_comb _ _ (m₀ x).1,
      log_comb _ _ (m₁ x).1]
    simp only [fun p => CR.line_pt p t h0 (h1.trans Q.t₀_le) _ (m₀ x),
      fun p => CR.line_pt p t h0 (h1.trans Q.t₀_le) _ (m₁ x), w₀, w₁, mul_add, Finset.sum_add_distrib]
    ring
end
end
