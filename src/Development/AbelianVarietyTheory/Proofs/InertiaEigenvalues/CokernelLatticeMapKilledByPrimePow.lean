import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMemA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEn
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicMonodromyPolynomialsRaiseDegree
import Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse
import Formalism.PadicSubsetSums.StableGradedCounts.LagrangeBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumericalConditionsTheoremTLargePrimeStatement

section
section
open scoped PowerSeries Pointwise

namespace GlobalTheory.FrobIdealDeg

open PowerSeries

variable {O : Type} [CommRing O] (l : ℕ) (hl : 2 ≤ l) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧)
  (hφ : ∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) =
    if l ∣ m then PowerSeries.coeff (m / l) f else 0)

noncomputable def comps (f : O⟦X⟧) : Fin l → O⟦X⟧ :=
  (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl φ hφ f).exists.choose

include hφ in
lemma comps_spec (f : O⟦X⟧) :
    f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (comps l hl φ hφ f j) :=
  (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl φ hφ f).exists.choose_spec

lemma comps_eq {f : O⟦X⟧} {c : Fin l → O⟦X⟧}
    (h : f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (c j)) : comps l hl φ hφ f = c :=
  (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl φ hφ f).unique (comps_spec l hl φ hφ f) h

lemma comps_add (f f' : O⟦X⟧) :
    comps l hl φ hφ (f + f') = comps l hl φ hφ f + comps l hl φ hφ f' := by
  apply comps_eq
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  rw [← comps_spec l hl φ hφ f, ← comps_spec l hl φ hφ f']

lemma comps_zero : comps l hl φ hφ (0 : O⟦X⟧) = 0 := by
  apply comps_eq
  simp

lemma comps_mul_phi (c f : O⟦X⟧) (k : Fin l) :
    comps l hl φ hφ (φ c * f) k = c * comps l hl φ hφ f k := by
  have : comps l hl φ hφ (φ c * f) = fun k => c * comps l hl φ hφ f k := by
    apply comps_eq
    conv_lhs => rw [comps_spec l hl φ hφ f]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring
  rw [this]

include hl hφ in
lemma phi_X : φ PowerSeries.X = PowerSeries.X ^ l := by
  ext m
  rw [hφ, PowerSeries.coeff_X_pow]
  by_cases h1 : l ∣ m
  · obtain ⟨q, rfl⟩ := h1
    rw [if_pos (dvd_mul_right l q), Nat.mul_div_cancel_left q (by omega), PowerSeries.coeff_X]
    by_cases hq : q = 1
    · subst hq; simp
    · rw [if_neg hq, if_neg]
      intro h2
      apply hq
      have : l * q = l * 1 := by simpa using h2
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
  · rw [if_neg h1, if_neg]
    rintro rfl
    exact h1 dvd_rfl

lemma comps_X_pow (t : ℕ) :
    comps l hl φ hφ (PowerSeries.X ^ t) ⟨t % l, Nat.mod_lt _ (Nat.lt_of_lt_of_le (by norm_num) hl)⟩ =
      PowerSeries.X ^ (t / l) := by
  have : comps l hl φ hφ (PowerSeries.X ^ t) = fun j =>
      if j = (⟨t % l, Nat.mod_lt _ (Nat.lt_of_lt_of_le (by norm_num) hl)⟩ : Fin l) then PowerSeries.X ^ (t / l) else 0 := by
    apply comps_eq
    simp only [apply_ite φ, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [map_pow, phi_X l hl φ hφ, ← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [this]; simp

lemma descend (J : Ideal O⟦X⟧) (b : ℕ) (f : O⟦X⟧)
    (hf : f ∈ J.map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b}) (k : Fin l) :
    comps l hl φ hφ f k ∈ J ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  clear hf
  rw [comps_add, Pi.add_apply]
  refine Submodule.add_mem_sup ?_ ?_
  · have key : ∀ r : O⟦X⟧, comps l hl φ hφ (r * x) k ∈ J := by
      change x ∈ Submodule.span O⟦X⟧ (φ '' (J : Set O⟦X⟧)) at hx
      induction hx using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨j, hj, rfl⟩ := hz
        intro r
        rw [mul_comm, comps_mul_phi]
        exact J.mul_mem_right _ hj
      | zero =>
        intro r
        rw [mul_zero, comps_zero]
        exact J.zero_mem
      | add z w _ _ hz hw =>
        intro r
        rw [mul_add, comps_add, Pi.add_apply]
        exact J.add_mem (hz r) (hw r)
      | smul s z _ hz =>
        intro r
        rw [smul_eq_mul, ← mul_assoc]
        exact hz (r * s)
    simpa using key 1
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e : c * (l : O⟦X⟧) ^ b = φ ((l : O⟦X⟧) ^ b) * c := by
      rw [map_pow, map_natCast, mul_comm]
    rw [e, comps_mul_phi]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

lemma pow_mem_binom (e h b : ℕ) (hb : 1 ≤ b) :
    (PowerSeries.X : O⟦X⟧) ^ (e * (h + b - 1)) ∈
      Ideal.span {(PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h} ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  have : (PowerSeries.X : O⟦X⟧) ^ (e * (h + b - 1)) =
      ((PowerSeries.X ^ e + (l : O⟦X⟧)) + (-(l : O⟦X⟧))) ^ (h + b - 1) := by
    rw [pow_mul]; congr 1; ring
  rw [this]
  apply Ideal.add_pow_mem_of_pow_mem_of_le (m := h) (n := b)
  · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  · rw [neg_pow]
    exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  · omega

end GlobalTheory.FrobIdealDeg

namespace GlobalTheory

open GlobalTheory.FrobIdealDeg in

theorem frobenius_ideal_degree_bound : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l →
    ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) =
      if l ∣ m then PowerSeries.coeff (m / l) f else 0) →
    ∀ (a e h b : ℕ) [NeZero a] (I : ZMod a → Ideal O⟦X⟧), 1 ≤ b → h + b ≤ l →
    (∀ τ, ∃ s : ℕ, PowerSeries.X ^ s ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b}) →
    (∀ τ, ∀ x ∈ I τ, (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h * x ∈ (I (τ - 1)).map φ) →
    ∀ τ, (PowerSeries.X : O⟦X⟧) ^ (e * (h + b)) ∈ (I τ).map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  intro O _ l hl φ hφ a e h b _ I hb hhb hs hI
  classical
  have step : ∀ τ t, (PowerSeries.X : O⟦X⟧) ^ t ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} →
      (PowerSeries.X : O⟦X⟧) ^ (t + e * (h + b - 1)) ∈
        (I (τ - 1)).map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
    intro τ t ht
    have hK := pow_mem_binom (O := O) l e h b hb
    obtain ⟨r1, hr1, r2, hr2, hr⟩ := Submodule.mem_sup.mp hK
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ht
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr1
    rw [pow_add, ← hxy, ← hr]
    have hring : (x + y) * (c * (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h + r2) =
        c * ((PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h * x) +
          (y * (c * (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h + r2) + x * r2) := by ring
    rw [hring]
    exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (hI τ x hx))
      (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hy) (Ideal.mul_mem_left _ _ hr2))
  let s : ZMod a → ℕ := fun τ => Nat.find (hs τ)
  have hspec : ∀ τ, (PowerSeries.X : O⟦X⟧) ^ s τ ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} :=
    fun τ => Nat.find_spec (hs τ)
  have down : ∀ τ, l * s τ ≤ s (τ + 1) + e * (h + b - 1) := by
    intro τ
    have h1 := step (τ + 1) (s (τ + 1)) (hspec (τ + 1))
    rw [add_sub_cancel_right] at h1
    have h2 := descend l hl φ hφ (I τ) b _ h1 ⟨(s (τ + 1) + e * (h + b - 1)) % l,
      Nat.mod_lt _ (by omega)⟩
    rw [comps_X_pow] at h2
    have h3 : s τ ≤ (s (τ + 1) + e * (h + b - 1)) / l := Nat.find_min' _ h2
    calc l * s τ ≤ l * ((s (τ + 1) + e * (h + b - 1)) / l) := Nat.mul_le_mul_left _ h3
      _ ≤ s (τ + 1) + e * (h + b - 1) := Nat.mul_div_le _ _
  obtain ⟨τ0, -, hmax⟩ := Finset.exists_max_image Finset.univ s Finset.univ_nonempty
  obtain ⟨n, hn⟩ : ∃ n, h + b - 1 = n := ⟨_, rfl⟩
  have hnl : n + 1 ≤ l := by omega
  have hS : s τ0 ≤ e := by
    have d := down τ0
    have m := hmax (τ0 + 1) (Finset.mem_univ _)
    rw [hn] at d
    by_contra hc
    push_neg at hc
    nlinarith
  intro τ
  have h1 := step (τ + 1) (s (τ + 1)) (hspec (τ + 1))
  rw [add_sub_cancel_right] at h1
  refine Ideal.pow_mem_of_pow_mem _ h1 ?_
  have m := hmax (τ + 1) (Finset.mem_univ _)
  have : e * (h + b) = e * (h + b - 1) + e := by
    rw [← Nat.mul_add_one]; congr 1; omega
  omega

end GlobalTheory
end

open scoped PowerSeries Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_pow_mem_map_sup_span_pow_of_frobenius_bound : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l → ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0) → ∀ (a e h b : ℕ) [NeZero a] (I : ZMod a → Ideal O⟦X⟧), 1 ≤ b → h + b ≤ l → (∀ τ, ∃ s : ℕ, PowerSeries.X ^ s ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b}) → (∀ τ, ∀ x ∈ I τ, (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h * x ∈ (I (τ - 1)).map φ) → ∀ τ, (PowerSeries.X : O⟦X⟧) ^ (e * (h + b)) ∈ (I τ).map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  atlas_forward_decl GlobalTheory.frobenius_ideal_degree_bound
end

section
section
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.UPow

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem isUnit_one_add_mul_uIn (f : A O K) : IsUnit (1 + f * uIn (A O K)) := by
  set g := (equivA O K).symm (1 + f * uIn (A O K))
  have hg : equivA O K g = 1 + f * uIn (A O K) := by simp [g]
  have hc : constantCoeff g = 1 := by
    apply IsUnitBall.inj (O := O) (K := K)
    have h1 := congrArg (fun x : A O K => constantCoeff (x : K⟦X⟧)) hg
    simp only [coe_equivA] at h1
    rw [map_one]
    have h2 : algebraMap O K (constantCoeff g) = constantCoeff ((PowerSeries.map (algebraMap O K)) g) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_map]
    rw [h2, h1]
    simp
  have hu : IsUnit g := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hc]
    exact isUnit_one
  rw [← hg]
  exact hu.map (equivA O K)

theorem exists_uIn_pow_smul_eq_zero : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (M : Type) [AddCommGroup M] [Module (A O K) M], IsFiniteLength (A O K) M →
    ∃ n : ℕ, ∀ x : M, (uIn (A O K)) ^ n • x = 0 := by
  intro O K _ _ _ _ _ M _ _ hM
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hM
  set I : Ideal (A O K) := Ideal.span {uIn (A O K)}
  let F : ℕ →o (Submodule (A O K) M)ᵒᵈ :=
    ⟨fun k => OrderDual.toDual (I ^ k • (⊤ : Submodule (A O K) M)), fun i j hij =>
      Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes F
  have hstab : I ^ n • (⊤ : Submodule (A O K) M) = I • (I ^ n • (⊤ : Submodule (A O K) M)) := by
    have : I ^ n • (⊤ : Submodule (A O K) M) = I ^ (n + 1) • (⊤ : Submodule (A O K) M) :=
      OrderDual.toDual_inj.1 (hn (n + 1) (Nat.le_succ n))
    rw [← Submodule.mul_smul, ← pow_succ', ← this]
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
    (I ^ n • (⊤ : Submodule (A O K) M)) (IsNoetherian.noetherian _) hstab.le
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1 hr
  have hru : IsUnit r := by
    have : r = 1 + f * uIn (A O K) := by rw [hf]; ring
    rw [this]
    exact isUnit_one_add_mul_uIn f
  refine ⟨n, fun x => ?_⟩
  have hmem : (uIn (A O K)) ^ n • x ∈ I ^ n • (⊤ : Submodule (A O K) M) :=
    Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) trivial
  have h0 := hr0 _ hmem
  obtain ⟨v, rfl⟩ := hru
  have := congrArg (fun y => ((v⁻¹ : (A O K)ˣ) : A O K) • y) h0
  simpa [smul_smul] using this

end GlobalTheory.UPow
end

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variable_pow_smul_eq_zero_of_finiteLength : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (M : Type) [AddCommGroup M] [Module (A O K) M], IsFiniteLength (A O K) M → ∃ n : ℕ, ∀ x : M, (uIn (A O K)) ^ n • x = 0 := by
  atlas_forward_decl GlobalTheory.UPow.exists_uIn_pow_smul_eq_zero
end

section
section
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.LiftCoker

theorem colon_map_expand_le : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    (colon O K G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) ≤ colon O K (G.map (frob K l)) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G
  rw [Ideal.map_le_iff_le_comap]
  intro α hα
  rw [Ideal.mem_comap, mem_colon]
  intro w hw
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hf : ∀ i, ∃ f : O⟦X⟧, PowerSeries.map (algebraMap O K) f = w i := fun i => by
    obtain ⟨f, hf⟩ := (equivA O K).surjective ⟨w i, hw i⟩
    exact ⟨f, by rw [← coe_equivA, hf]⟩
  choose f hf using hf
  have hdec := fun i => (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)
    (fun g m => PowerSeries.coeff_expand _ _ g) (f i)).exists
  choose g hg using hdec
  have hα' := fun j : Fin l => (mem_colon.1 hα) (fun i => PowerSeries.map (algebraMap O K) (g i j))
    (fun i => map_mem_A _)
  choose m hm hmeq using hα'
  have hX : (X : K⟦X⟧) ∈ A O K := by simpa using map_mem_A (O := O) (K := K) X
  refine ⟨∑ j : Fin l, (X : K⟦X⟧) ^ j.val • frobV l (m j), fun i => ?_, ?_⟩
  · rw [Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, frobV_apply]
    exact mul_mem (pow_mem hX _) (frob_mem_A l (hm j i))
  · funext i
    have hwi : w i = ∑ j : Fin l, (X : K⟦X⟧) ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g i j)) := by
      rw [← hf i, hg i, map_sum]
      simp [map_mul, map_pow, map_X, map_expand, frob]
    have key : ∀ j : Fin l, frob K l (PowerSeries.map (algebraMap O K) α) *
        frob K l (PowerSeries.map (algebraMap O K) (g i j)) = (G.map (frob K l) *ᵥ frobV l (m j)) i := by
      intro j
      rw [← map_mul]
      have := congrFun (hmeq j) i
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      exact RingHom.map_mulVec (frob K l).toRingHom G (m j) i
    rw [Pi.smul_apply, smul_eq_mul, map_expand, hwi, Finset.mul_sum, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← key j]
    simp only [frob]
    ring

end GlobalTheory.LiftCoker
end

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colonIdeal_map_expand_le_frobenius : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧), (colon O K G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) ≤ colon O K (G.map (frob K l)) := by
  atlas_forward_decl GlobalTheory.LiftCoker.colon_map_expand_le
end

section
section
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

noncomputable section

namespace GlobalTheory.LiftCoker

theorem map_decomp_frob {O K : Type} [CommRing O] [NormedField K] [Algebra O K] (l : ℕ) [Fact l.Prime]
    {f : O⟦X⟧} {g : Fin l → O⟦X⟧}
    (h : f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j)) :
    PowerSeries.map (algebraMap O K) f =
      ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g j)) := by
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, map_X, map_expand]
  rfl

theorem colon_map_frob_le : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    colon O K (G.map (frob K l)) ≤
      (colon O K G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G β hβ
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have decO : ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧,
      f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j) :=
    GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 _ (fun f m => coeff_expand _ _ f)
  have uniqK : ∀ f : K⟦X⟧, ∃! g : Fin l → K⟦X⟧, f = ∑ j : Fin l, X ^ j.val * frob K l (g j) :=
    GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (frob K l) (fun f m => coeff_frob l f m)
  obtain ⟨b, hb, -⟩ := decO β
  have hbK := map_decomp_frob (K := K) l hb
  have key : ∀ j, b j ∈ colon O K G := by
    intro j w hw
    obtain ⟨M, hM, hMeq⟩ := hβ (frobV l w) (fun i => frob_mem_A l (hw i))
    have lift : ∀ k, ∃ μ : O⟦X⟧, PowerSeries.map (algebraMap O K) μ = M k := fun k => by
      obtain ⟨μ, hμ⟩ := (equivA O K).surjective ⟨M k, hM k⟩
      exact ⟨μ, by rw [← coe_equivA, hμ]⟩
    choose μ hμ using lift
    choose c hc using fun k => (decO (μ k)).exists
    have hMk : ∀ k, M k = ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (c k j)) :=
      fun k => by rw [← hμ k]; exact map_decomp_frob l (hc k)
    refine ⟨fun k => PowerSeries.map (algebraMap O K) (c k j), fun k => map_mem_A _, ?_⟩
    funext i
    have e1 := congrFun hMeq i
    simp only [Pi.smul_apply, smul_eq_mul, frobV_apply] at e1
    obtain ⟨g, -, hg⟩ := uniqK (PowerSeries.map (algebraMap O K) β * frob K l (w i))
    have E1 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (b j) * w i) := by
      rw [hbK, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_assoc]
    have E2 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val *
          frob K l ((G *ᵥ fun k => PowerSeries.map (algebraMap O K) (c k j)) i) := by
      rw [e1]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hMk, Finset.mul_sum, map_sum, map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have h1 := hg _ E1
    have h2 := hg _ E2
    rw [Pi.smul_apply, smul_eq_mul]
    exact (congrFun h1 j).trans (congrFun h2 j).symm

  rw [hb]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (key j))

end GlobalTheory.LiftCoker
end
end

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colonIdeal_frobenius_le_map_expand : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧), colon O K (G.map (frob K l)) ≤ (colon O K G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) := by
  atlas_forward_decl GlobalTheory.LiftCoker.colon_map_frob_le
end

section
section
noncomputable section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.LiftCoker

theorem E_pow_mul_mem_colon_frob (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ)
    (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (τ : ZMod a) :
    ∀ α ∈ colon O K (F.mat τ),
      (X ^ e + (l : O⟦X⟧)) ^ (H + η) * α ∈ colon O K ((F.mat (τ - 1)).map (frob K l)) := by
  intro α hα w hw
  set x := D₂.mx τ *ᵥ w with hxdef
  have hx : x ∈ D₂.Lcomp τ := D₂.mem_extc.2 ⟨w, hw, rfl⟩
  have hxL : (Pi.single τ x : Vec K a κ) ∈ D₂.L := mem_tot.2 fun σ => by
    by_cases h : σ = τ
    · subst h
      simpa using hx
    · simp [h, zero_mem]
  have hup := mem_tot.1 (D₂.upper _ hxL) τ
  simp only [Pi.smul_apply, Pi.single_eq_same] at hup
  obtain ⟨m, hm, hαm⟩ := hα (E K l e ^ η • x) hup
  have hmM : (Pi.single τ m : Vec K a ι) ∈ D₁.M := mem_tot.2 fun σ => by
    by_cases h : σ = τ
    · subst h
      rw [Pi.single_eq_same]
      exact hm
    · simp [h, zero_mem]
  have hlow := mem_tot.1 (D₁.lower _ hmM) τ
  simp only [Pi.smul_apply, Pi.single_eq_same] at hlow
  obtain ⟨m', hm', hm'eq⟩ := D₁.mem_extc.1 hlow
  have hE : PowerSeries.map (algebraMap O K) ((X ^ e + (l : O⟦X⟧)) ^ (H + η) * α) =
      E K l e ^ (H + η) * PowerSeries.map (algebraMap O K) α := by
    simp [E, map_X, map_natCast]
  refine ⟨m', hm', ?_⟩
  · have key : D₂.mx τ *ᵥ (PowerSeries.map (algebraMap O K) ((X ^ e + (l : O⟦X⟧)) ^ (H + η) * α) • w) =
        D₂.mx τ *ᵥ ((F.mat (τ - 1)).map (frob K l) *ᵥ m') := by
      rw [Matrix.mulVec_smul, ← hxdef, hE, pow_add,
        show E K l e ^ H * E K l e ^ η * PowerSeries.map (algebraMap O K) α =
          E K l e ^ H * (PowerSeries.map (algebraMap O K) α * E K l e ^ η) by ring,
        mul_smul, mul_smul, hαm,
        ← Matrix.mulVec_smul, hm'eq, Matrix.mulVec_mulVec, F.comm, ← Matrix.mulVec_mulVec]
    have := congrArg (fun v => D₂.mxInv τ *ᵥ v) key
    rwa [Matrix.mulVec_mulVec (M := D₂.mxInv τ) (N := D₂.mx τ),
      Matrix.mulVec_mulVec (M := D₂.mxInv τ) (N := D₂.mx τ), PhiMod.mxInv_mul_mx,
      Matrix.one_mulVec, Matrix.one_mulVec] at this

end GlobalTheory.LiftCoker
end
end

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_pow_mul_mem_colonIdeal_frobenius : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (τ : ZMod a), ∀ α ∈ colon O K (F.mat τ), (X ^ e + (l : O⟦X⟧)) ^ (H + η) * α ∈ colon O K ((F.mat (τ - 1)).map (frob K l)) := by
  atlas_forward_decl GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob
end

section
section
noncomputable section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

theorem GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), IsFiniteLength (A O K) F.coker → ∀ b : ℕ, 1 ≤ b → H + η + b ≤ l → ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ (H + η + b) • x = F.app y + (l : K) ^ b • z := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F hfin b hb hlb x hx
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_variable_pow_smul_eq_zero_of_finiteLength O K _ hfin
  have hX : ∀ τ, (X : O⟦X⟧) ^ n ∈ colon O K (F.mat τ) := by
    intro τ w hw
    have hW : (Pi.single τ w : Vec K a κ) ∈ D₂.M := mem_tot.2 fun σ i => by
      by_cases h : σ = τ
      · subst h; simpa using hw i
      · simp [h]
    have h1 := hn (Submodule.Quotient.mk ⟨_, hW⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap] at h1
    obtain ⟨m, hm, hm'⟩ := h1
    refine ⟨m τ, fun j => mem_tot.1 hm τ j, ?_⟩
    have h2 := congrFun hm' τ
    simp only [LinearMap.restrictScalars_apply, BK.Hom.app_apply] at h2
    rw [h2]
    simp [Submodule.coe_smul, Subalgebra.smul_def]
  have key := GlobalTheory.T.X_pow_mem_map_sup_span_pow_of_frobenius_bound (O := O) l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)
    (fun f m => PowerSeries.coeff_expand _ _ f) a e (H + η) b (fun τ => colon O K (F.mat τ)) hb hlb
    (fun τ => ⟨n, Ideal.mem_sup_left (hX τ)⟩)
    (fun τ α hα => GlobalTheory.T.colonIdeal_frobenius_le_map_expand O K l ι κ _ (GlobalTheory.T.eisenstein_pow_mul_mem_colonIdeal_frobenius O K l e a ι κ η H D₁ D₂ F τ α hα))
  have comp : ∀ τ, ∀ w : κ → K⟦X⟧, (∀ i, w i ∈ A O K) → ∃ m : ι → K⟦X⟧, (∀ j, m j ∈ A O K) ∧
      ∃ w' : κ → K⟦X⟧, (∀ i, w' i ∈ A O K) ∧
        ((X : K⟦X⟧) ^ e) ^ (H + η + b) • w = (F.mat (τ - 1)).map (frob K l) *ᵥ m + (l : K⟦X⟧) ^ b • w' := by
    intro τ w hw
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (key (τ - 1))
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hq
    obtain ⟨m, hm, hmeq⟩ := GlobalTheory.T.colonIdeal_map_expand_le_frobenius O K l ι κ _ hp w hw
    refine ⟨m, hm, PowerSeries.map (algebraMap O K) c • w, fun i => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]
      exact mul_mem (map_mem_A c) (hw i)
    · have h3 := congrArg (PowerSeries.map (algebraMap O K)) hpq
      rw [map_add, map_mul, map_pow, map_pow, map_X, map_natCast] at h3
      rw [← pow_mul, ← h3, add_smul, hmeq, smul_smul, mul_comm]
  choose w hw hxw using fun τ => D₂.mem_extc.1 (mem_tot.1 hx τ)
  choose m hm w' hw' hmw using fun τ => comp τ (w τ) (hw τ)
  refine ⟨fun τ => D₁.mx τ *ᵥ m τ, mem_tot.2 fun τ => D₁.mem_extc.2 ⟨m τ, hm τ, rfl⟩,
    fun τ => D₂.mx τ *ᵥ w' τ, mem_tot.2 fun τ => D₂.mem_extc.2 ⟨w' τ, hw' τ, rfl⟩, ?_⟩
  funext τ
  have hsm : ∀ v : κ → K⟦X⟧, (l : K) ^ b • v = (l : K⟦X⟧) ^ b • v := fun v => by
    rw [← algebraMap_smul K⟦X⟧ ((l : K) ^ b) v, map_pow, map_natCast]
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hsm, BK.Hom.app_apply, Matrix.mulVec_mulVec,
    F.comm τ, hxw τ, ← Matrix.mulVec_smul, hmw τ, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec]
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), IsFiniteLength (A O K) F.coker → ∀ b : ℕ, 1 ≤ b → H + η + b ≤ l → ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ (H + η + b) • x = F.app y + (l : K) ^ b • z := by
  atlas_forward_decl GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds in

theorem degrees_eq_image_pairs {e : ℕ} (Sig : Finset (ZMod e)) (c : ZMod e) (m m' : ℕ) :
    degrees Sig c m m' =
      ((Sig.image fun s => (c - s).val) ×ˢ Finset.Ico m m').image (fun p : ℕ × ℕ => p.1 + p.2 * e) := by
  ext i
  simp only [degrees, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨s, n, ⟨hs, hn⟩, rfl⟩
    exact ⟨(c - s).val, n, ⟨⟨s, hs, rfl⟩, hn⟩, rfl⟩
  · rintro ⟨x, n, ⟨⟨s, hs, rfl⟩, hn⟩, rfl⟩
    exact ⟨s, n, ⟨hs, hn⟩, rfl⟩

theorem add_mul_inj_of_lt {e x y n m : ℕ} (hx : x < e) (hy : y < e) (h : x + n * e = y + m * e) :
    x = y ∧ n = m := by
  have h1 : (x + n * e) % e = x := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have h2 : (y + m * e) % e = y := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  have hxy : x = y := by rw [← h1, ← h2, h]
  subst hxy
  have he : 0 < e := lt_of_le_of_lt (Nat.zero_le _) hx
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right he (by omega)⟩

end GlobalTheory

namespace GlobalTheory

theorem exists_period_dvd {l e a : ℕ} (ha : 1 ≤ a) (he : e + 1 = l ^ a) [NeZero e]
    (Sig : Finset (ZMod e)) (c : ZMod e) {s s' : ZMod e} (hs : s ∈ Sig) (hs' : s' ∈ Sig) :
    ∃ ρ, 1 ≤ ρ ∧ ρ ≤ GlobalTheory.BK.maxPeriod l Sig ∧
      ((l : ℤ) ^ a - 1) ∣ ((((c - s).val : ℕ) : ℤ) - (((c - s').val : ℕ) : ℤ)) * ((l : ℤ) ^ ρ - 1) := by
  have hla : ((l : ZMod e)) ^ a = 1 := by
    have h := congrArg (Nat.cast : ℕ → ZMod e) he
    push_cast at h
    rw [ZMod.natCast_self, zero_add] at h
    exact h.symm
  have hper : Function.IsPeriodicPt (fun x : ZMod e => (l : ZMod e) * x) a (s' - s) := by
    show (fun x : ZMod e => (l : ZMod e) * x)^[a] (s' - s) = s' - s
    rw [mul_left_iterate, hla]; exact one_mul _
  refine ⟨GlobalTheory.BK.frobPeriod l (s' - s), hper.minimalPeriod_pos (by omega), ?_, ?_⟩
  · exact Finset.le_sup (f := fun p : ZMod e × ZMod e => GlobalTheory.BK.frobPeriod l (p.1 - p.2)) (b := (s', s))
      (Finset.mem_product.2 ⟨hs', hs⟩)
  · have hE : ((l : ℤ) ^ a - 1) = (e : ℤ) := by
      have : (e : ℤ) + 1 = (l : ℤ) ^ a := by exact_mod_cast he
      linarith
    rw [hE, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hfix : (fun x : ZMod e => (l : ZMod e) * x)^[GlobalTheory.BK.frobPeriod l (s' - s)] (s' - s) = s' - s :=
      Function.iterate_minimalPeriod
    rw [mul_left_iterate] at hfix
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination hfix

end GlobalTheory

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds GlobalTheory.BK in

theorem lagrange_C_rho_eq_comb_degrees : ∀ (l e a : ℕ) [Fact l.Prime], 1 ≤ a → e + 1 = l ^ a →
    ∀ (Sig : Finset (ZMod e)) (c : ZMod e) (A' N : ℕ), Sig.card ≤ N → 2 * A' + 2 < l →
    ∃ α β : Polynomial ℤ_[l], Polynomial.C ((l : ℤ_[l]) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) =
      α * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A').map (Int.castRingHom ℤ_[l]) +
        β * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A').map (Int.castRingHom ℤ_[l]) := by
  intro l e a _ ha he Sig c A' N hN hA
  have hl : l.Prime := Fact.out
  have hl2 := hl.two_le
  have hepos : 0 < e := by
    have : l ≤ l ^ a := Nat.le_self_pow (by omega) l
    omega
  have : NeZero e := ⟨by omega⟩
  have hE : ((l : ℤ) ^ a - 1) = (e : ℤ) := by
    have : (e : ℤ) + 1 = (l : ℤ) ^ a := by exact_mod_cast he
    linarith
  set Cc : Finset ℕ := Sig.image fun s => (c - s).val with hCc
  have hCclt : ∀ x ∈ Cc, x < e := by
    intro x hx
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hx
    exact ZMod.val_lt _
  have hD₁ : D₁ Sig c A' = (Cc ×ˢ Finset.Ico 0 A').image (fun p : ℕ × ℕ => p.1 + p.2 * e) :=
    degrees_eq_image_pairs Sig c 0 A'
  have hD₂ : D₂ Sig c A' = (Cc ×ˢ Finset.Ico A' (2 * A')).image (fun p : ℕ × ℕ => p.1 + p.2 * e) :=
    degrees_eq_image_pairs Sig c A' (2 * A')
  have hmap : ∀ T : Finset ℕ, (rootPoly T).map (Int.castRingHom ℤ_[l]) =
      ∏ i ∈ T.image (Nat.cast : ℕ → ℤ), (Polynomial.X - Polynomial.C ((i : ℤ) : ℤ_[l])) := by
    intro T
    rw [Finset.prod_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
    simp [rootPoly, Polynomial.map_prod]
  set Z₁ : Finset ℤ := (D₁ Sig c A').image (Nat.cast : ℕ → ℤ) with hZ₁
  set Z₂ : Finset ℤ := (D₂ Sig c A').image (Nat.cast : ℕ → ℤ) with hZ₂
  have hdisj : Disjoint Z₁ Z₂ := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.1 hi1
    obtain ⟨i₂, hi₂, heq⟩ := Finset.mem_image.1 hi2
    have heq' : i₂ = i₁ := by exact_mod_cast heq
    subst heq'
    rw [hD₁] at hi₁
    rw [hD₂] at hi₂
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 hi₁
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 hi₂
    rw [Finset.mem_product, Finset.mem_Ico] at hp hq
    have := add_mul_inj_of_lt (hCclt _ hp.1) (hCclt _ hq.1) (hpe.trans hqe.symm)
    omega
  have hlt : ∀ x ∈ Cc, x < l ^ a - 1 := fun x hx => by have := hCclt x hx; omega
  have hper : ∀ x ∈ Cc, ∀ y ∈ Cc, x ≠ y → ∃ ρ, 1 ≤ ρ ∧ ρ ≤ maxPeriod l Sig ∧
      ((l : ℤ) ^ a - 1) ∣ ((x : ℤ) - y) * ((l : ℤ) ^ ρ - 1) := by
    intro x hx y hy _
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 hy
    exact exists_period_dvd ha he Sig c hs hs'
  have hU : Z₁ ∪ Z₂ = ((Cc ×ˢ Finset.range (2 * A')).image
      (fun p : ℕ × ℕ => p.1 + p.2 * e)).image (Nat.cast : ℕ → ℤ) := by
    rw [hZ₁, hZ₂, ← Finset.image_union, hD₁, hD₂, ← Finset.image_union, ← Finset.product_union]
    congr 3
    ext n
    simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]
    omega
  have hbound : ∀ i ∈ Z₁, (∑ j ∈ Z₂, padicValInt l (i - j)) +
      ∑ j ∈ Z₁.erase i, padicValInt l (i - j) ≤ rho l Sig N := by
    intro i hi
    rw [Finset.sum_erase _ (by simp), add_comm, ← Finset.sum_union hdisj, hU,
      Finset.sum_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
    rw [Finset.sum_image (fun p hp q hq hpq => by
      rw [Finset.mem_coe, Finset.mem_product] at hp hq
      have := add_mul_inj_of_lt (hCclt _ hp.1) (hCclt _ hq.1) hpq
      exact Prod.ext this.1 this.2), Finset.sum_product]
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hi
    rw [hD₁] at hi₀
    obtain ⟨⟨x, n⟩, hxn, rfl⟩ := Finset.mem_image.1 hi₀
    rw [Finset.mem_product, Finset.mem_Ico] at hxn
    have LB := Formalism.IrreducibleCountingLemmas.WindowSums.sumPadicValDifferencesLe l a A' (maxPeriod l Sig) Cc hl ha (by omega) hlt
      hper x hxn.1 n hxn.2.2
    rw [hE] at LB
    refine le_trans (le_of_eq ?_) (LB.trans ?_)
    · refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun m _ => ?_
      split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc
        simp
      · push_cast
        rfl
    · have hcard : Cc.card ≤ N := Finset.card_image_le.trans hN
      unfold rho
      calc (Cc.card - 1) * maxPeriod l Sig ≤ (N - 1) * maxPeriod l Sig :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 * (N - 1) * maxPeriod l Sig := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1
    (Formalism.IrreducibleCountingLemmas.WindowSums.lagrange_resolvent_T l Z₁ Z₂ (rho l Sig N) hdisj hbound)
  refine ⟨α, β, ?_⟩
  rw [← hαβ, P₁, P₂, hmap, hmap]

end GlobalTheory
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrange_prime_pow_mem_isotypicDegreePoly_span : ∀ (l e a : ℕ) [Fact l.Prime], 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (c : ZMod e) (A' N : ℕ), Sig.card ≤ N → 2 * A' + 2 < l → ∃ α β : Polynomial ℤ_[l], Polynomial.C ((l : ℤ_[l]) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) = α * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A').map (Int.castRingHom ℤ_[l]) + β * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A').map (Int.castRingHom ℤ_[l]) := by
  atlas_forward_decl GlobalTheory.lagrange_C_rho_eq_comb_degrees
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.PowKill

theorem exists_pow_smul_eq_zero {R : Type} [CommRing R] {x : R}
    (hx : ∀ I : Ideal R, I.IsMaximal → x ∈ I) {M : Type} [AddCommGroup M] [Module R M]
    (h : IsFiniteLength R M) : ∃ m : ℕ, ∀ q : M, (x ^ m) • q = 0 := by
  induction h with
  | of_subsingleton => exact ⟨0, fun q => Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
    refine ⟨m + 1, fun q => ?_⟩
    have h1 : x • q ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      apply e.injective
      obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective I (e (Submodule.Quotient.mk q))
      rw [map_smul, ← hr, map_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul]
      exact I.mul_mem_right r (hx I hI)
    have h2 := hm ⟨x • q, h1⟩
    rw [pow_succ, mul_smul]
    exact congrArg Subtype.val h2

section

variable {O : Type} [CommRing O] (l : ℕ) [Fact l.Prime]

theorem isUnit_l_mul_add_one (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (c : O) : IsUnit ((l : O) * c + 1) := by
  set u := algebraMap O K ((l : O) * c + 1) with hu
  have hlc : ‖(l : K) * algebraMap O K c‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (norm_algebraMap_le c))
      (norm_l_lt_one (K := K) l)
  have hu1 : ‖u‖ = 1 := by
    have : u = (l : K) * algebraMap O K c + 1 := by simp [hu]
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlc.ne)]
    rw [norm_one]; exact max_eq_right hlc.le
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
  obtain ⟨b, hb⟩ := (IsUnitBall.mem_range_iff (O := O) (u⁻¹)).2 (by rw [norm_inv, hu1, inv_one])
  refine isUnit_iff_exists_inv.2 ⟨b, IsUnitBall.inj (O := O) (K := K) ?_⟩
  rw [map_mul, hb, ← hu, mul_inv_cancel₀ hu0, map_one]

theorem l_mem_maximal {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (I : Ideal (A O K)) (hI : I.IsMaximal) : (l : A O K) ∈ I := by
  have hj : (l : A O K) ∈ Ideal.jacobson (⊥ : Ideal (A O K)) := by
    rw [Ideal.mem_jacobson_bot]
    intro y
    have key : IsUnit ((equivA O K).symm ((l : A O K) * y + 1)) := by
      rw [map_add, map_mul, map_natCast, map_one, PowerSeries.isUnit_iff_constantCoeff, map_add,
        map_mul, map_natCast, map_one]
      exact isUnit_l_mul_add_one l K _
    simpa using key.map (equivA O K).toRingEquiv.toRingHom
  have hle : Ideal.jacobson (⊥ : Ideal (A O K)) ≤ I := by
    rw [Ideal.jacobson]; exact sInf_le ⟨bot_le, hI⟩
  exact hle hj

end

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (Mo : Type) [AddCommGroup Mo]
    [Module (A O K) Mo], IsFiniteLength (A O K) Mo → ∃ m : ℕ, ∀ q : Mo, ((l : A O K) ^ m) • q = 0 :=
  fun O K _ _ _ _ _ l _ _ _ _ _ h => exists_pow_smul_eq_zero (l_mem_maximal (K := K) l) h

end GlobalTheory.PowKill
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_kills_finiteLength_integralPowerSeries : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (Mo : Type) [AddCommGroup Mo] [Module (A O K) Mo], IsFiniteLength (A O K) Mo → ∃ m : ℕ, ∀ q : Mo, ((l : A O K) ^ m) • q = 0 := by
  atlas_forward_decl GlobalTheory.PowKill.main
end

section
section
noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

omit [NeZero e] in

theorem act_inertia_diagScale {P : PhiMod O K l e a ι} (Δ : Descent P) (ξ : rootsOfUnity e K)
    (s : ZMod a → K) (w : Vec K a ι) :
    Δ.act (TameGal.inertia ξ) (diagScale K a ι s w) =
      diagScale K a ι s (Δ.act (TameGal.inertia ξ) w) := by
  have h1 (u : Vec K a ι) : diagScale K a ι s u = (fun τ => (C (s τ) : K⟦X⟧)) • u := by
    ext τ i : 2
    simp [diagScale_apply, smul_eq_C_mul]
  have h2 : ringAct (TameGal.inertia ξ : TameGal K l e a) (fun τ => (C (s τ) : K⟦X⟧)) =
      fun τ => C (s τ) := by
    ext τ n
    rw [ringAct_apply, TameGal.shift_inertia, sub_zero, coeff_rescale, coeff_C]
    split_ifs with h <;> simp [h]
  rw [h1, h1, Δ.act_smul_tot, h2]

theorem isoProj_mem_isotypic {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e)
    (v : Vec K a ι) : isoProj Δ c v ∈ Δ.isotypic c := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  unfold isoProj
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  intro ξ τ
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, act_inertia_diagScale,
    Finset.sum_apply, diagScale_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft ξ) _ _ fun ζ => ?_
  rw [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, ← map_mul, smul_smul]
  congr 1
  rw [map_mul, TameGal.root_mul, TameGal.shift_inertia, sub_zero, ← mul_pow, mul_inv,
    mul_inv_cancel_left₀ (TameGal.root_ne_zero _ _)]

theorem isoProj_mem_isotypic' : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι)
    (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), GlobalTheory.CokerL.isoProj Δ c v ∈ Δ.isotypic c :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Δ c v => isoProj_mem_isotypic Δ c v

end GlobalTheory.CokerL
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), GlobalTheory.CokerL.isoProj Δ c v ∈ Δ.isotypic c := by
  atlas_forward_decl GlobalTheory.CokerL.isoProj_mem_isotypic'
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

theorem sum_zmod_val_eq_sum_range {M : Type} [AddCommMonoid M] (e : ℕ) [NeZero e] (f : ℕ → M) :
    ∑ c : ZMod e, f c.val = ∑ i ∈ Finset.range e, f i := by
  refine Finset.sum_bij (fun c _ => c.val) (fun c _ => Finset.mem_range.2 (ZMod.val_lt c))
    (fun c _ d _ h => ZMod.val_injective e h) (fun i hi => ?_) (fun _ _ => rfl)
  exact ⟨(i : ZMod e), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.1 hi)⟩

theorem sum_zmod_pow_eq_zero {K : Type} [Field K] (e : ℕ) [NeZero e] {r : K} (hr : r ^ e = 1)
    (h1 : r ≠ 1) : ∑ c : ZMod e, r ^ c.val = 0 := by
  rw [sum_zmod_val_eq_sum_range e (fun i => r ^ i), geom_sum_eq h1, hr, sub_self, zero_div]

theorem root_inertia_ne_one {K : Type} [NormedField K] {l e a : ℕ} [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] {ζ : rootsOfUnity e K} (h : ζ ≠ 1)
    (τ : ZMod a) : (TameGal.inertia ζ : TameGal K l e a).root τ ≠ 1 := by
  intro h1
  apply h
  have h2 : powL l (-τ) ζ = 1 := Subtype.ext (Units.ext h1)
  have h3 := powL_add l τ (-τ) ζ
  rw [h2, map_one, add_neg_cancel, powL_zero] at h3
  exact h3

theorem sum_isoProj : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι)
    (Δ : Descent P) (v : Vec K a ι), ∑ c : ZMod e, GlobalTheory.CokerL.isoProj Δ c v = v := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ P Δ v
  letI := Fintype.ofFinite (rootsOfUnity e K)
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have he : (e : K) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne e)
  simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  classical
  rw [Finset.sum_eq_single (1 : rootsOfUnity e K)]
  · ext1 τ
    simp only [map_one, TameGal.root_one, inv_one, one_pow, Pi.smul_apply, Finset.sum_apply,
      diagScale_apply, one_smul, Module.End.one_apply, Finset.sum_const, Finset.card_univ, ZMod.card]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ he, one_smul]
  · intro ζ _ hζ
    ext1 τ
    simp only [Finset.sum_apply, diagScale_apply, Pi.zero_apply]
    rw [← Finset.sum_smul, sum_zmod_pow_eq_zero e (by rw [inv_pow, TameGal.root_pow, inv_one])
      (fun h => root_inertia_ne_one hζ τ (inv_eq_one.1 h)), zero_smul]
  · simp

end GlobalTheory.CokerL
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_isotypicProjectors_eq_id : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (v : Vec K a ι), ∑ c : ZMod e, GlobalTheory.CokerL.isoProj Δ c v = v := by
  atlas_forward_decl GlobalTheory.CokerL.sum_isoProj
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

theorem isoProj_mem_L : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), v ∈ P.L → GlobalTheory.CokerL.isoProj Δ c v ∈ P.L := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ P Δ c v hv
  letI := Fintype.ofFinite (rootsOfUnity e K)
  have key : ∀ s : ZMod a → K, (∀ τ, ‖s τ‖ ≤ 1) → ∀ w ∈ P.L, diagScale K a ι s w ∈ P.L := by
    intro s hs w hw
    have h : diagScale K a ι s w = (fun τ => C (s τ)) • w := by
      ext τ i
      simp [diagScale_apply, Pi.smul_apply', PowerSeries.smul_eq_C_mul]
    rw [h]
    refine P.smul_tot_mem_ext (fun τ => mem_A.2 fun n => ?_) hw
    rw [coeff_C]
    split_ifs
    · exact hs τ
    · simp
  have hnd : ¬ l ∣ e := by
    intro h
    have h1 : l ∣ e + 1 := by
      rw [TameDescentExponentData.succ_eq (K := K) (l := l) (e := e) (a := a)]
      exact dvd_pow_self l (NeZero.ne a)
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h1))
  have he : ‖(e : K)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_natCast_eq l, Padic.norm_natCast_eq_one_iff.2
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd), inv_one]
  have hsc : isoProj Δ c v = diagScale K a ι (fun _ => (e : K)⁻¹) (∑ ζ : rootsOfUnity e K,
      diagScale K a ι (fun τ => ((TameGal.inertia ζ : TameGal K l e a).root τ)⁻¹ ^ c.val)
        (Δ.act (TameGal.inertia ζ) v)) := by
    simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  rw [hsc]
  refine key _ (fun _ => he) _ (Submodule.sum_mem _ fun ζ _ => key _ (fun τ => ?_) _ ?_)
  · rw [norm_pow, norm_inv, TameGal.norm_root, inv_one, one_pow]
  · exact Δ.act_mem_ext _ le_rfl rot_A hv

end GlobalTheory.CokerL
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), v ∈ P.L → GlobalTheory.CokerL.isoProj Δ c v ∈ P.L := by
  atlas_forward_decl GlobalTheory.CokerL.isoProj_mem_L
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

open Matrix

theorem inv_mul_coeff_eq_of_X_pow_mul {K : Type} [Field K] {N : ℕ} {c : K} (hc : c ≠ 0)
    {f g : K⟦X⟧} (h : X ^ N * f = c • g) (k : ℕ) : c⁻¹ * coeff k f = coeff (k + N) g := by
  have := congrArg (coeff (k + N)) h
  rw [coeff_X_pow_mul, coeff_smul, smul_eq_mul] at this
  rw [this, inv_mul_cancel_left₀ hc]

theorem mem_lpow_L_of_vpow_smul (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (n b : ℕ) (w z : Vec K a ι) (hw : w ∈ P.L)
    (hz : z ∈ P.L) (h : ((X : K⟦X⟧) ^ e) ^ n • w = (l : K) ^ b • z) :
    ∃ z' ∈ P.L, w = (l : K) ^ b • z' := by
  have hc : (l : K) ^ b ≠ 0 := pow_ne_zero _ (l_ne_zero l)
  refine ⟨((l : K) ^ b)⁻¹ • w, mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => ?_,
    (smul_inv_smul₀ hc w).symm⟩
  have hm := P.mem_extc_iff.1 (mem_tot.1 hw τ)
  have hm' := P.mem_extc_iff.1 (mem_tot.1 hz τ)
  have hi : X ^ (e * n) * (P.mxInv τ *ᵥ w τ) i = (l : K) ^ b • (P.mxInv τ *ᵥ z τ) i := by
    have hτ := congrArg (fun v : Vec K a ι => (P.mxInv τ *ᵥ v τ) i) h
    simp only [Pi.smul_apply, Matrix.mulVec_smul, smul_eq_mul] at hτ
    rw [pow_mul]
    exact hτ
  rw [mem_A]
  intro k
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, coeff_smul, smul_eq_mul,
    inv_mul_coeff_eq_of_X_pow_mul hc hi]
  exact mem_A.1 (hm' i) _

end GlobalTheory.CokerL
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_prime_pow_lattice_of_X_pow_smul_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (n b : ℕ) (w z : Vec K a ι), w ∈ P.L → z ∈ P.L → ((X : K⟦X⟧) ^ e) ^ n • w = (l : K) ^ b • z → ∃ z' ∈ P.L, w = (l : K) ^ b • z' := by
  atlas_forward_decl GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL.Tconn

theorem N_vpow {K : Type} [NormedField K] (e A' : ℕ) :
    N K (((X : K⟦X⟧) ^ e) ^ A') = ((e * A' : ℕ) : K⟦X⟧) * ((X : K⟦X⟧) ^ e) ^ A' := by
  ext n
  rw [coeff_N, ← pow_mul, ← map_natCast (C (R := K)), coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h; simp
  · simp

theorem N_lpow {K : Type} [NormedField K] (l b : ℕ) : N K ((l : K⟦X⟧) ^ b) = 0 := by
  rw [← Nat.cast_pow]; exact Derivation.map_natCast _ _

theorem part_top {K O κ : Type} {a : ℕ} [NormedField K] [CommRing O] [Algebra O K]
    (V : Submodule O (Vec K a κ)) : GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ V = V := by
  ext v; simp [GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part]

end GlobalTheory.CokerL.Tconn

theorem GlobalTheory.CokerL.Tsub_conn : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (A' b : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Reduction O K l e a → ∀ x ∈ GlobalTheory.CokerL.Tsub F A' b, D₂.conn x ∈ GlobalTheory.CokerL.Tsub F A' b := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F A' b hred x hx
  have hIS := (hred.2.2 ι κ η H D₁ D₂ F).2.1
  have hMH := (hred.2.1 κ η H D₂).1
  have hvS : ((X : K⟦X⟧) ^ e) ^ A' ∈ S O K e := pow_mem (pow_mem HasU.X_mem e) A'
  have hHigh : ∀ (f : K⟦X⟧), f ∈ S O K e → ∀ q ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod,
      f • q ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod := fun f hf q hq =>
    (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • D₂.MM).smul_mem (⟨f, hf⟩ : S O K e) hq
  have hnat : ∀ (n : ℕ) (q : Vec K a κ) (V : Submodule O (Vec K a κ)), q ∈ V → ((n : K⟦X⟧)) • q ∈ V :=
    fun n q V hq => by
      rw [Nat.cast_smul_eq_nsmul]; exact V.nsmul_mem hq n
  obtain ⟨x12, h12, x3, h3, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨x1, h1, x2, h2, rfl⟩ := Submodule.mem_sup.1 h12
  rw [map_add, map_add]
  refine add_mem (add_mem ?_ ?_) ?_
  · obtain ⟨y, hy, rfl⟩ := h1
    change D₂.toPhiMod.conn (((X : K⟦X⟧) ^ e) ^ A' • y) ∈ _
    rw [PhiMod.conn_smul, GlobalTheory.CokerL.Tconn.N_vpow, mul_smul]
    refine add_mem ?_ ?_
    · have : ((e * A' : ℕ) : K⟦X⟧) • y ∈ (F.imL.restrictScalars O) := hnat _ _ _ hy
      rw [smul_comm]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, this, rfl⟩)
    · have hc := hIS y (by
        rw [GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top]
        exact Submodule.mem_sup_left hy)
      rw [GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top] at hc
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hc
      rw [← hpq, smul_add]
      exact add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨p, hp, rfl⟩))
        (Submodule.mem_sup_right (hHigh _ hvS q hq))
  · obtain ⟨z, hz, rfl⟩ := h2
    change D₂.toPhiMod.conn (((l : K⟦X⟧) ^ b) • z) ∈ _
    rw [PhiMod.conn_smul, GlobalTheory.CokerL.Tconn.N_lpow, zero_smul, zero_add]
    have hzM : z ∈ D₂.MM := PhiMod.ext_mono _ (A_le_S l e) hz
    have hc : D₂.conn z ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O) := by
      rw [GlobalTheory.CokerL.Tconn.part_top]
      exact BKDat.conn_mem_MM D₂ hzM
    rw [hMH.MM_eq, GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top] at hc
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hc
    change (l : K⟦X⟧) ^ b • D₂.toPhiMod.conn z ∈ _
    rw [← hpq, smul_add]
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨p, hp, rfl⟩)) ?_
    refine Submodule.mem_sup_right ?_
    rw [← Nat.cast_pow]
    exact hnat _ _ _ hq
  · have := hMH.conn_high x3 (by rw [GlobalTheory.CokerL.Tconn.part_top]; exact h3)
    rw [GlobalTheory.CokerL.Tconn.part_top] at this
    exact Submodule.mem_sup_right this
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerDerivation_preserves_breuilKisin_sum_submodule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (A' b : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Reduction O K l e a → ∀ x ∈ GlobalTheory.CokerL.Tsub F A' b, D₂.conn x ∈ GlobalTheory.CokerL.Tsub F A' b := by
  atlas_forward_decl GlobalTheory.CokerL.Tsub_conn
end

section
section
noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

theorem aeval_mem_of_stable {O K V : Type} [CommRing O] [NormedField K] [Algebra O K] [IsUnitBall O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (W : Submodule O V)
    (T : Module.End K V) (hT : ∀ x ∈ W, T x ∈ W) (p : Polynomial K) (hp : ∀ n, ‖p.coeff n‖ ≤ 1) :
    ∀ x ∈ W, Polynomial.aeval T p x ∈ W := by
  intro x hx
  have hpow : ∀ n : ℕ, (T ^ n) x ∈ W := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hT _ ih
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O) (p.coeff i)).2 (hp i)
  rw [LinearMap.smul_apply, ← hc, algebraMap_smul]
  exact W.smul_mem c (hpow i)

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]

theorem app_aeval {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (p : Polynomial K)
    (v : Vec K a ι) : F.app (Polynomial.aeval P.conn p v) = Polynomial.aeval Q.conn p (F.app v) := by
  have hpow : ∀ (n : ℕ) (v : Vec K a ι), F.app ((P.conn ^ n) v) = (Q.conn ^ n) (F.app v) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      simp only [pow_succ', Module.End.mul_apply]
      rw [F.app_conn, ih]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply,
    LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.map_smul_of_tower, hpow]

theorem app_mem_MMHigh [NormedAlgebra ℚ_[l] K] [NeZero e] {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q)
    {h : Vec K a ι} (hh : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh P) : F.app h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh Q := by
  change h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • P.MM at hh
  change F.app h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • Q.MM
  refine Submodule.smul_induction_on hh (fun s hs m hm => ?_) (fun x y hx hy => ?_)
  · rw [LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem_smul hs (F.app_mem_ext (A_le_S l e) hm)
  · rw [map_add]
    exact add_mem hx hy

end GlobalTheory.CokerL

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

theorem isotypic_step : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (N : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H → (∀ τ, D₁.desc.chars τ ⊆ (Sig : Set (ZMod e))) → (∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))) → IsFiniteLength (A O K) F.coker → ∀ c : ZMod e, ∀ x ∈ D₂.L, (l : K) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N • isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ (H + η + (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N + 1)) • x) ∈ Tsub F (H + η + (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N + 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F Sig U N hB h₁ h₂ hfl c x hx
  set ρ := GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N with hρ
  set b := ρ + 1 with hb
  set A' := H + η + b with hA'
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (NeZero.ne a)
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  have horb := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a (Fact.out : l.Prime) ha he Sig N hB.frob_mem hB.zero_mem_Sig
    hB.card_Sig hB.two_le
  have hnum := GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hB.two_le hB.one_le hB.lt horb.2.1 hB.large
  have hA'l : 2 * A' + 2 < l := by
    have : A' = H + η + 2 * (N - 1) * maxPeriod l Sig + 1 := by
      simp only [hA', hb, hρ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho]; ring
    rw [this]; exact hnum.1
  have hred := GlobalTheory.T.monodromy_reduction_modulo_high_degree O K l e a
  have hdeg := GlobalTheory.T.isotypic_monodromy_polynomials_raise_degree O K l e a
  obtain ⟨α, β, hαβ⟩ := GlobalTheory.T.lagrange_prime_pow_mem_isotypicDegreePoly_span l e a ha he Sig c A' N hB.card_Sig hA'l

  have hlpow : ∀ (n : ℕ) (v : Vec K a κ), (l : K) ^ n • v = (l ^ n) • v := fun n v => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul K]
  have hlpow' : ∀ (n : ℕ) (v : Vec K a κ), (l : K⟦X⟧) ^ n • v = (l : K) ^ n • v := fun n v => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul K⟦X⟧, hlpow]
  have hvA : ∀ n : ℕ, ((X : K⟦X⟧) ^ e) ^ n ∈ A O K := fun n =>
    pow_mem (pow_mem (HasU.X_mem (B := A O K)) e) n
  have vmemL : ∀ n : ℕ, ∀ v ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ n • v ∈ D₂.L := fun n v hv =>
    D₂.L.smul_mem (⟨_, hvA n⟩ : A O K) hv

  set T := Tsub F A' b with hT
  have memT1 : ∀ y ∈ D₁.L, ((X : K⟦X⟧) ^ e) ^ A' • F.app y ∈ T := fun y hy =>
    Submodule.mem_sup_left (Submodule.mem_sup_left ⟨F.app y, ⟨y, hy, rfl⟩, rfl⟩)
  have memT2 : ∀ z ∈ D₂.L, (l : K) ^ b • z ∈ T := fun z hz =>
    Submodule.mem_sup_left (Submodule.mem_sup_right ⟨z, hz, by simp [hlpow']⟩)
  have memT3 : ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod, h ∈ T := fun h hh =>
    Submodule.mem_sup_right hh
  have hTc : ∀ w ∈ T, D₂.conn w ∈ T := GlobalTheory.T.eulerDerivation_preserves_breuilKisin_sum_submodule O K l e a ι κ η H D₁ D₂ F A' b hred

  have a3 := GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel O K l e a ι κ η H D₁ D₂ F hfl b (by omega) (by omega)
  obtain ⟨y₀, hy₀, z₀, hz₀, h3⟩ := a3 x hx
  have hyd : isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x) =
      F.app (isoProj D₁.desc c y₀) + (l : K) ^ b • isoProj D₂.desc c z₀ := by
    rw [h3, map_add, map_smul, app_isoProj]
  have hy_iso := GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit O K l e a κ D₂.toPhiMod D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x)
  have hy_v : isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.vL D₂.toPhiMod A' := by
    rw [isoProj_vpow]
    exact ⟨_, GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice O K l e a κ D₂.toPhiMod D₂.desc c x hx, rfl⟩
  have hy₁L := GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice O K l e a ι D₁.toPhiMod D₁.desc c y₀ hy₀
  have hy₁iso := GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit O K l e a ι D₁.toPhiMod D₁.desc c y₀
  have hz₁L := GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice O K l e a κ D₂.toPhiMod D₂.desc c z₀ hz₀
  set y := isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x) with hy

  let φ : ℤ_[l] →+* K := (algebraMap ℚ_[l] K).comp PadicInt.Coe.ringHom
  have hφ : ∀ t, ‖φ t‖ ≤ 1 := fun t => by
    simp only [φ, RingHom.comp_apply, norm_algebraMap']
    exact PadicInt.norm_le_one t
  have hPZ : ∀ p : Polynomial ℤ, (p.map (Int.castRingHom ℤ_[l])).map φ = p.map (Int.castRingHom K) := by
    intro p
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hZ : ∀ (p : Polynomial ℤ), ∀ (m : ℕ), ‖(p.map (Int.castRingHom K)).coeff m‖ ≤ 1 := by
    intro p m
    rw [Polynomial.coeff_map, eq_intCast]
    exact IsUltrametricDist.norm_intCast_le_one K _
  have haeZ : ∀ {μ : Type} [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a μ) (p : Polynomial ℤ)
      (v : Vec K a μ), Polynomial.aeval P.conn p v = Polynomial.aeval P.conn (p.map (Int.castRingHom K)) v := by
    intro μ _ _ P p v
    rw [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]
  have key : (l : K) ^ ρ • y =
      Polynomial.aeval D₂.conn (α.map φ)
          (Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A') y) +
        Polynomial.aeval D₂.conn (β.map φ)
          (Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A') y) := by
    have h1 := congrArg (Polynomial.map φ) hαβ
    rw [Polynomial.map_C, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hPZ, hPZ] at h1
    have h2 := congrArg (fun p => Polynomial.aeval D₂.conn p y) h1
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply, map_pow, map_natCast] at h2
    simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply] at h2
    rw [h2, haeZ, haeZ]

  have hA : Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A') y ∈ T := by
    rw [haeZ, hyd, map_add, map_smul, ← app_aeval, ← haeZ]
    refine add_mem ?_ ?_
    · have hr := ((hdeg Sig c A' (by omega)).2 ι η H D₁ h₁).aeval₁ _ ⟨hy₁L, hy₁iso⟩
      obtain ⟨u, hu, h, hh, hsum⟩ := Submodule.mem_sup.1 hr
      rw [← hsum, map_add]
      obtain ⟨w, hw, rfl⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_mulL.1 hu
      rw [map_smul]
      exact add_mem (memT1 w hw) (memT3 _ (app_mem_MMHigh F.toHom hh))
    · have hMM : isoProj D₂.desc c z₀ ∈
          GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O) :=
        ⟨D₂.ext_mono (A_le_S l e) hz₁L, Submodule.mem_top⟩
      have hst := aeval_mem_of_stable (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O)) D₂.conn
        ((hred.2.1 κ η H D₂).1.conn_MM) _ (hZ (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A')) _ hMM
      rw [(hred.2.1 κ η H D₂).1.MM_eq] at hst
      obtain ⟨u, hu, h, hh, hsum⟩ := Submodule.mem_sup.1 hst
      rw [← hsum, smul_add]
      refine add_mem (memT2 _ hu.1) (memT3 _ ?_)
      rw [hlpow]
      exact (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod).toAddSubmonoid.nsmul_mem hh.1 _

  have hB' : Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A') y ∈ T := by
    have hr := ((hdeg Sig c A' (by omega)).2 κ η H D₂ h₂).aeval₂ _ ⟨hy_v, hy_iso⟩
    obtain ⟨u, hu, h, hh, hsum⟩ := Submodule.mem_sup.1 hr
    rw [← hsum]
    refine add_mem ?_ (memT3 _ hh)
    obtain ⟨w, hw, rfl⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_mulL.1 hu
    obtain ⟨y', hy', z', hz', h4⟩ := a3 w hw
    have : ((X : K⟦X⟧) ^ e) ^ (2 * A') • w = ((X : K⟦X⟧) ^ e) ^ A' • ((X : K⟦X⟧) ^ e) ^ A' • w := by
      rw [smul_smul, ← pow_add, two_mul]
    rw [this, h4, smul_add, smul_comm _ ((l : K) ^ b)]
    exact add_mem (memT1 y' hy') (memT2 _ (vmemL _ _ hz'))
  rw [key]
  exact add_mem
    (aeval_mem_of_stable T D₂.conn hTc _ (fun n => by rw [Polynomial.coeff_map]; exact hφ _) _ hA)
    (aeval_mem_of_stable T D₂.conn hTc _ (fun n => by rw [Polynomial.coeff_map]; exact hφ _) _ hB')

end GlobalTheory.CokerL

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

theorem kills_cokerL : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (N : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H → (∀ τ, D₁.desc.chars τ ⊆ (Sig : Set (ZMod e))) → (∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))) → IsFiniteLength (A O K) F.coker → GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) D₁.L D₂.L := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F Sig U N hB h₁ h₂ hfl
  set ρ := GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N with hρ
  set b := ρ + 1 with hb
  set A' := H + η + b with hA'

  have horb := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a (Fact.out : l.Prime) (Nat.one_le_iff_ne_zero.2 (NeZero.ne a))
    (TameDescentExponentData.succ_eq (K := K)) Sig N hB.frob_mem hB.zero_mem_Sig hB.card_Sig hB.two_le
  have hnum := GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hB.two_le hB.one_le hB.lt horb.2.1 hB.large
  have hA'l : 2 * A' + 2 < l := by
    have : A' = H + η + 2 * (N - 1) * maxPeriod l Sig + 1 := by
      simp only [hA', hb, hρ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho]; ring
    rw [this]; exact hnum.1

  have hns : ∀ (n : ℕ) (v : Vec K a κ), ((n : K)) • v = n • v := fun n v => Nat.cast_smul_eq_nsmul K n v
  have hns' : ∀ (n : ℕ) (v : Vec K a κ), ((n : K⟦X⟧)) • v = n • v := fun n v => Nat.cast_smul_eq_nsmul K⟦X⟧ n v
  have hlpow : ∀ (n : ℕ) (v : Vec K a κ), (l : K) ^ n • v = (l ^ n) • v := fun n v => by
    rw [← Nat.cast_pow, hns]
  have hlpow' : ∀ (n : ℕ) (v : Vec K a κ), (l : K⟦X⟧) ^ n • v = (l : K) ^ n • v := fun n v => by
    rw [← Nat.cast_pow, hns', hlpow]
  have hlpow₁ : ∀ (n : ℕ) (v : Vec K a ι), (l : K) ^ n • v = (l ^ n) • v := fun n v => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul K]
  have hvA : ∀ n : ℕ, ((X : K⟦X⟧) ^ e) ^ n ∈ A O K := fun n =>
    pow_mem (pow_mem (HasU.X_mem (B := A O K)) e) n
  have vmemL : ∀ n : ℕ, ∀ v ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ n • v ∈ D₂.L := fun n v hv =>
    D₂.L.smul_mem (⟨_, hvA n⟩ : A O K) hv
  have lmemL : ∀ n : ℕ, ∀ v ∈ D₂.L, (l : K) ^ n • v ∈ D₂.L := fun n v hv => by
    rw [hlpow]; exact D₂.L.toAddSubmonoid.nsmul_mem hv _
  have lmemL₁ : ∀ n : ℕ, ∀ v ∈ D₁.L, (l : K) ^ n • v ∈ D₁.L := fun n v hv => by
    rw [hlpow₁]; exact D₁.L.toAddSubmonoid.nsmul_mem hv _
  have appL : ∀ v ∈ D₁.L, F.app v ∈ D₂.L := fun v hv => F.app_mem_ext le_rfl hv
  have hred := GlobalTheory.T.monodromy_reduction_modulo_high_degree O K l e a

  have a3 : ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L,
      ((X : K⟦X⟧) ^ e) ^ A' • x = F.app y + (l : K) ^ b • z :=
    GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel O K l e a ι κ η H D₁ D₂ F hfl b (by omega) (by omega)

  have stepP : ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, (l : K) ^ ρ • x = F.app y + (l : K) ^ b • z := by
    intro x hx
    have hT : (l : K) ^ ρ • (((X : K⟦X⟧) ^ e) ^ A' • x) ∈ GlobalTheory.CokerL.Tsub F A' b := by
      rw [← GlobalTheory.T.sum_isotypicProjectors_eq_id O K l e a κ D₂.toPhiMod D₂.desc (((X : K⟦X⟧) ^ e) ^ A' • x),
        Finset.smul_sum]
      refine Submodule.sum_mem _ fun c _ => ?_
      exact GlobalTheory.CokerL.isotypic_step O K l e a ι κ η H D₁ D₂ F Sig U N hB h₁ h₂ hfl c x hx
    obtain ⟨t, ht, h, hh, hth⟩ := Submodule.mem_sup.1 hT
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := Submodule.mem_sup.1 ht
    obtain ⟨u₁, hu₁, rfl⟩ := Submodule.mem_map.1 ht₁
    obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.1 (Submodule.restrictScalars_mem _ _ _ |>.1 hu₁)
    obtain ⟨z', hz', rfl⟩ := Submodule.mem_map.1 ht₂
    simp only [LinearMap.restrictScalars_apply, GlobalTheory.BK.mulV_apply] at hth
    have hz'L : z' ∈ D₂.L := hz'
    have hhL : h ∈ D₂.L := by
      have : h = (l : K) ^ ρ • (((X : K⟦X⟧) ^ e) ^ A' • x) -
          (((X : K⟦X⟧) ^ e) ^ A' • F.app y' + (l : K⟦X⟧) ^ b • z') := by rw [← hth]; abel
      rw [this]
      exact sub_mem (lmemL _ _ (vmemL _ _ hx))
        (add_mem (vmemL _ _ (appL _ hy')) (by rw [hlpow']; exact lmemL _ _ hz'L))
    have hv : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.vL D₂.toPhiMod l := by
      have hi := (hred.2.1 κ η H D₂).1.inter_eq
      have hmem : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.L.restrictScalars O) ⊓
          GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod) :=
        ⟨⟨hhL, Submodule.mem_top⟩, ⟨hh, Submodule.mem_top⟩⟩
      rw [hi] at hmem
      exact hmem.1
    obtain ⟨h₀, hh₀, rfl⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_mulL.1 hv
    have hle : A' ≤ l := by omega
    have hwL : (l : K) ^ ρ • x - F.app y' - ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀ ∈ D₂.L :=
      sub_mem (sub_mem (lmemL _ _ hx) (appL _ hy')) (vmemL _ _ hh₀)
    have hw : ((X : K⟦X⟧) ^ e) ^ A' • ((l : K) ^ ρ • x - F.app y' - ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀) =
        (l : K) ^ b • z' := by
      rw [smul_sub, smul_sub, smul_comm (((X : K⟦X⟧) ^ e) ^ A') ((l : K) ^ ρ), smul_smul, ← pow_add,
        Nat.add_sub_cancel' hle, ← hth, hlpow']
      abel
    obtain ⟨z'', hz'', hw'⟩ := GlobalTheory.T.mem_prime_pow_lattice_of_X_pow_smul_mem O K l e a κ D₂.toPhiMod A' b _ z' hwL hz'L hw
    obtain ⟨y₂, hy₂, z₂, hz₂, h2⟩ := a3 _ (vmemL (l - 2 * A') _ hh₀)
    have e1 : ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀ =
        ((X : K⟦X⟧) ^ e) ^ A' • ((X : K⟦X⟧) ^ e) ^ (l - 2 * A') • h₀ := by
      rw [smul_smul, ← pow_add]
      congr 2
      omega
    refine ⟨y' + y₂, add_mem hy' hy₂, z'' + z₂, add_mem hz'' hz₂, ?_⟩
    have key : (l : K) ^ ρ • x = ((l : K) ^ ρ • x - F.app y' - ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀) +
        F.app y' + ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀ := by abel
    rw [key, hw', e1, h2, map_add, smul_add]
    abel

  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_prime_pow_kills_finiteLength_integralPowerSeries O K l F.coker hfl
  have killM : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ m) D₁.M D₂.M :=
    (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.killsCoker_M_iff F.toHom (l ^ m)).2 fun q => by
      rw [← Nat.cast_smul_eq_nsmul (A O K), Nat.cast_pow]
      exact hm q
  have killL : ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, F.app y = (l ^ m) • x := by
    intro x hx
    rw [D₂.toPhiMod.L_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨y₀, hy₀, hF⟩ := killM w hw
      exact ⟨D₁.phi y₀, D₁.phi_mem_L hy₀, by rw [F.app_phi, hF, map_nsmul]⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a1, ha1, e1⟩ := hx
      obtain ⟨a2, ha2, e2⟩ := hy
      exact ⟨a1 + a2, add_mem ha1 ha2, by rw [map_add, e1, e2, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a1, ha1, e1⟩ := hx
      exact ⟨r • a1, D₁.L.smul_mem r ha1, by rw [LinearMap.map_smul_of_tower, e1, smul_comm]⟩
  have Q : ∀ k : ℕ, ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L,
      (l : K) ^ ρ • x = F.app y + (l : K) ^ (ρ + k) • z := by
    intro k
    induction k with
    | zero => exact fun x hx => ⟨0, zero_mem _, x, hx, by simp⟩
    | succ k ih =>
      intro x hx
      obtain ⟨y, hy, z, hz, e1⟩ := ih x hx
      obtain ⟨y₂, hy₂, z₂, hz₂, e2⟩ := stepP z hz
      refine ⟨y + (l : K) ^ k • y₂, add_mem hy (lmemL₁ _ _ hy₂), z₂, hz₂, ?_⟩
      have hp : (l : K) ^ (ρ + (k + 1)) = (l : K) ^ k * (l : K) ^ b := by
        rw [← pow_add]; congr 1; omega
      rw [e1, pow_add, mul_comm, mul_smul, e2, smul_add, smul_smul, ← hp, map_add,
        LinearMap.map_smul_of_tower, add_assoc]
  intro x hx
  obtain ⟨y, hy, z, hz, e1⟩ := Q m x hx
  obtain ⟨y₃, hy₃, e3⟩ := killL z hz
  refine ⟨y + (l : K) ^ ρ • y₃, add_mem hy (lmemL₁ _ _ hy₃), ?_⟩
  rw [← hlpow ρ x, e1, pow_add, mul_smul, hlpow m z, map_add, LinearMap.map_smul_of_tower, e3]

end GlobalTheory.CokerL
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_pow_kills_lattice_cokernel : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (N : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H → (∀ τ, D₁.desc.chars τ ⊆ (Sig : Set (ZMod e))) → (∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))) → IsFiniteLength (A O K) F.coker → GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) D₁.L D₂.L := by
  atlas_forward_decl GlobalTheory.CokerL.kills_cokerL
end

section
section
noncomputable section

namespace GlobalTheory.CokerLift

open PowerSeries GlobalTheory.BK Matrix

section Psi

variable {K : Type} [NormedField K]

def psi (l : ℕ) : K⟦X⟧ →ₗ[K] K⟦X⟧ where
  toFun f := PowerSeries.mk fun n => coeff (l * n) f
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp

theorem coeff_psi (l : ℕ) (f : K⟦X⟧) (n : ℕ) : coeff n (psi l f) = coeff (l * n) f := by
  simp [psi]

theorem psi_frob_mul (l : ℕ) [Fact l.Prime] (g h : K⟦X⟧) :
    psi l (frob K l g * h) = g * psi l h := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_psi, coeff_mul, coeff_mul]
  have hinj : Function.Injective (fun p : ℕ × ℕ => (l * p.1, l * p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hl h.1) (Nat.eq_of_mul_eq_mul_left hl h.2)
  have h1 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 g * coeff p.2 (psi l h) =
      ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).map ⟨_, hinj⟩, coeff p.1 (frob K l g) * coeff p.2 h := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Function.Embedding.coeFn_mk, coeff_frob, coeff_psi, dvd_mul_right, if_true,
      Nat.mul_div_cancel_left _ hl]
  rw [h1]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro p hp
    rw [Finset.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    simp only [Function.Embedding.coeFn_mk]
    rw [← mul_add, hq]
  · intro p hp hp'
    rw [coeff_frob, if_neg, zero_mul]
    rintro ⟨c, hc⟩
    apply hp'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [Finset.mem_map]
    refine ⟨(c, n - c), ?_, ?_⟩
    · have : l * c ≤ l * n := by omega
      have := Nat.le_of_mul_le_mul_left this hl
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      simp only; omega
    · refine Prod.ext hc.symm ?_
      simp only [Function.Embedding.coeFn_mk, Nat.mul_sub]
      omega

theorem psi_frob (l : ℕ) [Fact l.Prime] (g : K⟦X⟧) : psi l (frob K l g) = g := by
  ext n
  rw [coeff_psi, coeff_frob, if_pos (dvd_mul_right _ _),
    Nat.mul_div_cancel_left _ (Fact.out : l.Prime).pos]

theorem psi_mulVec {ι κ : Type} [Fintype ι] (l : ℕ) [Fact l.Prime] (Y : Matrix κ ι K⟦X⟧)
    (m : ι → K⟦X⟧) :
    (fun i => psi l ((Y.map (frob K l) *ᵥ m) i)) = Y *ᵥ fun j => psi l (m j) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, psi_frob_mul]

end Psi

end GlobalTheory.CokerLift

noncomputable section

namespace GlobalTheory.CokerLift

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds

section Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]

theorem psi_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : psi l f ∈ A O K := fun n => by
  rw [coeff_psi]
  exact hf _

theorem killsCoker_M {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q) (n : ℕ)
    (hL : KillsCoker F.app n P.L Q.L) : KillsCoker F.app n P.M Q.M := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hL (Q.phi y) (Q.phi_mem_L hy)
  have hm (τ : ZMod a) := P.mem_extc_iff.1 (mem_tot.1 hx τ)
  refine ⟨fun σ i => psi l ((P.mxInv (σ + 1) *ᵥ x (σ + 1)) i),
    mem_tot.2 fun σ i => psi_mem_A (hm (σ + 1) i), ?_⟩
  funext σ
  have key : (F.mat σ).map (frob K l) *ᵥ (P.mxInv (σ + 1) *ᵥ x (σ + 1)) = n • frobV l (y σ) := by
    have hc := F.comm (σ + 1)
    rw [add_sub_cancel_right] at hc
    have h2 : (F.mat σ).map (frob K l) = Q.mxInv (σ + 1) * (F.mat (σ + 1) * P.mx (σ + 1)) := by
      rw [hc, ← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]
    have h3 := congrFun hxy (σ + 1)
    rw [Hom.app_apply, Pi.smul_apply, Q.phi_apply, add_sub_cancel_right] at h3
    rw [h2, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Q.mxInv_mul_mx,
      Matrix.one_mulVec]
  rw [Hom.app_apply, ← psi_mulVec, key]
  funext i
  simp only [Pi.smul_apply, frobV_apply, map_nsmul, psi_frob]

theorem killsCoker_EM [NormedAlgebra ℚ_[l] K] [NeZero e] {P : PhiMod O K l e a ι}
    {Q : PhiMod O K l e a κ} (F : Hom P Q) (n η : ℕ) (hM : KillsCoker F.app n P.M Q.M) :
    KillsCoker F.app n (P.EM η) (Q.EM η) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hM _ hy
  refine ⟨Ezpow K l e (-(η : ℤ)) • x, ?_, ?_⟩
  · change E K l e ^ η • Ezpow K l e (-(η : ℤ)) • x ∈ P.M
    rw [smul_smul, E_pow_mul_Ezpow_neg, one_smul]
    exact hx
  · rw [map_smul, hxy, smul_comm, smul_smul, mul_comm, E_pow_mul_Ezpow_neg, one_smul]

theorem killsCoker_invOf [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P} {Δ₂ : Descent Q}
    (F : Descent.Hom Δ₁ Δ₂) (n : ℕ) (W₁ : Submodule (A O K) (Vec K a ι))
    (W₂ : Submodule (A O K) (Vec K a κ)) (hW : ∀ g, ∀ v ∈ W₁, Δ₁.act g v ∈ W₁)
    (h : KillsCoker F.app n W₁ W₂) : KillsCoker F.app n (Δ₁.invOf W₁) (Δ₂.invOf W₂) := by
  intro y hy
  obtain ⟨hy1, hy2⟩ := Δ₂.mem_invOf.1 hy
  obtain ⟨x, hx, hxy⟩ := h y hy1
  refine ⟨Δ₁.avg x, Δ₁.mem_invOf.2 ⟨Δ₁.avg_mem (W₁.restrictScalars O) fun g => hW g x hx,
    fun g => Δ₁.avg_mem_inv x g⟩, ?_⟩
  have := Δ₁.map_avg (F.app.restrictScalars K) (v := x) fun g => by
    simp only [LinearMap.restrictScalars_apply]
    rw [F.app_act, hxy, map_nsmul, hy2 g]
  exact this.trans hxy

theorem killsCoker_Y' [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P} {Δ₂ : Descent Q}
    (F : Descent.Hom Δ₁ Δ₂) (n η : ℕ) (hY : KillsCoker F.app n (Δ₁.Y η) (Δ₂.Y η)) :
    KillsCoker F.app n (Δ₁.Y' η) (Δ₂.Y' η) := by
  intro y hy
  obtain ⟨y₀, h₀, rfl⟩ := Δ₂.mem_Y'.1 hy
  obtain ⟨x, hx, hxy⟩ := hY y₀ h₀
  exact ⟨_, Δ₁.mem_Y'.2 ⟨x, hx, rfl⟩, by rw [map_smul, hxy, smul_comm]⟩

end Main

theorem killsAll_of_killsCoker_L (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type)
    [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H)
    (F : BKHom D₁ D₂) : ∀ r : ℕ, KillsCoker F.app (l ^ r) D₁.L D₂.L → KillsAll F (l ^ r) := by
  intro r hL
  have hM := killsCoker_M F.toHom _ hL
  have hEM := killsCoker_EM F.toHom _ η hM
  have hY := killsCoker_invOf F _ _ _ (fun g _ hv => D₁.desc.act_mem_EM g hv) hEM
  exact ⟨hL, hM, hEM, killsCoker_invOf F _ _ _ (fun g v hv => D₁.desc.act_mem_M g v hv) hM, hY,
    killsCoker_Y' F _ η hY⟩

end GlobalTheory.CokerLift
end
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.killsCoker_all_of_killsCoker_phiModuleLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ r : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ r) D₁.L D₂.L → GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsAll F (l ^ r) := by
  atlas_forward_decl GlobalTheory.CokerLift.killsAll_of_killsCoker_L
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  intro O K _ _ _ _ _ l e a _ _ _ _ hT ι κ _ _ _ _ Sig U N η H hB D₁ D₂ hD₁ hD₂ F hF
  haveI : FiniteDimensional ℚ_[l] K := hT.finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  exact GlobalTheory.T.killsCoker_all_of_killsCoker_phiModuleLattice O K l e a ι κ η H D₁ D₂ F _
    (GlobalTheory.T.breuilKisin_pow_kills_lattice_cokernel O K l e a ι κ η H D₁ D₂ F Sig U N hB hD₁.chars_subset hD₂ hF)

end GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  atlas_forward_decl GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main
end
