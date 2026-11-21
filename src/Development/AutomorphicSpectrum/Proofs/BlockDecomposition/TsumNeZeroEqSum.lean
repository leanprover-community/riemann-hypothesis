import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncSum
import BuildAid.ForwardExisting

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.Mass.MeanV.Den

variable {F : Type} [Field F] [NumberField F]

theorem exists_pow_mul_le_one (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v)
    (ha : Valued.v a < 1) (K : Set (Fv F v)) (hK : IsCompact K) :
    ∃ m : ℕ, ∀ s ∈ K, Valued.v (a ^ m * s) ≤ 1 := by
  have h1 : IsOpen {s : Fv F v | Valued.v s < 1} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy => ?_⟩
    have hy' : Valued.v (y - x) < 1 := by simpa using hy
    have h := Valuation.map_add_lt Valued.v hy' hx
    simpa using h
  have h2 : Tendsto (fun m : ℕ => a ^ m) atTop (𝓝 0) := Valued.tendsto_zero_pow_of_v_lt_one ha
  have hUo : ∀ m : ℕ, IsOpen {s : Fv F v | Valued.v (a ^ m * s) < 1} := fun m =>
    (continuous_const.mul continuous_id).isOpen_preimage _ h1
  have hcover : ∀ s : Fv F v, ∃ m : ℕ, Valued.v (a ^ m * s) < 1 := by
    intro s
    have h0 : Tendsto (fun m : ℕ => a ^ m * s) atTop (𝓝 0) := by
      simpa using h2.mul_const s
    have hn : {y : Fv F v | Valued.v y < 1} ∈ 𝓝 (0 : Fv F v) := h1.mem_nhds (by simp)
    exact (h0.eventually hn).exists
  have hmono : Monotone fun m : ℕ => {s : Fv F v | Valued.v (a ^ m * s) < 1} := by
    intro m m' hmm' s hs
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmm'
    show Valued.v (a ^ (m + d) * s) < 1
    rw [show a ^ (m + d) * s = a ^ d * (a ^ m * s) by ring, Valuation.map_mul, map_pow]
    calc Valued.v a ^ d * Valued.v (a ^ m * s) ≤ 1 * Valued.v (a ^ m * s) :=
by
          gcongr
          first
            | exact pow_le_one₀ zero_le ha.le
            | exact pow_le_one₀ zero_le' ha.le
      _ = Valued.v (a ^ m * s) := one_mul _
      _ < 1 := hs
  obtain ⟨m, hm⟩ := hK.elim_directed_cover (fun m : ℕ => {s : Fv F v | Valued.v (a ^ m * s) < 1}) hUo
    (fun s _ => Set.mem_iUnion.mpr (hcover s)) hmono.directed_le
  exact ⟨m, fun s hs => le_of_lt (hm hs)⟩

theorem exists_nat_lt_one (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, 0 < p ∧ v.valuation F (p : F) < 1 := by
  refine ⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h), ?_⟩
  have hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  have h : (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) : F) = ((Ideal.absNorm v.asIdeal : ℕ) : F) := by simp
  rw [← h]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hm

theorem val_nat_le_one (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : v.valuation F (n : F) ≤ 1 := by
  have h : ((n : 𝓞 F) : F) = (n : F) := by simp
  rw [← h]
  exact HeightOneSpectrum.valuation_le_one v _

end GlobalTheory.CompanionTheory.Mass.MeanV.Den

theorem GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator :
    ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v ∈ T, IsCompact (K v)) → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ IntOut T, (∀ v ∈ T, algebraMap F (Fv F v) x ∈ K v) → ∃ y : 𝓞 F, (y : F) = (N : F) * x := by
  intro F _ _ T K hK
  have h3 : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : F), Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
    intro v x
    show Valued.v ((x : v.adicCompletion F)) = v.valuation F x
    first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) x
  have h4 : ∀ x : F, (∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1) → ∃ y : 𝓞 F, (y : F) = x := by
    intro x hx
    obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) (x := x) (h := hx)
    exact ⟨y, hy⟩
  have hpl : ∀ (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ), v.valuation F ((n : F) ^ k) ≤ 1 := by
    intro v n k
    rw [← Nat.cast_pow]
    exact Den.val_nat_le_one v _
  choose p hp0 hp1 using fun v : HeightOneSpectrum (𝓞 F) => Den.exists_nat_lt_one v
  have hm : ∀ v ∈ T, ∃ m : ℕ, ∀ s ∈ K v, Valued.v (algebraMap F (Fv F v) (p v : F) ^ m * s) ≤ 1 :=
    fun v hv => Den.exists_pow_mul_le_one v _ (by rw [h3]; exact hp1 v) (K v) (hK v hv)
  choose! m hm using hm
  refine ⟨∏ v ∈ T, p v ^ m v, Finset.prod_pos fun v _ => pow_pos (hp0 v) _, ?_⟩
  intro x hx hxK
  apply h4
  intro w
  push_cast
  rw [map_mul]
  by_cases hw : w ∈ T
  · rw [← Finset.mul_prod_erase T (fun v => (p v : F) ^ m v) hw, map_mul, map_prod]
    have hrest : ∏ v ∈ T.erase w, w.valuation F ((p v : F) ^ m v) ≤ 1 :=
      Finset.prod_le_one' fun v _ => hpl w (p v) (m v)
    have hmain : w.valuation F ((p w : F) ^ m w) * w.valuation F x ≤ 1 := by
      have h := hm w hw _ (hxK w hw)
      rw [← map_pow, ← map_mul, h3, map_mul] at h
      exact h
    calc w.valuation F ((p w : F) ^ m w) * (∏ v ∈ T.erase w, w.valuation F ((p v : F) ^ m v)) *
          w.valuation F x
        = (∏ v ∈ T.erase w, w.valuation F ((p v : F) ^ m v)) *
            (w.valuation F ((p w : F) ^ m w) * w.valuation F x) := by ac_rfl
      _ ≤ 1 * 1 := mul_le_mul' hrest hmain
      _ = 1 := one_mul 1
  · have hxw : w.valuation F x ≤ 1 := by
      have h : Valued.v (algebraMap F (Fv F w) x) ≤ 1 := hx w hw
      rwa [h3] at h
    have hN : w.valuation F (∏ v ∈ T, (p v : F) ^ m v) ≤ 1 := by
      rw [map_prod]
      exact Finset.prod_le_one' fun v _ => hpl w (p v) (m v)
    calc w.valuation F (∏ v ∈ T, (p v : F) ^ m v) * w.valuation F x ≤ 1 * 1 := mul_le_mul' hN hxw
      _ = 1 := one_mul 1
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_multiple_bounded_places : ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v ∈ T, IsCompact (K v)) → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ IntOut T, (∀ v ∈ T, algebraMap F (Fv F v) x ∈ K v) → ∃ y : 𝓞 F, (y : F) = (N : F) * x := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem support_finite (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (K : Set (Ainf F))
    (hK : IsCompact K) (Kv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hKv : ∀ v ∈ T, IsCompact (Kv v))
    (δ : ℝ) (hδ : 0 < δ) :
    {x : F | x ≠ 0 ∧ x ∈ IntOut T ∧ θ δ * algebraMap F (Ainf F) x ∈ K ∧
      ∀ v ∈ T, algebraMap F (Fv F v) x ∈ Kv v}.Finite := by
  obtain ⟨N, hN, hNx⟩ := GlobalTheory.T.exists_integral_multiple_bounded_places F T Kv hKv
  obtain ⟨C0, h⟩ := hC F hF θ hθ K hK N hN
  refine ((h δ hδ ⊤ top_ne_bot).1).subset ?_
  rintro x ⟨h0, h1, h2, h3⟩
  obtain ⟨y, hy⟩ := hNx x h1 h3
  exact ⟨h0, ⟨y, Submodule.mem_top, hy⟩, h2⟩

theorem tsum_ne_zero_eq_sum {F : Type} [Field F] (h : F → ℝ) (B : Finset F) (hB : ∀ x ∈ B, x ≠ 0)
    (hh : ∀ x, x ≠ 0 → x ∉ B → h x = 0) :
    ∑' β : {β : F // β ≠ 0}, h β.1 = ∑ x ∈ B, h x := by
  have h1 : ∑' β : {β : F // β ≠ 0}, h β.1 = ∑ β ∈ B.subtype (fun x => x ≠ 0), h β.1 := by
    refine tsum_eq_sum ?_
    intro b hb
    exact hh b.1 b.2 (by simpa [Finset.mem_subtype] using hb)
  rw [h1]
  refine Finset.sum_bij (fun b _ => b.1) ?_ ?_ ?_ ?_
  · intro a ha; simpa [Finset.mem_subtype] using ha
  · intro a _ b _ hab; exact Subtype.ext hab
  · intro b hb; exact ⟨⟨b, hB b hb⟩, by simpa [Finset.mem_subtype] using hb, rfl⟩
  · intro a _; rfl

theorem truncTerm_finite (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hGc : HasCompactSupport G)
    (hψ : ∀ v ∈ T, HasCompactSupport (ψ v)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : Finset F, (∀ x ∈ B, x ≠ 0) ∧ ∀ x, x ≠ 0 → x ∉ B → (IntOut T).indicator
      (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) x = 0 := by
  have hfin := support_finite hC F hF θ hθ T (tsupport G) hGc (fun v => tsupport (ψ v)) hψ δ hδ
  refine ⟨hfin.toFinset, fun x hx => ((hfin.mem_toFinset).1 hx).1, ?_⟩
  intro x hx0 hxB
  by_cases hxT : x ∈ IntOut T
  · rw [Set.indicator_of_mem hxT]
    by_cases h1 : θ δ * algebraMap F (Ainf F) x ∈ tsupport G
    · have : ∃ v ∈ T, algebraMap F (Fv F v) x ∉ tsupport (ψ v) := by
        by_contra hcon
        push_neg at hcon
        exact hxB ((hfin.mem_toFinset).2 ⟨hx0, hxT, h1, hcon⟩)
      obtain ⟨v, hv, hvx⟩ := this
      have h0 : ψ v (algebraMap F (Fv F v) x) = 0 := image_eq_zero_of_notMem_tsupport hvx
      rw [Finset.prod_eq_zero hv h0, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  · exact Set.indicator_of_notMem hxT _

theorem truncTerm_summable (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hGc : HasCompactSupport G)
    (hψ : ∀ v ∈ T, HasCompactSupport (ψ v)) (δ : ℝ) (hδ : 0 < δ) :
    Summable fun β : {β : F // β ≠ 0} => (IntOut T).indicator
      (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) β.1 := by
  obtain ⟨B, hB, hh⟩ := truncTerm_finite hC F hF θ hθ T G ψ hGc hψ δ hδ
  refine summable_of_ne_finset_zero (s := B.subtype (fun x => x ≠ 0)) ?_
  intro b hb
  exact hh b.1 b.2 (by simpa [Finset.mem_subtype] using hb)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end
