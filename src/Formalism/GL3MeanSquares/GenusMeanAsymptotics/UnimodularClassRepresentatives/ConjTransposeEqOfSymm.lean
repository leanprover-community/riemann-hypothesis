import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ConjTransposeMapMk
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardUnitaryReduction

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem IsE.mono {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e c : ℕ}
    (he : IsE h A 𝔭 e) (hec : e ≤ c) : IsE h A 𝔭 c :=
  fun x hx t ht => he x hx t (Ideal.pow_le_pow_right hec ht)







theorem pow_notMem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π₀ : 𝓞 F} (hπ : π₀ ∉ 𝔭 ^ 2) (e : ℕ) :
    π₀ ^ e ∉ 𝔭 ^ (e + 1) := by
  induction e with
  | zero =>
    rw [pow_zero, zero_add, pow_one]
    exact fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h)
  | succ e ih =>
    have := mul_notMem h𝔭.isPrime (ne_bot h𝔭) ih hπ
    rwa [← pow_succ] at this

theorem exists_common_den {𝔭 : Ideal (𝓞 F)} [hp : 𝔭.IsPrime] {α : Type*} [Fintype α] (f : α → K)
    (hf : ∀ a, f a ∈ SP K 𝔭) : ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ a, ∃ z : 𝓞 K, jK z = jK (ι t) * f a := by
  classical
  choose t ht z hz using fun a => mem_SP.1 (hf a)
  refine ⟨∏ a, t a, ?_, fun a => ⟨ι (∏ a' ∈ Finset.univ.erase a, t a') * z a, ?_⟩⟩
  · intro hmem
    obtain ⟨a, -, ha⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    exact ht a ha
  · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), map_mul, hz, map_mul ι, map_mul jK]
    ring

theorem exists_E₀ (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0)
    (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) :
    ∃ (E₀ : Matrix κ κ (𝓞 K)) (d : 𝓞 F), d ∉ 𝔭 ^ (e + 1) ∧ H * E₀ = ι d • (1 : Matrix κ κ (𝓞 K)) := by
  have := h𝔭.isPrime
  obtain ⟨π₀, s₀, hu⟩ := exists_isUnif0 h𝔭
  obtain ⟨E, hE, hHE⟩ := exists_E hF hd b he hu.mem
  obtain ⟨t, ht, hz⟩ := exists_common_den (fun p : κ × κ => E p.1 p.2) (fun p => hE p.1 p.2)
  choose z hz using hz
  refine ⟨Matrix.of fun i j => z (i, j), t * π₀ ^ e, ?_, ?_⟩
  · have := mul_notMem h𝔭.isPrime (ne_bot h𝔭) (i := 0) (by rwa [zero_add, pow_one]) (pow_notMem h𝔭 hu.notMem e)
    rwa [zero_add] at this
  · have h1 : (Matrix.of fun i j => z (i, j)).map jK = jK (ι t) • E := by
      ext i j
      exact hz (i, j)
    have h2 : (H * Matrix.of fun i j => z (i, j)).map jK = (ι (t * π₀ ^ e) • (1 : Matrix κ κ (𝓞 K))).map jK := by
      rw [Matrix.map_mul, h1, ← gramK_eq_map hH, Matrix.mul_smul, hHE, smul_smul]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    exact Matrix.ext fun i j => jK_inj (congrFun (congrFun h2 i) j)


end Formalism.HermitianLattices.Ext.L3.HU
