import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountEqEulerFacInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsClassRepsMap

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem absNorm_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) :
    Ideal.absNorm (extP K 𝔭) = Ideal.absNorm 𝔭 ^ 2 := by
  induction 𝔭 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp [extP]
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.mp hx]
    simp only [extP]
    simp only [Ideal.map_top, Ideal.absNorm_top, one_pow]
  | h₃ a p ha hp ih =>
    have hpm : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hq := idealPowerSpanBounds.absNorm_extP_eq_sq hK hF hpm
    simp only [extP] at ih hq ⊢
    rw [Ideal.map_mul, map_mul, map_mul, ih, hq, mul_pow]

theorem map_comap_eq_of_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := by
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [conjIdeal_eq_comap] at hc
  exact SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ

theorem extP_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  have hP' := conjIdeal_isMaximal hK hP
  have h1 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P := Ideal.map_comap_le
  have h2 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    have : (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).comap (algebraMap (𝓞 F) (𝓞 K)) =
        P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [conjIdeal_eq_comap]
      exact SplitPrimeIdeals.comap_ι_comap (conjO_eq_iff_mem_range hF) P
    rw [← this]
    exact Ideal.map_comap_le
  have hcop : IsCoprime P (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) :=
    (Ideal.isCoprime_iff_sup_eq).2 (hP.coprime_of_ne hP' (Ne.symm hc))
  have h3 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    rw [Ideal.mul_eq_inf_of_isCoprime hcop]
    exact le_inf h1 h2
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 h3
  have hN := absNorm_extP hK hF (P.comap (algebraMap (𝓞 F) (𝓞 K)))
  rw [hC, map_mul, map_mul, absNorm_conjIdeal hK, absNorm_comap_split hK hF hP hc, sq] at hN
  have hpos : 0 < Ideal.absNorm P * Ideal.absNorm P := by
    have : 0 < Ideal.absNorm P := by
      have := IdealNormInequalities.one_lt_absNorm hP
      exact_mod_cast zero_lt_one.trans this
    positivity
  have hC1 : Ideal.absNorm C = 1 := Nat.eq_of_mul_eq_mul_left hpos (by rw [hN, mul_one])
  rw [hC, Ideal.absNorm_eq_one_iff.1 hC1, Ideal.mul_top]

theorem alphaStd_one (𝔭 : Ideal (𝓞 F)) :
    alphaStd K 𝔭 1 = 1 - etaF K F 𝔭 * (Ideal.absNorm 𝔭 : ℝ)⁻¹ := by
  simp [alphaStd]

theorem normRepCount_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {j : ℕ} (hj : 1 ≤ j) :
    (normRepCount K (extP K 𝔭 ^ j) 1 1 : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ j * alphaStd K 𝔭 1 := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have h1 : (1 : 𝓞 K) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hd := localDensity K hK P hP 1 j le_rfl hj 1 (map_one _) h1
  rw [alphaStd_one, etaF_comap hK hF hP]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · rw [map_comap_eq_of_inert hK hF hP hc, hd.1 hc, if_pos hc, ← absNorm_comap_inert hK hF hP hc]
    push_cast
    rw [Real.sqrt_sq (Nat.cast_nonneg _)]
    simp
  · rw [extP_split hK hF hP hc, hd.2 hc, if_neg hc, absNorm_comap_split hK hF hP hc]
    simp

end Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem map_mem_extP {𝔭 : Ideal (𝓞 F)} {k : ℕ} {s : 𝓞 F} (hs : s ∈ 𝔭 ^ k) :
    algebraMap (𝓞 F) (𝓞 K) s ∈ extP K 𝔭 ^ k := by
  rw [← Ideal.mem_comap, MeanB.comap_extP_pow]
  exact hs

theorem mem_extP_of_mul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) {k : ℕ}
    {z : 𝓞 K} (hz : algebraMap (𝓞 F) (𝓞 K) t * z ∈ extP K 𝔭 ^ k) : z ∈ extP K 𝔭 ^ k := by
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  have e : z = algebraMap (𝓞 F) (𝓞 K) u * (algebraMap (𝓞 F) (𝓞 K) t * z) -
      algebraMap (𝓞 F) (𝓞 K) (u * t - 1) * z := by
    rw [map_sub, map_mul, map_one]
    ring
  rw [e]
  exact sub_mem (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_right _ _ (map_mem_extP hu))

theorem conjO_mem_extP (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {z : 𝓞 K}
    (hz : z ∈ extP K 𝔭 ^ k) : conjO K z ∈ extP K 𝔭 ^ k := by
  obtain ⟨z', hz', e⟩ := MeanB.star_mem_extP hF 𝔭 k hz
  have : conjO K z = z' := RingOfIntegers.ext e.symm
  rw [this]
  exact hz'

theorem ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)


variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def IsGen (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (e : V) : Prop :=
  e ∈ L ∧ e ≠ 0 ∧ ∀ x ∈ L, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ a : 𝓞 K, algebraMap (𝓞 F) (𝓞 K) t • x = a • e

theorem exists_isGen {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ e, IsGen L 𝔭 e := by
  obtain ⟨b, hb, hloc⟩ := LocalSpans.exists_basis_locF hL h𝔭
  have hsub : Subsingleton (Fin (finrank K V)) := by
    rw [h1]
    infer_instance
  let i0 : Fin (finrank K V) := ⟨0, by omega⟩
  refine ⟨b i0, hb i0, b.ne_zero i0, fun x hx => ?_⟩
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hloc]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, hm⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ _).1 hx'
  have hr : Set.range b = {b i0} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      rw [Subsingleton.elim i i0]
      rfl
    · rintro rfl
      exact ⟨i0, rfl⟩
  rw [hr, Submodule.mem_span_singleton] at hm
  obtain ⟨a, ha⟩ := hm
  exact ⟨t, ht, a, ha.symm⟩

theorem discrIdeal_le_iff (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : V} (he : IsGen L 𝔭 e)
    {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F)) (j : ℕ) :
    discrIdeal h L ≤ extP K 𝔭 ^ j ↔ n ∈ 𝔭 ^ j := by
  have hsub : Subsingleton (Fin (finrank K V)) := by
    rw [h1]
    infer_instance
  let i0 : Fin (finrank K V) := ⟨0, by omega⟩
  constructor
  · intro hle
    rw [← MeanB.comap_extP_pow (K := K), Ideal.mem_comap]
    apply hle
    refine Ideal.subset_span ⟨fun _ => e, fun _ => he.1, ?_⟩
    rw [Matrix.det_eq_elem_of_subsingleton _ i0, Matrix.of_apply, hn]
    rfl
  · intro hnj
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, hz⟩
    rw [Matrix.det_eq_elem_of_subsingleton _ i0, Matrix.of_apply] at hz
    obtain ⟨t, ht, a, ha⟩ := he.2.2 (x i0) (hx i0)
    apply mem_extP_of_mul h𝔭 ht
    apply mem_extP_of_mul h𝔭 ht
    have : algebraMap (𝓞 F) (𝓞 K) t * (algebraMap (𝓞 F) (𝓞 K) t * z) =
        conjO K a * a * algebraMap (𝓞 F) (𝓞 K) n := by
      apply RingOfIntegers.coe_injective
      have e1 : h (algebraMap (𝓞 F) (𝓞 K) t • x i0) (algebraMap (𝓞 F) (𝓞 K) t • x i0) =
          h (a • e) (a • e) := by rw [ha]
      rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right,
        Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hn, ← hz,
        MeanB.algebraMap_comp, MeanB.star_algebraMap hF] at e1
      simp only [map_mul]
      rw [MeanB.algebraMap_comp, MeanB.algebraMap_comp]
      change _ = star (algebraMap (𝓞 K) K a) * _ * _
      rw [e1]
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (map_mem_extP hnj)

theorem vd_spec (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : V}
    (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F)) :
    n ∈ 𝔭 ^ vd h L 𝔭 ∧ n ∉ 𝔭 ^ (vd h L 𝔭 + 1) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply he.2.1
    apply LocF.aniso_of_totPosDef hd
    rw [hn]
    simp
  have hset : {j : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ j} = {j : ℕ | n ∈ 𝔭 ^ j} := by
    ext j
    exact discrIdeal_le_iff hF h1 h𝔭 he hn j
  have hinf : (⨅ j : ℕ, 𝔭 ^ j) = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top
  obtain ⟨j0, hj0⟩ : ∃ j0, n ∉ 𝔭 ^ j0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hn0
    have : n ∈ (⨅ j : ℕ, 𝔭 ^ j) := (Submodule.mem_iInf _).2 hcon
    rwa [hinf] at this
  have hbdd : BddAbove {j : ℕ | n ∈ 𝔭 ^ j} := by
    refine ⟨j0, fun j hj => ?_⟩
    by_contra hlt
    exact hj0 (Ideal.pow_le_pow_right (not_le.1 hlt).le hj)
  have hne : {j : ℕ | n ∈ 𝔭 ^ j}.Nonempty := ⟨0, by simp⟩
  unfold vd
  rw [hset]
  refine ⟨Nat.sSup_mem hne hbdd, fun hcon => ?_⟩
  have := le_csSup hbdd (show sSup {j : ℕ | n ∈ 𝔭 ^ j} + 1 ∈ {j : ℕ | n ∈ 𝔭 ^ j} from hcon)
  omega

end Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.EndomorphismScalars

open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

abbrev Qk (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Type :=
  ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)

variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V}

private theorem exists_mul_sub_one_mem_pow_of_not_mem_maximal (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) (k : ℕ) :
    ∃ s : 𝓞 F, s * t - 1 ∈ 𝔭 ^ k := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨y * ∑ l ∈ Finset.range k, i ^ l, ?_⟩
  have h1 : y * t = 1 - i := by rw [← hyi]; ring
  have h2 : y * (∑ l ∈ Finset.range k, i ^ l) * t - 1 = -(i ^ k) := by
    rw [mul_right_comm, h1, mul_neg_geom_sum]; ring
  rw [h2]
  exact (Submodule.neg_mem_iff _).mpr (Ideal.pow_mem_pow hi k)

private theorem algebraMap_mem_extP_pow_of_mem_pow {k : ℕ} {a : 𝓞 F} (ha : a ∈ 𝔭 ^ k) :
    algebraMap (𝓞 F) (𝓞 K) a ∈ extP K 𝔭 ^ k := by
  rw [extP, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

theorem mk_eq_smul (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (x : ↥L) :
    ∃ a : 𝓞 K, (Submodule.Quotient.mk x : Qk L 𝔭 k) = a • Submodule.Quotient.mk ⟨e, he.1⟩ := by
  obtain ⟨t, ht, a, hta⟩ := he.2.2 x x.2
  obtain ⟨s, hs⟩ := exists_mul_sub_one_mem_pow_of_not_mem_maximal h𝔭 ht k
  refine ⟨algebraMap (𝓞 F) (𝓞 K) s * a, ?_⟩
  have hmem : (algebraMap (𝓞 F) (𝓞 K) (s * t - 1)) • x ∈
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) :=
    Submodule.smul_mem_smul (algebraMap_mem_extP_pow_of_mem_pow hs) Submodule.mem_top
  have hL : (algebraMap (𝓞 F) (𝓞 K) t) • x = a • (⟨e, he.1⟩ : ↥L) :=
    Subtype.ext (by rw [Submodule.coe_smul, Submodule.coe_smul]; exact hta)
  have hx : x = (algebraMap (𝓞 F) (𝓞 K) s * a) • (⟨e, he.1⟩ : ↥L) -
      (algebraMap (𝓞 F) (𝓞 K) (s * t - 1)) • x := by
    rw [map_sub, map_mul, map_one, sub_smul, one_smul, mul_smul, mul_smul, hL]
    abel
  conv_lhs => rw [hx]
  rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).mpr hmem, sub_zero,
    Submodule.Quotient.mk_smul]

theorem smul_top_spec (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) {w : ↥L}
    (hw : w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c ∈ extP K 𝔭 ^ k, algebraMap (𝓞 F) (𝓞 K) t • (w : V) = c • e := by
  refine Submodule.smul_induction_on
    (p := fun w : ↥L => ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c ∈ extP K 𝔭 ^ k,
      algebraMap (𝓞 F) (𝓞 K) t • (w : V) = c • e) hw ?_ ?_
  · intro r hr n _
    obtain ⟨t, ht, a, hta⟩ := he.2.2 n n.2
    refine ⟨t, ht, r * a, Ideal.mul_mem_right _ _ hr, ?_⟩
    rw [Submodule.coe_smul, smul_comm, hta, smul_smul]
  · rintro x y ⟨t1, ht1, c1, hc1, h1⟩ ⟨t2, ht2, c2, hc2, h2⟩
    refine ⟨t1 * t2, fun h => (h𝔭.isPrime.mem_or_mem h).elim ht1 ht2,
      algebraMap (𝓞 F) (𝓞 K) t2 * c1 + algebraMap (𝓞 F) (𝓞 K) t1 * c2,
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hc1) (Ideal.mul_mem_left _ _ hc2), ?_⟩
    have e1 : algebraMap (𝓞 F) (𝓞 K) (t1 * t2) • (x : V) = algebraMap (𝓞 F) (𝓞 K) t2 • (c1 • e) := by
      rw [map_mul, mul_comm (algebraMap (𝓞 F) (𝓞 K) t1), mul_smul, h1]
    have e2 : algebraMap (𝓞 F) (𝓞 K) (t1 * t2) • (y : V) = algebraMap (𝓞 F) (𝓞 K) t1 • (c2 • e) := by
      rw [map_mul, mul_smul, h2]
    rw [Submodule.coe_add, smul_add, e1, e2, add_smul, mul_smul, mul_smul]

theorem smul_gen_mem_iff (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    b • (⟨e, he.1⟩ : ↥L) ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) ↔ b ∈ extP K 𝔭 ^ k := by
  constructor
  · intro hb
    obtain ⟨t, ht, c, hc, htc⟩ := smul_top_spec h𝔭 he k hb
    have h1 : (algebraMap (𝓞 F) (𝓞 K) t * b) • e = c • e := by
      rw [Submodule.coe_smul] at htc
      rw [mul_smul]
      exact htc
    have h2 : algebraMap (𝓞 F) (𝓞 K) t * b = c := by
      rw [← algebraMap_smul K _ e, ← algebraMap_smul K c e] at h1
      exact IsFractionRing.injective (𝓞 K) K (smul_left_injective K he.2.1 h1)
    obtain ⟨s, hs⟩ := exists_mul_sub_one_mem_pow_of_not_mem_maximal h𝔭 ht k
    have hb' : b = algebraMap (𝓞 F) (𝓞 K) s * c -
        algebraMap (𝓞 F) (𝓞 K) (s * t - 1) * b := by
      rw [← h2, map_sub, map_mul, map_one]; ring
    rw [hb']
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hc) (Ideal.mul_mem_right _ _ (algebraMap_mem_extP_pow_of_mem_pow hs))
  · intro hb
    exact Submodule.smul_mem_smul hb Submodule.mem_top

theorem end_surj (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ)
    (X : Module.End (𝓞 K) (Qk L 𝔭 k)) :
    ∃ b : 𝓞 K, algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b = X := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (X (Submodule.Quotient.mk ⟨e, he.1⟩))
  obtain ⟨a, ha⟩ := mk_eq_smul h𝔭 he k y
  refine ⟨a, LinearMap.ext fun z => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨ax, hax⟩ := mk_eq_smul h𝔭 he k x
  rw [Module.algebraMap_end_apply, hax, map_smul, ← hy, ha, smul_comm]

theorem end_eq_zero_iff (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b = 0 ↔ b ∈ extP K 𝔭 ^ k := by
  constructor
  · intro h0
    have := LinearMap.congr_fun h0 (Submodule.Quotient.mk ⟨e, he.1⟩)
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at this
    exact (smul_gen_mem_iff h𝔭 he k b).mp this
  · intro hb
    refine LinearMap.ext fun z => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hb Submodule.mem_top

def endHom (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) :
    (𝓞 K ⧸ extP K 𝔭 ^ k) →+* Module.End (𝓞 K) (Qk L 𝔭 k) :=
  Ideal.Quotient.lift _ (algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)))
    fun b hb => (end_eq_zero_iff h𝔭 he k b).2 hb

theorem endHom_mk (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    endHom h𝔭 he k (Ideal.Quotient.mk _ b) =
      algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b := Ideal.Quotient.lift_mk _ _ _

theorem endHom_bijective (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) :
    Function.Bijective (endHom h𝔭 he k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [endHom_mk, end_eq_zero_iff h𝔭 he k] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  · intro X
    obtain ⟨b, hb⟩ := end_surj h𝔭 he k X
    exact ⟨Ideal.Quotient.mk _ b, by rw [endHom_mk, hb]⟩

end Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.NormOneGroup

open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals Formalism.HermitianLattices.Ext.L3.EndomorphismScalars

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem cond_of_mem (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F))
    {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hvk : v ≤ k) {b : 𝓞 K}
    (hc : conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v)) (x y x' y' : ↥L)
    (hx : x' - b • x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L))
    (hy : y' - b • y ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V)) := by
  have e3 : ∀ c : 𝓞 K, algebraMap (𝓞 K) K (conjO K c) = star (algebraMap (𝓞 K) K c) :=
    fun _ => rfl
  have eφ : ∀ a : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (a : F) :=
    fun _ => rfl
  have hψ : ∀ a c : 𝓞 F, algebraMap F K ((a * c : 𝓞 F) : F) =
      algebraMap F K (a : F) * algebraMap F K (c : F) := fun a c => by
    rw [show ((a * c : 𝓞 F) : F) = (a : F) * (c : F) from rfl, map_mul]
  have hfix : ∀ a : 𝓞 F, star (algebraMap F K (a : F)) = algebraMap F K (a : F) :=
    fun a => (hF _).mpr ⟨_, rfl⟩
  have hsmul1 : ∀ (c : 𝓞 K) (u w : V), h (c • u) w = star (algebraMap (𝓞 K) K c) * h u w :=
    fun c u w => by rw [← algebraMap_smul K c u, LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]
  have hsmul2 : ∀ (c : 𝓞 K) (u w : V), h u (c • w) = algebraMap (𝓞 K) K c * h u w :=
    fun c u w => by rw [← algebraMap_smul K c w, map_smul, smul_eq_mul]
  have hA : ∀ w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L), ∀ u : ↥L,
      (∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (w : V) (u : V)) ∧
      (∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (u : V) (w : V)) := by
    intro w hw u
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro c hc m _
      obtain ⟨r1, hr1⟩ := Submodule.mem_one.mp (hLi m m.2 u u.2)
      obtain ⟨r2, hr2⟩ := Submodule.mem_one.mp (hLi u u.2 m m.2)
      refine ⟨⟨conjO K c * r1, Ideal.mul_mem_right _ _ (conjO_mem_extP hF 𝔭 k hc), ?_⟩,
        ⟨c * r2, Ideal.mul_mem_right _ _ hc, ?_⟩⟩
      · rw [map_mul, e3, hr1, Submodule.coe_smul, hsmul1]
      · rw [map_mul, hr2, Submodule.coe_smul, hsmul2]
    · intro w1 w2 h1 h2
      obtain ⟨⟨z1, hz1, ez1⟩, ⟨z1', hz1', ez1'⟩⟩ := h1
      obtain ⟨⟨z2, hz2, ez2⟩, ⟨z2', hz2', ez2'⟩⟩ := h2
      refine ⟨⟨z1 + z2, add_mem hz1 hz2, ?_⟩, ⟨z1' + z2', add_mem hz1' hz2', ?_⟩⟩
      · rw [map_add, ez1, ez2, Submodule.coe_add, map_add, LinearMap.add_apply]
      · rw [map_add, ez1', ez2', Submodule.coe_add, map_add]
  have hB : ∀ u w : ↥L, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ r ∈ extP K 𝔭 ^ v,
      algebraMap (𝓞 K) K r = algebraMap F K (t : F) * h (u : V) (w : V) := by
    intro u w
    obtain ⟨t1, ht1, a1, ha1⟩ := he.2.2 u u.2
    obtain ⟨t2, ht2, a2, ha2⟩ := he.2.2 w w.2
    refine ⟨t1 * t2, fun hm => (h𝔭.isPrime.mem_or_mem hm).elim ht1 ht2,
      conjO K a1 * a2 * algebraMap (𝓞 F) (𝓞 K) n, Ideal.mul_mem_left _ _ (map_mem_extP hv), ?_⟩
    have h1 := congrArg₂ (fun p q => h p q) ha1 ha2
    simp only [hsmul1, hsmul2, hn, eφ, hfix] at h1
    rw [map_mul, map_mul, e3, eφ, hψ]
    linear_combination -h1
  obtain ⟨⟨z1, hz1, ez1⟩, -⟩ := hA (x' - b • x) hx y'
  obtain ⟨-, ⟨z2, hz2, ez2⟩⟩ := hA (y' - b • y) hy (b • x)
  obtain ⟨t, ht, r, hr, er⟩ := hB x y
  refine ⟨t, ht, algebraMap (𝓞 F) (𝓞 K) t * (z1 + z2) + (conjO K b * b - 1) * r, ?_, ?_⟩
  · refine add_mem (Ideal.mul_mem_left _ _ (add_mem hz1 hz2)) ?_
    have hpow : extP K 𝔭 ^ k = extP K 𝔭 ^ (k - v) * extP K 𝔭 ^ v := by
      rw [← pow_add, Nat.sub_add_cancel hvk]
    rw [hpow]
    exact Ideal.mul_mem_mul hc hr
  · rw [map_add, map_mul, map_mul, map_add, ez1, ez2, er, map_sub, map_mul, map_one, e3, eφ]
    simp only [Submodule.coe_sub, Submodule.coe_smul, map_sub, LinearMap.sub_apply, hsmul1, hsmul2]
    ring

theorem mem_of_cond (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F}
    (hn : h e e = algebraMap F K (n : F)) {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hv' : n ∉ 𝔭 ^ (v + 1))
    {b : 𝓞 K} (H : CongrP 𝔭 k (h (b • e) (b • e)) (h e e)) :
    conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v) := by
  obtain ⟨t, ht, z, hz, hzeq⟩ := H
  have e1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
  have e2 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) = algebraMap F K (n : F) := rfl
  have e3 : algebraMap (𝓞 K) K (conjO K b) = star (algebraMap (𝓞 K) K b) := rfl
  have hbe : h (b • e) (b • e) = star (algebraMap (𝓞 K) K b) * algebraMap (𝓞 K) K b * h e e := by
    rw [← algebraMap_smul K b e, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul,
      starRingEnd_apply, mul_assoc]
  have hz' : z = algebraMap (𝓞 F) (𝓞 K) t * algebraMap (𝓞 F) (𝓞 K) n * (conjO K b * b - 1) := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [hzeq, hbe, hn, map_mul, map_mul, map_sub, map_mul, map_one, e1, e2, e3]
    ring
  rcases le_or_gt k v with hkv | hvk
  · rw [Nat.sub_eq_zero_of_le hkv, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  have hne : 𝔭 ≠ ⊥ := ne_bot_of_isMaximal h𝔭
  have hcop : ∀ I : Ideal (𝓞 F), ¬ I ≤ 𝔭 → 𝔭 ⊔ I = ⊤ := fun I hI => by
    by_contra hne'
    exact hI (le_sup_right.trans (h𝔭.eq_of_le hne' le_sup_left).ge)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  have hJp : ¬ J ≤ 𝔭 := by
    intro hle
    apply hv'
    rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_succ]
    exact Ideal.mul_mono_right hle
  have htp : ¬ Ideal.span {t} ≤ 𝔭 := fun hle => ht ((Ideal.span_singleton_le_iff_mem _).mp hle)
  have hcopF : IsCoprime 𝔭 (Ideal.span {t} * J) :=
    (Ideal.isCoprime_iff_sup_eq.mpr (hcop _ htp)).mul_right (Ideal.isCoprime_iff_sup_eq.mpr (hcop _ hJp))
  have hX : IsCoprime (extP K 𝔭) ((Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K))) := by
    rw [Ideal.isCoprime_iff_sup_eq] at hcopF ⊢
    rw [extP, ← Ideal.map_sup, hcopF, Ideal.map_top]
  have hspan : Ideal.span {z} = extP K 𝔭 ^ v * Ideal.span {conjO K b * b - 1} *
      (Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K)) := by
    have hn' : Ideal.span {algebraMap (𝓞 F) (𝓞 K) n} =
        Ideal.map (algebraMap (𝓞 F) (𝓞 K)) (𝔭 ^ v) * Ideal.map (algebraMap (𝓞 F) (𝓞 K)) J := by
      rw [← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton]
    rw [hz', ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
      Ideal.map_mul, extP, ← Ideal.map_pow, hn', Ideal.map_span, Set.image_singleton]
    ring
  have hdvd : extP K 𝔭 ^ k ∣ extP K 𝔭 ^ v * Ideal.span {conjO K b * b - 1} *
      (Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [← hspan]
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hz)
  have hdvd2 := (hX.pow_left (m := k)).dvd_of_dvd_mul_right hdvd
  have hP0 : extP K 𝔭 ^ v ≠ 0 := by
    apply pow_ne_zero
    rw [extP, Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
    exact hne
  rw [show k = v + (k - v) by omega, pow_add] at hdvd2
  have h3 := (mul_dvd_mul_iff_left hP0).mp hdvd2
  exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp h3)

theorem cond_iff (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F))
    {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hv' : n ∉ 𝔭 ^ (v + 1)) (hvk : v ≤ k) (b : 𝓞 K) :
    (∀ x y x' y' : ↥L,
      (Submodule.Quotient.mk x' : Qk L 𝔭 k) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b (Submodule.Quotient.mk x) →
      (Submodule.Quotient.mk y' : Qk L 𝔭 k) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) ↔
      conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v) := by
  constructor
  · intro H
    apply mem_of_cond hF h𝔭 hn hv hv'
    have h1 : (Submodule.Quotient.mk (b • (⟨e, he.1⟩ : ↥L)) : Qk L 𝔭 k) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b (Submodule.Quotient.mk ⟨e, he.1⟩) := by
      rw [Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]
    exact H _ _ _ _ h1 h1
  · intro hc x y x' y' hx hy
    rw [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hx hy
    exact cond_of_mem hF hs hLi h𝔭 he hn hv hvk hc x y x' y' hx hy

def NormOne (Q : Ideal (𝓞 K)) (z : 𝓞 K ⧸ Q) : Prop :=
  ∃ y : 𝓞 K, Ideal.Quotient.mk Q y = z ∧
    Ideal.Quotient.mk Q (conjO K y * y) = Ideal.Quotient.mk Q 1

theorem normOne_mk_iff (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (j : ℕ) (b : 𝓞 K) :
    NormOne (extP K 𝔭 ^ j) (Ideal.Quotient.mk _ b) ↔ conjO K b * b - 1 ∈ extP K 𝔭 ^ j := by
  constructor
  · rintro ⟨y, hy, h1⟩
    rw [Ideal.Quotient.eq] at hy h1
    have hyb : conjO K (y - b) ∈ extP K 𝔭 ^ j := conjO_mem_extP hF 𝔭 j hy
    have e : conjO K b * b - 1 =
        (conjO K y * y - 1) - (conjO K y * (y - b) + conjO K (y - b) * b) := by
      rw [map_sub]
      ring
    rw [e]
    exact sub_mem h1 (add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hyb))
  · intro h
    exact ⟨b, rfl, Ideal.Quotient.eq.mpr h⟩

theorem card_normOne (Q : Ideal (𝓞 K)) :
    Nat.card {z : 𝓞 K ⧸ Q // NormOne Q z} = normRepCount K Q 1 1 := by
  unfold normRepCount
  refine Nat.card_congr ((Equiv.funUnique (Fin 1) (𝓞 K ⧸ Q)).symm.subtypeEquiv ?_)
  intro z
  constructor
  · rintro ⟨y, h1, h2⟩
    exact ⟨fun _ => y, fun i => by simpa using h1, by simpa using h2⟩
  · rintro ⟨y, h1, h2⟩
    exact ⟨y 0, by simpa using h1 0, by simpa using h2⟩

end Formalism.HermitianLattices.Ext.L3.NormOneGroup
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace U3

open ExtendedPrimeIdeals EndomorphismScalars NormOneGroup

theorem absNorm_extP_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F))
    (k : ℕ) : Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
  rw [← absNorm_eq_card, map_pow, ThirdPropositionSlot.absNorm_extP hK hF, ← pow_mul]

theorem absNorm_pos {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 0 < Ideal.absNorm 𝔭 :=
  Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 (ne_bot_of_isMaximal h𝔭))

theorem akCount_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hvk : vd h L 𝔭 ≤ k) :
    akCount h L 𝔭 k = Ideal.absNorm 𝔭 ^ (2 * vd h L 𝔭) *
      normRepCount K (extP K 𝔭 ^ (k - vd h L 𝔭)) 1 1 := by
  obtain ⟨e, he⟩ := exists_isGen hL h1 h𝔭
  obtain ⟨n, hn⟩ := MeanB.exists_val hF hs hLi ⟨e, he.1⟩
  obtain ⟨hv, hv'⟩ := vd_spec hF hd h1 h𝔭 he hn
  generalize vd h L 𝔭 = v at hv hv' hvk ⊢
  have hq := absNorm_pos h𝔭
  have hfin : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := Nat.finite_of_card_ne_zero (by
    rw [absNorm_extP_pow hK hF]
    positivity)
  let π : (𝓞 K ⧸ extP K 𝔭 ^ k) →+* (𝓞 K ⧸ extP K 𝔭 ^ (k - v)) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.sub_le k v))
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have s1 : akCount h L 𝔭 k =
      Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // NormOne (extP K 𝔭 ^ (k - v)) (π a)} := by
    unfold akCount
    refine (Nat.card_congr (Equiv.subtypeEquiv
      (Equiv.ofBijective _ (endHom_bijective h𝔭 he k)) fun a => ?_)).symm
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Equiv.ofBijective_apply, endHom_mk, cond_iff hF hs hLi h𝔭 he hn hv hv' hvk b]
    exact normOne_mk_iff hF 𝔭 (k - v) b
  have s2 : Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // NormOne (extP K 𝔭 ^ (k - v)) (π a)} = _ :=
    HermitianSublattices.card_preimage π.toAddMonoidHom hπ (NormOne (extP K 𝔭 ^ (k - v)))
  have s3 : Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // True} = _ :=
    HermitianSublattices.card_preimage π.toAddMonoidHom hπ (fun _ => True)
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial),
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), absNorm_extP_pow hK hF,
    absNorm_extP_pow hK hF] at s3
  have s4 : Nat.card π.toAddMonoidHom.ker = Ideal.absNorm 𝔭 ^ (2 * v) := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq (2 * (k - v)))
    rw [← s3, ← pow_add]
    congr 1
    omega
  rw [s1, s2, s4, card_normOne]

theorem alphaStd_one_ne_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : alphaStd K 𝔭 1 ≠ 0 := by
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) := by
    have h0 := absNorm_pos h𝔭
    have h1 : Ideal.absNorm 𝔭 ≠ 1 := mt Ideal.absNorm_eq_one_iff.1 h𝔭.ne_top
    exact_mod_cast (show 2 ≤ Ideal.absNorm 𝔭 by omega)
  have h3 : (Ideal.absNorm 𝔭 : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
  have h4 : 0 < (Ideal.absNorm 𝔭 : ℝ)⁻¹ := inv_pos.2 (by linarith)
  rw [ThirdPropositionSlot.alphaStd_one]
  unfold etaF
  split_ifs
  · nlinarith
  · nlinarith

theorem alphaL_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    alphaL h L 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * alphaStd K 𝔭 1 := by
  have hq : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by exact_mod_cast (absNorm_pos h𝔭).ne'
  unfold alphaL
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop (vd h L 𝔭 + 1)] with k hk
  rw [akCount_eq hK hF hs hd hL hLi h1 h𝔭 (by omega), h1]
  push_cast
  rw [ThirdPropositionSlot.normRepCount_extP hK hF h𝔭 (by omega), eq_div_iff (pow_ne_zero _ hq)]
  have e1 : (Ideal.absNorm 𝔭 : ℝ) ^ (2 * vd h L 𝔭) * (Ideal.absNorm 𝔭 : ℝ) ^ (k - vd h L 𝔭) =
      (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (k * 1 ^ 2) := by
    rw [← pow_add, ← pow_add]
    congr 1
    rw [one_pow, mul_one]
    omega
  linear_combination (-alphaStd K 𝔭 1) * e1

end U3

theorem localFactor_rank_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    lamP h L 𝔭 = 1 := by
  have hq : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by exact_mod_cast (U3.absNorm_pos h𝔭).ne'
  unfold lamP
  rw [U3.alphaL_eq hK hF hs hd hL hLi h1 h𝔭, h1, one_mul, mul_comm]
  exact div_self (mul_ne_zero (pow_ne_zero _ hq) (U3.alphaStd_one_ne_zero h𝔭))

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem exists_ne_zero_of_isLattice {A : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A) :
    ∃ a ∈ A, a ≠ 0 := by
  by_contra hne
  push_neg at hne
  have h2 : Submodule.span K (A : Set K) = ⊥ := by
    rw [Submodule.span_eq_bot]; exact hne
  have h3 : (1 : K) ∈ Submodule.span K (A : Set K) := by
    rw [hA.span_eq_top]; exact Submodule.mem_top
  rw [h2, Submodule.mem_bot] at h3
  exact one_ne_zero h3

theorem span_eq_top_of_ne_zero {A : Submodule (𝓞 K) K} {a : K} (ha : a ∈ A) (h0 : a ≠ 0) :
    Submodule.span K (A : Set K) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x = (x * a⁻¹) • a := by rw [smul_eq_mul, mul_assoc, inv_mul_cancel₀ h0, mul_one]
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ha)

theorem isLattice_mul {A B : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsLattice K B) : Submodule.IsLattice K (A * B) := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_isLattice hA
  obtain ⟨b, hb, hb0⟩ := exists_ne_zero_of_isLattice hB
  exact ⟨hA.fg.mul hB.fg, span_eq_top_of_ne_zero (Submodule.mul_mem_mul ha hb) (mul_ne_zero ha0 hb0)⟩

theorem exists_inv {A : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A) :
    ∃ A' : Submodule (𝓞 K) K, Submodule.IsLattice K A' ∧ A' * A = 1 := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_isLattice hA
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨A, FractionalIdeal.isFractional_of_fg hA.fg⟩
  have hI : I ≠ 0 := by
    intro h
    have h' : a ∈ (I : Submodule (𝓞 K) K) := ha
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at h'
    exact ha0 h'
  have hmul : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) * A = 1 := by
    have e := congrArg (fun J : FractionalIdeal (𝓞 K)⁰ K => (J : Submodule (𝓞 K) K))
      (inv_mul_cancel₀ hI)
    have e2 : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) * (I : Submodule (𝓞 K) K) = 1 := by
      simpa only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one] using e
    exact e2
  refine ⟨_, ⟨FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_⟩, hmul⟩
  have hne : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥ := by
    intro hb
    rw [hb, Submodule.bot_mul] at hmul
    have h1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.one_le.1 le_rfl
    rw [← hmul, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact span_eq_top_of_ne_zero hc hc0

def mulE (I J : Submodule (𝓞 K) K) (hJI : J * I = 1) :
    Submodule (𝓞 K) K ≃ Submodule (𝓞 K) K where
  toFun M := I * M
  invFun M := J * M
  left_inv M := by change J * (I * M) = M; rw [← mul_assoc, hJI, one_mul]
  right_inv M := by change I * (J * M) = M; rw [← mul_assoc, mul_comm I J, hJI, one_mul]

theorem gmap_mul (g : K ≃ₗ[K] K) (I M : Submodule (𝓞 K) K) : I * gmap g M = gmap g (I * M) := by
  have key : ∀ x y : K, g (x * y) = x * g y := fun x y => by
    simpa only [smul_eq_mul] using g.map_smul x y
  unfold gmap
  apply le_antisymm
  · refine Submodule.mul_le.2 fun i hi y hy => ?_
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨i * m, Submodule.mul_mem_mul hi hm, ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]
  · refine Submodule.map_le_iff_le_comap.2 (Submodule.mul_le.2 fun i hi m hm => ?_)
    rw [Submodule.mem_comap]
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]
    exact Submodule.mul_mem_mul hi (Submodule.mem_map_of_mem hm)

theorem ne_zero_of_mem_hcompl {p : Ideal (𝓞 K)} (hp : p.IsMaximal) {s : 𝓞 K}
    (hs : s ∈ hcompl (K := K) p) : s ≠ 0 := by
  intro h0
  exact Formalism.HermitianLatticesTheory.genusBasic_hS (K := K) p hp s hs (by rw [h0]; exact p.zero_mem)

theorem loc_mul {p : Ideal (𝓞 K)} (hp : p.IsMaximal) (I M : Submodule (𝓞 K) K) :
    I * loc (K := K) p M = loc (K := K) p (I * M) := by
  apply le_antisymm
  · refine Submodule.mul_le.2 fun i hi y hy => ?_
    have hy' : ∃ s ∈ hcompl (K := K) p, s • y ∈ M := hy
    obtain ⟨s, hs, hsy⟩ := hy'
    show ∃ s ∈ hcompl (K := K) p, s • (i * y) ∈ I * M
    refine ⟨s, hs, ?_⟩
    have e : s • (i * y) = i * (s • y) := by rw [Algebra.smul_def, Algebra.smul_def]; ring
    rw [e]
    exact Submodule.mul_mem_mul hi hsy
  · intro x hx
    have hx' : ∃ s ∈ hcompl (K := K) p, s • x ∈ I * M := hx
    obtain ⟨s, hs, hsx⟩ := hx'
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact ne_zero_of_mem_hcompl hp hs
    have hle : I * M ≤ (I * loc (K := K) p M).comap
        (LinearMap.mulLeft (𝓞 K) (algebraMap (𝓞 K) K s)⁻¹) := by
      refine Submodule.mul_le.2 fun i hi m hm => ?_
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
      have e : (algebraMap (𝓞 K) K s)⁻¹ * (i * m) = i * ((algebraMap (𝓞 K) K s)⁻¹ * m) := by ring
      rw [e]
      refine Submodule.mul_mem_mul hi ?_
      show ∃ t ∈ hcompl (K := K) p, t • ((algebraMap (𝓞 K) K s)⁻¹ * m) ∈ M
      refine ⟨s, hs, ?_⟩
      rw [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
      exact hm
    have h2 := hle hsx
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, Algebra.smul_def, ← mul_assoc,
      inv_mul_cancel₀ hs0, one_mul] at h2
    exact h2

theorem form_eq (h : K →ₗ⋆[K] K →ₗ[K] K) (x y : K) : h x y = star x * y * h 1 1 := by
  rw [show h x y = h (x • (1 : K)) (y • (1 : K)) by simp only [smul_eq_mul, mul_one],
    LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply]
  simp only [smul_eq_mul]
  ring

theorem mem_isom_iff {h : K →ₗ⋆[K] K →ₗ[K] K} (h1 : h 1 1 ≠ 0) (g : K ≃ₗ[K] K) :
    g ∈ isom h ↔ star (g 1) * g 1 = 1 := by
  have hg : ∀ x, g x = x * g 1 := fun x => by
    rw [show g x = g (x • (1 : K)) by rw [smul_eq_mul, mul_one], LinearEquiv.map_smul, smul_eq_mul]
  constructor
  · intro hm
    have hm' : ∀ x y, h (g x) (g y) = h x y := hm
    have e := hm' 1 1
    rw [form_eq h (g 1) (g 1)] at e
    exact mul_right_cancel₀ h1 (by rw [one_mul]; exact e)
  · intro he
    show ∀ x y, h (g x) (g y) = h x y
    intro x y
    rw [form_eq h (g x) (g y), form_eq h x y, hg x, hg y, star_mul']
    calc star x * star (g 1) * (y * g 1) * h 1 1 = star x * y * (star (g 1) * g 1) * h 1 1 := by ring
      _ = star x * y * h 1 1 := by rw [he, mul_one]

theorem mass_eq_of_lattices {h₁ h₂ : K →ₗ⋆[K] K →ₗ[K] K} (hn₁ : h₁ 1 1 ≠ 0) (hn₂ : h₂ 1 1 ≠ 0)
    {A B : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B)
    (hex : ∃ s, IsClassReps h₁ A s) : mass h₂ B = mass h₁ A := by
  obtain ⟨A', hA', hA'A⟩ := exists_inv hA
  obtain ⟨B', hB', hB'B⟩ := exists_inv hB
  have hC : Submodule.IsLattice K (B * A') := isLattice_mul hB hA'
  have hJ : Submodule.IsLattice K (A * B') := isLattice_mul hA hB'
  have hJC : (A * B') * (B * A') = 1 := by
    calc (A * B') * (B * A') = (A' * A) * (B' * B) := by ring
      _ = 1 := by rw [hA'A, hB'B, one_mul]
  have t1 : ∀ g : K ≃ₗ[K] K, (Equiv.refl (K ≃ₗ[K] K)) g ∈ isom h₂ ↔ g ∈ isom h₁ := fun g => by
    rw [Equiv.refl_apply, mem_isom_iff hn₂, mem_isom_iff hn₁]
  have t2 : ∀ (g : K ≃ₗ[K] K) (M : Submodule (𝓞 K) K),
      mulE (B * A') (A * B') hJC (gmap g M) =
        gmap ((Equiv.refl (K ≃ₗ[K] K)) g) (mulE (B * A') (A * B') hJC M) := fun g M =>
    gmap_mul g (B * A') M
  have t3 : ∀ (p : Ideal (𝓞 K)), p.IsMaximal → ∀ (M : Submodule (𝓞 K) K),
      mulE (B * A') (A * B') hJC (loc p M) = loc p (mulE (B * A') (A * B') hJC M) :=
    fun p hp M => loc_mul hp (B * A') M
  have t4 : ∀ (M : Submodule (𝓞 K) K),
      Submodule.IsLattice K (mulE (B * A') (A * B') hJC M) ↔ Submodule.IsLattice K M := by
    intro M
    show Submodule.IsLattice K (B * A' * M) ↔ Submodule.IsLattice K M
    constructor
    · intro hM
      have e := isLattice_mul hJ hM
      rwa [← mul_assoc, hJC, one_mul] at e
    · intro hM
      exact isLattice_mul hC hM
  have hΦA : mulE (B * A') (A * B') hJC A = B := by
    show B * A' * A = B
    rw [mul_assoc, hA'A, mul_one]
  have he := (mass_transfer (mulE (B * A') (A * B') hJC) (Equiv.refl _) t1 t2 t3 t4 hex).2
  rw [hΦA] at he
  exact he

end Formalism.HermitianLattices.Ext.L3.RankOne
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem trace_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hsum := trace_eq_sum_embeddings ℂ (K := ℚ) (x := h x x)
  have hre : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    have := congrArg Complex.re hsum
    simpa [Complex.re_sum] using this
  have hne : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hd x hx σ.toRingHom) Finset.univ_nonempty
  exact_mod_cast hre ▸ hpos

theorem exists_model [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) (h1 : finrank K V = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) :
    ∃ (h' : K →ₗ⋆[K] K →ₗ[K] K) (A : Submodule (𝓞 K) K), h' 1 1 ≠ 0 ∧ Submodule.IsLattice K A ∧
      (∃ s, IsClassReps h' A s) ∧ mass h' A = mass h L := by
  let b := Module.finBasisOfFinrankEq K V h1
  let φ : V ≃ₗ[K] K := b.equivFun.trans (LinearEquiv.funUnique (Fin 1) K K)
  let h' : K →ₗ⋆[K] K →ₗ[K] K := (h.comp φ.symm.toLinearMap).compl₂ φ.symm.toLinearMap
  have hh' : ∀ x y, h' (φ x) (φ y) = h x y := by
    intro x y
    simp [h']
  have htr := trace_pos hd
  obtain ⟨hex, -, -⟩ := Formalism.HermitianLatticesTheory.massBasic K V h hs htr L hL
  obtain ⟨hex', hm⟩ := mass_mapE φ hh' hex
  refine ⟨h', mapE φ L, ?_, isLattice_mapE φ hL, hex', hm⟩
  have h0 : φ.symm 1 ≠ 0 := by simp
  intro hz
  have := htr _ h0
  have hz' : h (φ.symm 1) (φ.symm 1) = 0 := by simpa [h'] using hz
  rw [hz', map_zero] at this
  exact lt_irrefl _ this

end RankOne

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_massConst_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c := by
  obtain ⟨h₀, hh⟩ : ∃ h₀ : K →ₗ⋆[K] K →ₗ[K] K, ∀ x y, h₀ x y = star x * y :=
    ⟨LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y)
      (fun x y z => by simp [add_mul]) (fun a x y => by simp [smul_eq_mul, mul_assoc, starRingEnd_apply])
      (fun x y z => by simp [mul_add]) (fun a x y => by simp [smul_eq_mul, mul_left_comm]),
      fun _ _ => rfl⟩
  have hs₀ : h₀.IsSymm := by
    first
      | (intro x y; simp [hh, starRingEnd_apply, mul_comm])
      | (constructor; intro x y; simp [hh, starRingEnd_apply, mul_comm])
  have hd₀ : IsTotPosDef h₀ := by
    intro x hx φ
    have hx' : φ x ≠ 0 := (map_ne_zero φ).mpr hx
    have : φ (h₀ x x) = ((Complex.normSq (φ x) : ℝ) : ℂ) := by
      rw [hh, map_mul, hK.2.1 φ x, Complex.normSq_eq_conj_mul_self]
    rw [this, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hx'
  have hn₀ : h₀ 1 1 ≠ 0 := by simp [hh]
  set L₀ : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}
  have hL₀ : Submodule.IsLattice K L₀ := by
    refine ⟨Submodule.fg_span_singleton _, ?_⟩
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : (1 : K) ∈ Submodule.span K (L₀ : Set K) :=
      Submodule.subset_span (Submodule.subset_span rfl)
    simpa using Submodule.smul_mem _ y h1
  obtain ⟨hex₀, -, hpos₀⟩ := Formalism.HermitianLatticesTheory.massBasic K K h₀ hs₀ (RankOne.trace_pos hd₀) L₀ hL₀
  refine ⟨Formalism.HermitianLatticesTheory.mass h₀ L₀, hpos₀, ?_⟩
  intro V _ _ _ _ _ h L hs hd h1 hL hLi
  obtain ⟨h', A, hn', hA, -, hm⟩ := RankOne.exists_model hs hd h1 hL
  have hlam : lamG F h L = 1 := by
    unfold lamG
    exact (tprod_congr fun p => localFactor_rank_one hK hF hs hd hL hLi h1 p.2).trans tprod_one
  rw [hlam, mul_one, ← hm]
  exact RankOne.mass_eq_of_lattices hn₀ hn' hL₀ hA hex₀

end Formalism.HermitianLattices.Ext.L3
end
end
