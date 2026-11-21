import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoMeanAlphaN
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepMassEqProdPsi
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsGlobalOfFibLocNeZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormSpanSingletonEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeVdLeOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinAA

open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans localValuationFiltration

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

def rd (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k j : ℕ) :
    (𝓞 K ⧸ extP K 𝔭 ^ k) →+* (𝓞 K ⧸ extP K 𝔭 ^ (k - j)) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.sub_le k j))

theorem rd_mk (𝔭 : Ideal (𝓞 F)) (k j : ℕ) (a : 𝓞 K) :
    rd K 𝔭 k j (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

theorem rd_surjective (𝔭 : Ideal (𝓞 F)) (k j : ℕ) : Function.Surjective (rd K 𝔭 k j) :=
  Ideal.Quotient.factor_surjective _

theorem rd_star [Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k j : ℕ) (a : 𝓞 K ⧸ extP K 𝔭 ^ k) :
    rd K 𝔭 k j (star a) = star (rd K 𝔭 k j a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  show rd K 𝔭 k j (NormLifting.conjQ _ _ (Ideal.Quotient.mk _ a)) =
    NormLifting.conjQ _ _ (rd K 𝔭 k j (Ideal.Quotient.mk _ a))
  rw [rd_mk, NormLifting.conjQ_mk, NormLifting.conjQ_mk, rd_mk]

private theorem iota_mul_mem_extP_pow_iff_mem_pow_sub_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0)
    {k : ℕ} (hk : vF 𝔭 c ≤ k) (x : 𝓞 K) :
    ι c * x ∈ extP K 𝔭 ^ k ↔ x ∈ extP K 𝔭 ^ (k - vF 𝔭 c) := by
  constructor
  · intro h
    obtain ⟨J, hJ⟩ : 𝔭 ^ vF 𝔭 c ∣ Ideal.span {c} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr (localValuationFiltration.mem_pow_vF h𝔭 hc))
    have hJp : ¬ J ≤ 𝔭 := by
      intro hle
      apply localValuationFiltration.notMem_pow_vF h𝔭 hc
      have hle' : Ideal.span {c} ≤ 𝔭 ^ (vF 𝔭 c + 1) := by
        rw [hJ, pow_succ]; exact Ideal.mul_mono_right hle
      exact hle' (Ideal.mem_span_singleton_self c)
    have hcop : IsCoprime 𝔭 J := by
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hJp (le_sup_right.trans (h𝔭.eq_of_le hne le_sup_left).symm.le)
    have hcopK : IsCoprime (extP K 𝔭) (J.map ι) := by
      rw [Ideal.isCoprime_iff_sup_eq] at hcop ⊢
      show 𝔭.map ι ⊔ J.map ι = ⊤
      rw [← Ideal.map_sup, hcop, Ideal.map_top]
    have hinj : Function.Injective ι := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)
    have h𝔭0 : 𝔭 ≠ ⊥ := by
      intro h0
      have := reductionMapsOfForms.absNorm_pos h𝔭
      rw [h0, Ideal.absNorm_bot] at this
      exact lt_irrefl _ this
    have hP0 : extP K 𝔭 ≠ ⊥ := by
      show 𝔭.map ι ≠ ⊥
      rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    have hsc : Ideal.span {ι c} = (Ideal.span {c}).map ι := by
      rw [Ideal.map_span, Set.image_singleton]
    have hspan : Ideal.span {ι c * x} =
        extP K 𝔭 ^ vF 𝔭 c * (J.map ι * Ideal.span {x}) := by
      rw [← Ideal.span_singleton_mul_span_singleton, hsc, hJ, Ideal.map_mul, Ideal.map_pow,
        mul_assoc]
      rfl
    have hle : extP K 𝔭 ^ k ∣ Ideal.span {ι c * x} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr h)
    rw [hspan, show k = vF 𝔭 c + (k - vF 𝔭 c) by omega, pow_add] at hle
    have h2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hP0)).mp hle
    have h3 := (hcopK.pow_left (m := k - vF 𝔭 c)).dvd_of_dvd_mul_left h2
    exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp h3)
  · intro h
    have h' := Ideal.mul_mem_mul (localizedQuotients.ι_mem_pow (K := K) (localValuationFiltration.mem_pow_vF h𝔭 hc)) h
    rwa [← pow_add, show vF 𝔭 c + (k - vF 𝔭 c) = k by omega] at h'

theorem mul_eq_zero_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ}
    (hk : vF 𝔭 c ≤ k) (z : 𝓞 K ⧸ extP K 𝔭 ^ k) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) * z = 0 ↔ rd K 𝔭 k (vF 𝔭 c) z = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← map_mul, rd_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  exact iota_mul_mem_extP_pow_iff_mem_pow_sub_vF h𝔭 hc hk x

theorem mul_eq_mul_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ}
    (hk : vF 𝔭 c ≤ k) (x y : 𝓞 K ⧸ extP K 𝔭 ^ k) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) * x = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) * y ↔
      rd K 𝔭 k (vF 𝔭 c) x = rd K 𝔭 k (vF 𝔭 c) y := by
  rw [← sub_eq_zero, ← mul_sub, mul_eq_zero_iff h𝔭 hc hk, map_sub, sub_eq_zero]

theorem card_ker_rd (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k j : ℕ} (hjk : j ≤ k) :
    Nat.card (RingHom.ker (rd K 𝔭 k j)) = Ideal.absNorm 𝔭 ^ (2 * j) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (RingHom.ker (rd K 𝔭 k j))
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective (rd_surjective 𝔭 k j)).toEquiv,
    idealPowerSpanBounds.absNorm_extP_pow hK hF h𝔭, idealPowerSpanBounds.absNorm_extP_pow hK hF h𝔭] at h1
  have hpos : 0 < Ideal.absNorm 𝔭 ^ (2 * (k - j)) := pow_pos (reductionMapsOfForms.absNorm_pos h𝔭) _
  have h2 : Ideal.absNorm 𝔭 ^ (2 * k) = Ideal.absNorm 𝔭 ^ (2 * j) * Ideal.absNorm 𝔭 ^ (2 * (k - j)) := by
    rw [← pow_add]; congr 1; omega
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right hpos (by rw [← h1])).symm

variable {κ : Type} [Fintype κ] [DecidableEq κ] [Fact (IsFixF K F)]

theorem map_smul_mk (𝔭 : Ideal (𝓞 F)) (k : ℕ) (c : 𝓞 F) (H : Matrix κ κ (𝓞 K)) :
    (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) =
      Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) • H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  ext i j
  show Ideal.Quotient.mk _ (ι c * H i j) =
    Ideal.Quotient.mk _ (ι c) * Ideal.Quotient.mk _ (H i j)
  exact map_mul _ _ _

private theorem card_subtype_comp_eq_card_mul_card_ker_of_surjective {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Surjective f) (T : B → Prop) :
    Nat.card {a : A // T (f a)} = Nat.card {b : B // T b} * Nat.card (AddMonoidHom.ker f) := by
  have hs : ∀ b, f (Function.surjInv hf b) = b := Function.surjInv_eq hf
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact
    { toFun := fun a => (⟨f a.1, a.2⟩, ⟨a.1 - Function.surjInv hf (f a.1), by
        rw [AddMonoidHom.mem_ker, map_sub, hs, sub_self]⟩)
      invFun := fun p => ⟨Function.surjInv hf p.1.1 + p.2.1, by
        rw [map_add, hs, AddMonoidHom.mem_ker.mp p.2.2, add_zero]; exact p.1.2⟩
      left_inv := fun a => Subtype.ext (by
        show Function.surjInv hf (f a.1) + (a.1 - Function.surjInv hf (f a.1)) = a.1
        abel)
      right_inv := fun p => by
        have e : f (Function.surjInv hf p.1.1 + p.2.1) = p.1.1 := by
          rw [map_add, hs, AddMonoidHom.mem_ker.mp p.2.2, add_zero]
        refine Prod.ext (Subtype.ext e) (Subtype.ext ?_)
        show Function.surjInv hf p.1.1 + p.2.1 - Function.surjInv hf (f (Function.surjInv hf p.1.1 + p.2.1)) = p.2.1
        rw [e]; abel }

private theorem card_ker_mapMatrix_eq_card_ker_pow_sq {A B : Type} [Ring A] [Ring B] (R : A →+* B) :
    Nat.card (AddMonoidHom.ker (R.toAddMonoidHom.mapMatrix : Matrix κ κ A →+ Matrix κ κ B)) =
      Nat.card (RingHom.ker R) ^ (Fintype.card κ ^ 2) := by
  have e : AddMonoidHom.ker (R.toAddMonoidHom.mapMatrix : Matrix κ κ A →+ Matrix κ κ B) ≃
      (κ → κ → RingHom.ker R) :=
    { toFun := fun X i j => ⟨X.1 i j, by
        have h := congrFun (congrFun (AddMonoidHom.mem_ker.mp X.2) i) j
        exact (RingHom.mem_ker).mpr h⟩
      invFun := fun g => ⟨Matrix.of fun i j => (g i j).1, by
        rw [AddMonoidHom.mem_ker]
        ext i j
        exact (RingHom.mem_ker).mp (g i j).2⟩
      left_inv := fun X => rfl
      right_inv := fun g => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := κ), ← pow_mul, sq]

private theorem card_ker_compLeft_eq_card_ker_pow {A B : Type} [Ring A] [Ring B] (R : A →+* B) :
    Nat.card (AddMonoidHom.ker (AddMonoidHom.compLeft R.toAddMonoidHom κ)) =
      Nat.card (RingHom.ker R) ^ Fintype.card κ := by
  have e : AddMonoidHom.ker (AddMonoidHom.compLeft R.toAddMonoidHom κ) ≃ (κ → RingHom.ker R) :=
    { toFun := fun x i => ⟨x.1 i, by
        have h := congrFun (AddMonoidHom.mem_ker.mp x.2) i
        exact (RingHom.mem_ker).mpr h⟩
      invFun := fun g => ⟨fun i => (g i).1, by
        rw [AddMonoidHom.mem_ker]
        funext i
        exact (RingHom.mem_ker).mp (g i).2⟩
      left_inv := fun x => rfl
      right_inv := fun g => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := κ)]

theorem akM_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F}
    (hc : c ≠ 0) {k : ℕ} (hk : vF 𝔭 c ≤ k) (H : Matrix κ κ (𝓞 K)) :
    Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) //
        Xᴴ * (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X =
          (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))} =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * Fintype.card κ ^ 2) *
        Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (k - vF 𝔭 c)) //
          Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) * X =
            H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c)))} := by
  have hHR : (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))).map (rd K 𝔭 k (vF 𝔭 c)) =
      H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) := by
    rw [Matrix.map_map]; rfl
  have key : ∀ X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k),
      (Xᴴ * (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X =
          (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) ↔
        (X.map (rd K 𝔭 k (vF 𝔭 c)))ᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *
            X.map (rd K 𝔭 k (vF 𝔭 c)) =
          H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) := by
    intro X
    have hR : (X.map (rd K 𝔭 k (vF 𝔭 c)))ᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *
        X.map (rd K 𝔭 k (vF 𝔭 c)) =
        (Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X).map (rd K 𝔭 k (vF 𝔭 c)) := by
      rw [Matrix.map_mul, Matrix.map_mul, ← hHR,
        Matrix.conjTranspose_map _ (fun a => rd_star 𝔭 k (vF 𝔭 c) a)]
    rw [map_smul_mk, Matrix.mul_smul, Matrix.smul_mul, hR, ← hHR, ← Matrix.ext_iff,
      ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
    exact mul_eq_mul_iff h𝔭 hc hk _ _
  have hsurj : Function.Surjective
      ((rd K 𝔭 k (vF 𝔭 c)).toAddMonoidHom.mapMatrix :
        Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) →+ Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (k - vF 𝔭 c))) := by
    intro Y
    refine ⟨Y.map (Function.surjInv (rd_surjective 𝔭 k (vF 𝔭 c))), ?_⟩
    ext i j
    exact Function.surjInv_eq (rd_surjective 𝔭 k (vF 𝔭 c)) (Y i j)
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  refine (card_subtype_comp_eq_card_mul_card_ker_of_surjective _ hsurj (fun Y => Yᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) * Y =
      H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))))).trans ?_
  rw [card_ker_mapMatrix_eq_card_ker_pow_sq, card_ker_rd hK Fact.out h𝔭 hk, ← pow_mul, mul_comm]

theorem nkM_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F}
    (hc : c ≠ 0) (n : 𝓞 F) {k : ℕ} (hk : vF 𝔭 c ≤ k) (H : Matrix κ κ (𝓞 K)) :
    Nat.card {x : κ → 𝓞 K ⧸ extP K 𝔭 ^ k //
        star x ⬝ᵥ ((ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ x) =
          Ideal.Quotient.mk _ (ι (c * n))} =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * Fintype.card κ) *
        Nat.card {x : κ → 𝓞 K ⧸ extP K 𝔭 ^ (k - vF 𝔭 c) //
          star x ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *ᵥ x) =
            Ideal.Quotient.mk _ (ι n)} := by
  have key : ∀ x : κ → 𝓞 K ⧸ extP K 𝔭 ^ k,
      (star x ⬝ᵥ ((ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ x) =
          Ideal.Quotient.mk _ (ι (c * n))) ↔
        star (fun i => rd K 𝔭 k (vF 𝔭 c) (x i)) ⬝ᵥ
            (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *ᵥ
              fun i => rd K 𝔭 k (vF 𝔭 c) (x i)) =
          Ideal.Quotient.mk _ (ι n) := by
    intro x
    have e : rd K 𝔭 k (vF 𝔭 c) (star x ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ x)) =
        star (fun i => rd K 𝔭 k (vF 𝔭 c) (x i)) ⬝ᵥ
            (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *ᵥ
              fun i => rd K 𝔭 k (vF 𝔭 c) (x i)) := by
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, rd_star,
        Matrix.map_apply, rd_mk]
    rw [map_smul_mk, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, map_mul, map_mul,
      mul_eq_mul_iff h𝔭 hc hk, e, rd_mk]
  have hsurj : Function.Surjective
      (AddMonoidHom.compLeft (rd K 𝔭 k (vF 𝔭 c)).toAddMonoidHom κ) := by
    intro y
    refine ⟨fun i => Function.surjInv (rd_surjective 𝔭 k (vF 𝔭 c)) (y i), ?_⟩
    funext i
    exact Function.surjInv_eq (rd_surjective 𝔭 k (vF 𝔭 c)) (y i)
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  refine (card_subtype_comp_eq_card_mul_card_ker_of_surjective _ hsurj (fun y => star y ⬝ᵥ
      (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *ᵥ y) = Ideal.Quotient.mk _ (ι n))).trans ?_
  rw [card_ker_compLeft_eq_card_ker_pow, card_ker_rd hK Fact.out h𝔭 hk, ← pow_mul, mul_comm]

end Formalism.HermitianLattices.Ext.L3.PinAA
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] in
theorem isIntegralLat_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (c : 𝓞 F) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (algebraMap F K (c : F) • h) L := by
  intro x hx y hy
  have h1 : algebraMap F K (c : F) ∈ (1 : Submodule (𝓞 K) K) :=
    Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 K) c, rfl⟩
  have h2 := Submodule.mul_mem_mul h1 (hLi x hx y hy)
  rw [one_mul] at h2
  exact h2

theorem akCount_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    akCount (algebraMap F K (c : F) • h) L 𝔭 k =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V ^ 2) * akCount h L 𝔭 (k - vF 𝔭 c) := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, -⟩ := localValuationFiltration.exists_local_data hF hs hd hL hLi h𝔭
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.akCount_eq _ h𝔭 b hb hH', integralBasisSpans.akCount_eq h h𝔭 b hb hH, PinAA.akM_smul hK h𝔭 hc hk,
    Fintype.card_fin]

theorem nkCount_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (n : 𝓞 F) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V) * nkCount h L 𝔭 (k - vF 𝔭 c) n := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, -⟩ := localValuationFiltration.exists_local_data hF hs hd hL hLi h𝔭
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.nkCount_eq _ h𝔭 b hb hH', integralBasisSpans.nkCount_eq h h𝔭 b hb hH, PinAA.nkM_smul hK h𝔭 hc n hk,
    Fintype.card_fin]

omit [NumberField K] [StarRing K] [Algebra F K] in
theorem pow_notMem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} {j : ℕ} (hc : c ∉ 𝔭 ^ (j + 1))
    (m : ℕ) : c ^ m ∉ 𝔭 ^ (m * j + 1) := by
  induction m with
  | zero =>
    rw [pow_zero, zero_mul, zero_add, pow_one]
    exact fun e => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 e)
  | succ m ih =>
    rw [show (m + 1) * j + 1 = m * j + j + 1 by ring, pow_succ c]
    exact idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) ih hc

theorem gram_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 F) (x : Fin (finrank K V) → V) :
    (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)).det =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V)) *
        (Matrix.of fun i j => h (x i) (x j)).det := by
  have e : (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)) =
      algebraMap F K (c : F) • Matrix.of fun i j => h (x i) (x j) := by
    ext i j
    rfl
  rw [e, Matrix.det_smul, Fintype.card_fin]
  congr 1
  simp only [map_pow]
  rfl

theorem discrIdeal_smul_le_iff {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0)
    (e : ℕ) :
    discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ (finrank K V * vF 𝔭 c + e) ↔
      discrIdeal h L ≤ extP K 𝔭 ^ e := by
  constructor
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    apply idealPowerSpanBounds.mem_of_mul_mem h𝔭 (pow_notMem h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hc) (finrank K V))
    apply hle
    exact Ideal.subset_span ⟨x, hx, by rw [gram_smul, map_mul, ez]⟩
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    obtain ⟨g, -, hdet⟩ := LocF.exists_gram hLi x hx
    have hz : z = algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) * g.det := by
      apply RingOfIntegers.coe_injective
      show algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K _
      rw [ez, gram_smul, map_mul, hdet]
    have h1 : g.det ∈ extP K 𝔭 ^ e := hle (Ideal.subset_span ⟨x, hx, hdet⟩)
    have h2 : algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) ∈ extP K 𝔭 ^ (finrank K V * vF 𝔭 c) := by
      apply localizedQuotients.ι_mem_pow
      rw [mul_comm, pow_mul]
      exact Ideal.pow_mem_pow (localValuationFiltration.mem_pow_vF h𝔭 hc) _
    show z ∈ _
    rw [hz, pow_add]
    exact Ideal.mul_mem_mul h2 h1

theorem vd_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) :
    vd (algebraMap F K (c : F) • h) L 𝔭 = vd h L 𝔭 + finrank K V * vF 𝔭 c := by
  have hD := LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi
  have hE : extP K 𝔭 ≠ ⊤ := by
    intro e
    apply h𝔭.ne_top
    rw [Ideal.eq_top_iff_one, ← pow_one 𝔭, ← idealPowerSpanBounds.mem_pow_iff (K := K), pow_one, e]
    trivial
  have hb : BddAbove {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    apply hD
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isDomain (extP K 𝔭) hE]
    refine le_iInf fun k => ?_
    obtain ⟨e, he, hke⟩ := hnb k
    exact he.trans (Ideal.pow_le_pow_right hke.le)
  have hmem : vd h L 𝔭 ∈ {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} :=
    Nat.sSup_mem ⟨0, by simp⟩ hb
  have hg : IsGreatest {e : ℕ | discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ e}
      (vd h L 𝔭 + finrank K V * vF 𝔭 c) := by
    constructor
    · rw [add_comm]
      exact (discrIdeal_smul_le_iff hLi h𝔭 hc _).2 hmem
    · intro e' he'
      by_cases hlt : e' ≤ finrank K V * vF 𝔭 c
      · omega
      · obtain ⟨e, rfl⟩ : ∃ e, e' = finrank K V * vF 𝔭 c + e := ⟨e' - finrank K V * vF 𝔭 c, by omega⟩
        have h1 : e ≤ vd h L 𝔭 := le_csSup hb ((discrIdeal_smul_le_iff hLi h𝔭 hc e).1 he')
        omega
  exact hg.csSup_eq

end Formalism.HermitianLattices.Ext.L3.PinA
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinC

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

private theorem VecSplit_adjoin_le_locF_of_le_locF (S : VecSplit h h') {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime)
    {T T' : Submodule (𝓞 K) V'} (hT : T ≤ locF 𝔭 T') :
    S.adjoin T ≤ locF 𝔭 (S.adjoin T') := by
  refine sup_le ?_ ?_
  · rw [Submodule.span_singleton_le_iff_mem]
    exact LocF.le_locF 𝔭 _ (S.x₀_mem_adjoin T')
  · rw [Submodule.map_le_iff_le_comap]
    intro a ha
    obtain ⟨t, ht, hta⟩ := (LocF.mem_locF_iff h𝔭 T' a).mp (hT ha)
    rw [Submodule.mem_comap, LocF.mem_locF_iff h𝔭]
    refine ⟨t, ht, ?_⟩
    rw [← map_smul]
    exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hta)

theorem locF_adjoin_congr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {T T' : Submodule (𝓞 K) V'} (e : locF 𝔭 T = locF 𝔭 T') :
    locF 𝔭 (S.adjoin T) = locF 𝔭 (S.adjoin T') := by
  have key : ∀ {A B : Submodule (𝓞 K) V'}, locF 𝔭 A = locF 𝔭 B →
      locF 𝔭 (S.adjoin A) ≤ locF 𝔭 (S.adjoin B) := by
    intro A B hAB
    have hle := VecSplit_adjoin_le_locF_of_le_locF S h𝔭.isPrime ((LocF.le_locF 𝔭 A).trans hAB.le)
    calc locF 𝔭 (S.adjoin A) ≤ locF 𝔭 (locF 𝔭 (S.adjoin B)) := LocF.locF_mono 𝔭 hle
      _ = locF 𝔭 (S.adjoin B) := LocF.locF_idem 𝔭 _
  exact le_antisymm (key e) (key e.symm)

theorem vd_eq_of_basis (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {m : ℕ} (hm : finrank K V = m) (b : Basis (Fin m) K V)
    (hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L) {g₀ : 𝓞 K}
    (hg : algebraMap (𝓞 K) K g₀ = (Matrix.of fun i j => h (b i) (b j)).det) :
    vd h L 𝔭 = sSup {e : ℕ | g₀ ∈ extP K 𝔭 ^ e} := by
  subst hm
  rw [← localizedQuotients.vd_locF hF h L h𝔭, ← hb, localizedQuotients.vd_locF hF h _ h𝔭, vd, BallB.discrIdeal_span b hg]
  simp only [Ideal.span_singleton_le_iff_mem]

theorem span_range_cons (S : VecSplit h h') {n : ℕ} (x : Fin n → V') :
    Submodule.span (𝓞 K) (Set.range (Fin.cons S.x₀ (fun i => S.ι (x i)) : Fin (n + 1) → V)) =
      S.adjoin (Submodule.span (𝓞 K) (Set.range x)) := by
  rw [Fin.range_cons, Submodule.span_insert, VecSplit.adjoin, Submodule.map_span, ← Set.range_comp]
  rfl

theorem vd_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : vd h' (S.cut L) 𝔭 = vd h L 𝔭 := by
  have hcL : Submodule.IsLattice K (S.cut L) := by
    rw [← S.isLattice_adjoin_iff, S.adjoin_cut h1 hLi hx]
    exact hL
  obtain ⟨b', hb'L, hb'⟩ := LocalSpans.exists_basis_locF hcL h𝔭
  have hint : ∀ i j, h' (b' i) (b' j) ∈ (1 : Submodule (𝓞 K) K) := fun i j =>
    UnimodularLocalization.isIntegralLat_cut S hLi _ (hb'L i) _ (hb'L j)
  choose H hH using fun i j => Submodule.mem_one.mp (hint i j)
  have hg₀ : algebraMap (𝓞 K) K (Matrix.of H).det =
      (Matrix.of fun i j => h' (b' i) (b' j)).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [hH]
  let c : Fin (finrank K V' + 1) → V := Fin.cons S.x₀ (fun i => S.ι (b' i))
  have hli : LinearIndependent K c := by
    refine linearIndependent_finCons.mpr ⟨?_, ?_⟩
    · exact b'.linearIndependent.map' S.ι (LinearMap.ker_eq_bot.mpr S.inj)
    · intro hmem
      have hle : Submodule.span K (Set.range fun i => S.ι (b' i)) ≤ LinearMap.range S.ι :=
        Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨b' i, rfl⟩)
      obtain ⟨a, ha⟩ := hle hmem
      exact S.x₀_not_mem_range a ha
  have hcard : Fintype.card (Fin (finrank K V' + 1)) = finrank K V := by
    rw [Fintype.card_fin]
    exact S.finrank_add_one
  let bb := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbb : ⇑bb = c := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hgram : (Matrix.of fun i j => h (bb i) (bb j)).det =
      (Matrix.of fun i j => h' (b' i) (b' j)).det := by
    rw [hbb, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [c, S.orth, h1, Fin.succAbove_zero]
    congr 1
    ext i j
    simp [S.isom]
  have hspan : locF 𝔭 (Submodule.span (𝓞 K) (Set.range bb)) = locF 𝔭 L := by
    rw [hbb, span_range_cons S b', locF_adjoin_congr hK hF S h𝔭 hb', S.adjoin_cut h1 hLi hx]
  rw [vd_eq_of_basis hF h h𝔭 S.finrank_add_one.symm bb hspan (hg₀.trans hgram.symm),
    vd_eq_of_basis hF h' h𝔭 rfl b' hb' hg₀]

theorem locF_eq_locF_adjoin_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    (h1 : h S.x₀ S.x₀ = 1) {B : Submodule (𝓞 K) V} (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hx : S.x₀ ∈ locF 𝔭 B) :
    locF 𝔭 B = locF 𝔭 (S.adjoin (S.cut B)) := by
  obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
  simp only [locF_eq_loc hK hF hP] at hx ⊢
  refine UnimodularLocalization.loc_eq_loc_adjoin_cut S hP.isPrime hBi hx ?_
  rw [h1, inv_one]
  exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩⟩

theorem vd_cut_of_mem_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {B : Submodule (𝓞 K) V}
    (hB : Submodule.IsLattice K B) (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hx : S.x₀ ∈ locF 𝔭 B) :
    vd h' (S.cut B) 𝔭 = vd h B 𝔭 := by
  have e5 := locF_eq_locF_adjoin_cut hK hF S h1 hBi h𝔭 hx
  have hcB : Submodule.IsLattice K (S.cut B) := StabilizerLattices.isLattice_cut S hB
  have hcBi := UnimodularLocalization.isIntegralLat_cut S hBi
  calc vd h' (S.cut B) 𝔭 = vd h (S.adjoin (S.cut B)) 𝔭 := by
        rw [← vd_cut hK hF hs hd S h1 ((S.isLattice_adjoin_iff _).mpr hcB)
          ((S.isIntegralLat_adjoin_iff hs h1 _).mpr hcBi) (S.x₀_mem_adjoin _) h𝔭, S.cut_adjoin]
    _ = vd h B 𝔭 := by rw [← localizedQuotients.vd_locF hF h _ h𝔭, ← e5, localizedQuotients.vd_locF hF h _ h𝔭]

theorem exists_isom_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hxg : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) :
    ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g' (locF 𝔭 (S.cut L)) = S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) ∧
      Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') (locF 𝔭 L) = Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) := by
  have hML : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) := LocalizedFibreSets.isLattice_gmap g hL
  have hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h (Formalism.HermitianLatticesTheory.gmap g L) := UnimodularLocalization.isIntegralLat_gmap hg hLi
  have hxM : S.x₀ ∈ locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g L) := by rwa [← LocalizedFibreSets.gmap_locF]
  have hxL : S.x₀ ∈ locF 𝔭 L := LocF.le_locF 𝔭 L hx
  have hvA : vd h' (S.cut L) 𝔭 = vd h L 𝔭 := vd_cut hK hF hs hd S h1 hL hLi hx h𝔭
  have hvB : vd h' (S.cut (Formalism.HermitianLatticesTheory.gmap g L)) 𝔭 = vd h L 𝔭 := by
    rw [vd_cut_of_mem_locF hK hF hs hd S h1 hML hMi h𝔭 hxM, UnimodularLocalization.vd_gmap hg]
  have hA := StabilizerLattices.isLattice_cut S hL
  have hB := StabilizerLattices.isLattice_cut S hML
  have hAi := UnimodularLocalization.isIntegralLat_cut S hLi
  have hBi := UnimodularLocalization.isIntegralLat_cut S hMi
  have hs' : h'.IsSymm := S.isSymm hs
  have hd' : IsTotPosDef h' := S.isTotPosDef hd
  obtain ⟨g', hg', hg'e⟩ : ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h',
      Formalism.HermitianLatticesTheory.gmap g' (locF 𝔭 (S.cut L)) = locF 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g L)) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with h0 | h0
    · exact exists_isom_locF_of_vd_zero hK hF hs' hd' hA hB hAi hBi h𝔭 (hvA.trans h0)
        (hvB.trans h0)
    · exact exists_isom_locF_of_vd_one hK hF hs' hd' hA hB hAi hBi h𝔭 (hvA.trans h0)
        (hvB.trans h0)
  refine ⟨g', hg', ?_, ?_⟩
  · rw [hg'e, LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF]
  · rw [LocalizedFibreSets.gmap_locF g 𝔭 L, locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭 hxL, LocalizedFibreSets.gmap_locF,
      SplitBAux.gmap_extOf S g' rfl, locF_eq_locF_adjoin_cut hK hF S h1 hMi h𝔭 hxM]
    exact locF_adjoin_congr hK hF S h𝔭 (by rw [← LocalizedFibreSets.gmap_locF]; exact hg'e)

theorem fibLoc_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) : fibLoc S L 𝔭 (locF 𝔭 (S.cut L)) = 1 := by
  have hxL : S.x₀ ∈ locF 𝔭 L := LocF.le_locF 𝔭 L hx
  rw [fibLoc, Nat.card_eq_one_iff_exists]
  refine ⟨⟨locF 𝔭 L, LocF.locF_idem 𝔭 L, ⟨1, one_mem _, autSub_gmap_one _⟩, hxL,
    by rw [LocalizedFibreSets.cut_locF, LocF.locF_idem]⟩, ?_⟩
  rintro ⟨Λ, -, ⟨g, hg, rfl⟩, hΛx, hΛc⟩
  apply Subtype.ext
  show Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 L
  have hMi := UnimodularLocalization.isIntegralLat_gmap hg hLi
  rw [LocalizedFibreSets.gmap_locF] at hΛx hΛc ⊢
  rw [locF_eq_locF_adjoin_cut hK hF S h1 hMi h𝔭 hΛx,
    locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭 hxL]
  apply locF_adjoin_congr hK hF S h𝔭
  rw [← LocalizedFibreSets.cut_locF, hΛc, LocF.locF_idem]

theorem isLocReps_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) : IsLocReps S L 𝔭 {locF 𝔭 (S.cut L)} := by
  have hcLi := UnimodularLocalization.isIntegralLat_cut S hLi
  refine ⟨?_, ?_⟩
  · intro T hT
    rw [Finset.mem_singleton] at hT
    subst hT
    refine ⟨LocF.locF_idem 𝔭 _, GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hcLi, ?_⟩
    rw [fibLoc_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv]
    exact one_ne_zero
  · intro T hT _ hf
    refine ⟨locF 𝔭 (S.cut L), ⟨Finset.mem_singleton_self _, ?_⟩, ?_⟩
    · obtain ⟨g, hg, hgx, hgT⟩ := UnimodularLocalization.exists_of_fibLoc_ne_zero S hf
      rw [← LocalizedFibreSets.gmap_locF] at hgx
      obtain ⟨g', hg', he, -⟩ := exists_isom_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv hg hgx
      refine ⟨g', hg', ?_⟩
      rw [he, LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF, hgT, hT]
    · rintro T₀ ⟨hT₀, -⟩
      exact Finset.mem_singleton.mp hT₀

theorem exists_aut_map (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) {y : V} (hy : y ∈ locF 𝔭 L) (hyy : h y y = 1) :
    ∃ g ∈ autSub h (locF 𝔭 L), g S.x₀ = y := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hyy
  obtain ⟨g₁, hg₁, hg₁y⟩ := exists_isom_map_of_eq hK hs hd hy0 (hyy.trans h1.symm)
  have hxg : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L) := by
    rw [← hg₁y]
    exact Submodule.mem_map_of_mem hy
  obtain ⟨g', hg', -, he⟩ := exists_isom_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv hg₁ hxg
  refine ⟨g₁⁻¹ * SplitBAux.extOf S g', ⟨mul_mem (inv_mem hg₁) (SplitBAux.extOf_mem_isom hs S hg'), ?_⟩, ?_⟩
  · rw [autSub_gmap_mul, he, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · show g₁⁻¹ (SplitBAux.extOf S g' S.x₀) = y
    rw [SplitBAux.extOf_x₀, ← hg₁y]
    exact g₁.symm_apply_apply y

end Formalism.HermitianLattices.Ext.L3.PinC
end
end

section
open Matrix

namespace Formalism.HermitianLattices.Ext.L3.PinE

variable {A : Type*} [CommRing A] [StarRing A] {κ : Type} [Fintype κ] [DecidableEq κ]

def e₀ : Unit ⊕ κ → A := Pi.single (Sum.inl ()) 1

def HH (H' : Matrix κ κ A) : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A := fromBlocks 1 0 0 H'

theorem form_block (H' X' : Matrix κ κ A) :
    (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A)ᴴ * HH H' * fromBlocks 1 0 0 X' =
      fromBlocks 1 0 0 (X'ᴴ * H' * X') := by
  simp [HH, fromBlocks_conjTranspose, fromBlocks_multiply]

theorem block_mulVec_e₀ (X' : Matrix κ κ A) :
    (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) *ᵥ e₀ = e₀ := by
  unfold e₀
  rw [mulVec_single_one]
  ext i
  rcases i with ⟨⟩ | i <;> simp

theorem eq_block_of_fix {H' : Matrix κ κ A} {Y : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A}
    (hY : Yᴴ * HH H' * Y = HH H') (h0 : Y *ᵥ e₀ = e₀) :
    Y.toBlocks₂₂ᴴ * H' * Y.toBlocks₂₂ = H' ∧ Y = fromBlocks 1 0 0 Y.toBlocks₂₂ := by
  have h11 : Y (Sum.inl ()) (Sum.inl ()) = 1 := by
    have := congrFun h0 (Sum.inl ())
    simpa [e₀, mulVec_single_one] using this
  have h21 : ∀ i, Y (Sum.inr i) (Sum.inl ()) = 0 := by
    intro i
    have := congrFun h0 (Sum.inr i)
    simpa [e₀, mulVec_single_one] using this
  have hA : Y.toBlocks₁₁ = 1 := by
    ext ⟨⟩ ⟨⟩
    simpa [toBlocks₁₁] using h11
  have hC : Y.toBlocks₂₁ = 0 := by
    ext i ⟨⟩
    simpa [toBlocks₂₁] using h21 i
  have hYb : Y = fromBlocks 1 Y.toBlocks₁₂ 0 Y.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks Y]
    rw [hA, hC]
  rw [hYb] at hY
  have key := congrArg Matrix.toBlocks₁₂ hY
  have key2 := congrArg Matrix.toBlocks₂₂ hY
  simp [HH, fromBlocks_conjTranspose, fromBlocks_multiply] at key key2
  refine ⟨?_, ?_⟩
  · simpa [key] using key2
  · rw [key] at hYb
    exact hYb

theorem form_col {H X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A} (hX : Xᴴ * H * X = H)
    (h00 : H (Sum.inl ()) (Sum.inl ()) = 1) : star (X *ᵥ e₀) ⬝ᵥ (H *ᵥ (X *ᵥ e₀)) = 1 := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hX]
  simp [e₀, mulVec_single_one, dotProduct, Fintype.sum_sum_type, h00]

theorem card_split [Finite A] (H' : Matrix κ κ A)
    (htr : ∀ x : Unit ⊕ κ → A, star x ⬝ᵥ (HH H' *ᵥ x) = 1 →
      ∃ G G' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A, Gᴴ * HH H' * G = HH H' ∧ G * G' = 1 ∧ G *ᵥ e₀ = x) :
    Nat.card {X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A // Xᴴ * HH H' * X = HH H'} =
      Nat.card {x : Unit ⊕ κ → A // star x ⬝ᵥ (HH H' *ᵥ x) = 1} *
        Nat.card {X' : Matrix κ κ A // X'ᴴ * H' * X' = H'} := by
  classical
  choose G G' hG using htr
  have h00 : HH H' (Sum.inl ()) (Sum.inl ()) = (1 : A) := by simp [HH]
  have hinv : ∀ x hx, G' x hx * G x hx = 1 := fun x hx => by
    first
      | exact mul_eq_one_comm.mp (hG x hx).2.1
      | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) (hG x hx).2.1
      | exact (Matrix.mul_eq_one_comm (M := G x hx) (N := G' x hx)).mp (hG x hx).2.1
  have hG'form : ∀ x hx, (G' x hx)ᴴ * HH H' * G' x hx = HH H' := by
    intro x hx
    calc (G' x hx)ᴴ * HH H' * G' x hx = (G' x hx)ᴴ * ((G x hx)ᴴ * HH H' * G x hx) * G' x hx := by
          rw [(hG x hx).1]
      _ = (G x hx * G' x hx)ᴴ * HH H' * (G x hx * G' x hx) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = HH H' := by rw [(hG x hx).2.1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hGeq : ∀ x y (hx : star x ⬝ᵥ (HH H' *ᵥ x) = 1) (hy : star y ⬝ᵥ (HH H' *ᵥ y) = 1), x = y →
      G x hx = G y hy ∧ G' x hx = G' y hy := by
    rintro x _ hx hy rfl
    exact ⟨rfl, rfl⟩
  have fixY : ∀ (X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) (hX : Xᴴ * HH H' * X = HH H'),
      (G' (X *ᵥ e₀) (form_col hX h00) * X)ᴴ * HH H' * (G' (X *ᵥ e₀) (form_col hX h00) * X) = HH H' ∧
      (G' (X *ᵥ e₀) (form_col hX h00) * X) *ᵥ e₀ = e₀ := by
    intro X hX
    constructor
    · calc _ = Xᴴ * ((G' (X *ᵥ e₀) (form_col hX h00))ᴴ * HH H' * G' (X *ᵥ e₀) (form_col hX h00)) * X := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = HH H' := by rw [hG'form, hX]
    · have h1 : G' (X *ᵥ e₀) (form_col hX h00) *ᵥ (G (X *ᵥ e₀) (form_col hX h00) *ᵥ e₀) = e₀ := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [(hG _ _).2.2] at h1
      rw [← Matrix.mulVec_mulVec]
      exact h1
  have recon : ∀ (X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) (hX : Xᴴ * HH H' * X = HH H'),
      X = G (X *ᵥ e₀) (form_col hX h00) *
        fromBlocks 1 0 0 (G' (X *ᵥ e₀) (form_col hX h00) * X).toBlocks₂₂ := by
    intro X hX
    rw [← (eq_block_of_fix (fixY X hX).1 (fixY X hX).2).2, ← Matrix.mul_assoc, (hG _ _).2.1,
      Matrix.one_mul]
  let f : {X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A // Xᴴ * HH H' * X = HH H'} →
      {x : Unit ⊕ κ → A // star x ⬝ᵥ (HH H' *ᵥ x) = 1} × {X' : Matrix κ κ A // X'ᴴ * H' * X' = H'} :=
    fun X => (⟨X.1 *ᵥ e₀, form_col X.2 h00⟩,
      ⟨_, (eq_block_of_fix (fixY X.1 X.2).1 (fixY X.1 X.2).2).1⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨X1, hX1⟩ ⟨X2, hX2⟩ h
      simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨hGG, hGG'⟩ := hGeq _ _ (form_col hX1 h00) (form_col hX2 h00) h1
      apply Subtype.ext
      dsimp only
      rw [recon X1 hX1, recon X2 hX2, hGG, h2]
    · rintro ⟨⟨x, hx⟩, ⟨X', hX'⟩⟩
      have hform : (G x hx * fromBlocks 1 0 0 X')ᴴ * HH H' * (G x hx * fromBlocks 1 0 0 X') = HH H' := by
        calc _ = (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A)ᴴ * ((G x hx)ᴴ * HH H' * G x hx) *
              fromBlocks 1 0 0 X' := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = HH H' := by rw [(hG x hx).1, form_block, hX']; rfl
      have hxe : (G x hx * fromBlocks 1 0 0 X') *ᵥ e₀ = x := by
        rw [← Matrix.mulVec_mulVec, block_mulVec_e₀, (hG x hx).2.2]
      refine ⟨⟨_, hform⟩, ?_⟩
      simp only [f]
      obtain ⟨_, hGG'⟩ := hGeq _ _ (form_col hform h00) hx hxe
      refine Prod.ext (Subtype.ext hxe) (Subtype.ext ?_)
      dsimp only
      rw [hGG', ← Matrix.mul_assoc, hinv, Matrix.one_mul, Matrix.toBlocks_fromBlocks₂₂]
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective f hf)

end Formalism.HermitianLattices.Ext.L3.PinE
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinF

open idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

omit [FiniteDimensional K V] in
theorem exists_norm_int (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {y : V} (hy : y ∈ L) :
    ∃ a : 𝓞 F, h y y = algebraMap (𝓞 K) K (ι a) := by
  obtain ⟨z, hz⟩ := (Submodule.mem_one).1 (hLi y hy y hy)
  have hzc : conjO K z = z := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [WA.algebraMap_conjO, hz, Cell.form_self_star hs y]
  obtain ⟨a, ha⟩ := (conjO_eq_iff_mem_range hF z).1 hzc
  exact ⟨a, by rw [ha, hz]⟩

theorem newton (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {N : ℕ} (hN : 1 ≤ N) {y : V}
    (hy : y ∈ L) {a : 𝓞 F} (ha : h y y = algebraMap (𝓞 K) K (ι a)) (ha1 : a - 1 ∈ 𝔭 ^ N) :
    ∃ y' ∈ L, ∃ a' : 𝓞 F, h y' y' = algebraMap (𝓞 K) K (ι a') ∧ a' - 1 ∈ 𝔭 ^ (N + 1) ∧
      y' - y ∈ (extP K 𝔭 ^ N • L : Submodule (𝓞 K) V) := by
  obtain ⟨c, hc⟩ := traceDeterminantCongruences.exists_trace_one hK hF h𝔭 1
  have hc' : c + conjO K c - 1 ∈ extP K 𝔭 ^ 1 := hc
  rw [pow_one] at hc'
  have hEm : ι (a - 1) ∈ extP K 𝔭 ^ N := localizedQuotients.ι_mem_pow ha1
  have hEc : conjO K (ι (a - 1)) = ι (a - 1) := idealPowerSpanBounds.conjO_map hF (a - 1)
  obtain ⟨ν, hν⟩ : ∃ ν : 𝓞 F, ι ν = conjO K (1 - ι (a - 1) * c) * (1 - ι (a - 1) * c) := by
    have : conjO K (conjO K (1 - ι (a - 1) * c) * (1 - ι (a - 1) * c)) =
        conjO K (1 - ι (a - 1) * c) * (1 - ι (a - 1) * c) := by
      rw [map_mul, WA.conjO_conjO, mul_comm]
    exact (conjO_eq_iff_mem_range hF _).1 this
  have ha' : ι a = 1 + ι (a - 1) := by rw [map_sub, map_one]; ring
  refine ⟨(1 - ι (a - 1) * c) • y, L.smul_mem _ hy, ν * a, ?_, ?_, ?_⟩
  · rw [← algebraMap_smul K (1 - ι (a - 1) * c) y]
    simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, starRingEnd_apply]
    rw [ha, map_mul, hν, map_mul, map_mul, WA.algebraMap_conjO]
    ring
  · rw [← idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 (N + 1) (ν * a - 1)]
    have key : ι (ν * a - 1) = ι (a - 1) * (-(c + conjO K c - 1)) +
        ι (a - 1) * ι (a - 1) * (conjO K c * c - (c + conjO K c) + ι (a - 1) * conjO K c * c) := by
      rw [map_sub (algebraMap (𝓞 F) (𝓞 K)) (ν * a) 1, map_mul, hν, ha', map_one, map_sub, map_one,
        map_mul, hEc]
      ring
    rw [key]
    refine Ideal.add_mem _ ?_ ?_
    · rw [pow_succ]
      exact Ideal.mul_mem_mul hEm ((Ideal.neg_mem_iff _).2 hc')
    · refine Ideal.mul_mem_right _ _ ?_
      refine Ideal.pow_le_pow_right (by omega : N + 1 ≤ N + N) ?_
      rw [pow_add]
      exact Ideal.mul_mem_mul hEm hEm
  · have : (1 - ι (a - 1) * c) • y - y = (-(ι (a - 1) * c)) • y := by
      rw [sub_smul, one_smul, neg_smul]; abel
    rw [this]
    exact Submodule.smul_mem_smul ((Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ hEm)) hy

theorem newton_iter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 1 ≤ k) {y : V}
    (hy : y ∈ L) {a : 𝓞 F} (ha : h y y = algebraMap (𝓞 K) K (ι a)) (ha1 : a - 1 ∈ 𝔭 ^ k) (j : ℕ) :
    ∃ y' ∈ L, ∃ a' : 𝓞 F, h y' y' = algebraMap (𝓞 K) K (ι a') ∧ a' - 1 ∈ 𝔭 ^ (k + j) ∧
      y' - y ∈ (extP K 𝔭 ^ k • L : Submodule (𝓞 K) V) := by
  induction j with
  | zero => exact ⟨y, hy, a, ha, by simpa using ha1, by simp⟩
  | succ j ih =>
    obtain ⟨y1, hy1, a1, hh1, h1, hd1⟩ := ih
    obtain ⟨y2, hy2, a2, hh2, h2, hd2⟩ := newton hK hF h𝔭 (by omega : 1 ≤ k + j) hy1 hh1 h1
    refine ⟨y2, hy2, a2, hh2, by simpa only [add_assoc] using h2, ?_⟩
    have : y2 - y = (y2 - y1) + (y1 - y) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) hd2) hd1

theorem exists_exact_lift (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {x₀ : V} (h1 : h x₀ x₀ = 1) {k : ℕ} (hk : 1 ≤ k) {y : V} (hy : y ∈ L)
    (hyy : CongrP 𝔭 k (h y y) 1) :
    ∃ z ∈ locF 𝔭 L, h z z = 1 ∧ z - y ∈ (extP K 𝔭 ^ k • locF 𝔭 L : Submodule (𝓞 K) V) := by
  haveI := h𝔭.isPrime
  obtain ⟨a, ha⟩ := exists_norm_int hF hs hLi hy
  have hI0 : WCA.InI 𝔭 k (algebraMap (𝓞 K) K (ι (a - 1))) := by
    have := Cell.congrP_iff_inI.1 hyy
    rwa [ha, ← map_one (algebraMap (𝓞 K) K), ← map_sub, ← map_one (algebraMap (𝓞 F) (𝓞 K)),
      ← map_sub] at this
  have ha1 : a - 1 ∈ 𝔭 ^ k := (Cell.inI_ι h𝔭).1 hI0
  obtain ⟨v, hv⟩ := Cell.exists_near h𝔭 hF hs hL hLi (n := 1) one_ne_zero
    ⟨x₀, by rw [h1, map_one, map_one]⟩
  obtain ⟨y', hy', a', ha', ha1', hd'⟩ := newton_iter hK hF h𝔭 hk hy ha ha1 v
  have hI : WCA.InI 𝔭 (v + k) (h y' y' - algebraMap (𝓞 K) K (ι 1)) := by
    rw [ha', ← map_sub, ← map_sub]
    exact (Cell.inI_ι h𝔭).2 (by rw [add_comm]; exact ha1')
  obtain ⟨z, hz0, hz1, hzd⟩ :=
    hv k hk y' ((WCA.inL_zero_iff h𝔭.isPrime).2 (localizedQuotients.le_locF 𝔭 L hy')) hI
  refine ⟨z, (WCA.inL_zero_iff h𝔭.isPrime).1 hz0, by rw [hz1, map_one, map_one], ?_⟩
  have : z - y = (z - y') + (y' - y) := by abel
  rw [this]
  exact Submodule.add_mem _ (WCA.InL.mem h𝔭.isPrime hzd)
    (Submodule.smul_mono le_rfl (localizedQuotients.le_locF 𝔭 L) hd')

end Formalism.HermitianLattices.Ext.L3.PinF
end
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinG

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

def red (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    ↥(locF 𝔭 (spanO b)) →ₗ[𝓞 K] (κ → 𝓞 K ⧸ extP K 𝔭 ^ k) :=
  (qE b (extP K 𝔭 ^ k)).toLinearMap ∘ₗ (quotLocF h𝔭 (spanO b) k).symm.toLinearMap ∘ₗ
    Submodule.mkQ _

theorem red_of_mem (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (w : ↥(locF 𝔭 (spanO b))) (hw : (w : V) ∈ spanO b) :
    red b h𝔭 k w = fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (crd b ⟨w, hw⟩ i) := by
  have e : (quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨(w : V), hw⟩ := by
    rw [LinearEquiv.symm_apply_eq, quotLocF_mk h𝔭 (spanO b) k ⟨(w : V), hw⟩ w.2]
  show qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w)) = _
  rw [e, qE_mk]

theorem red_smul_one (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) {c : 𝓞 F}
    (hc : c - 1 ∈ 𝔭 ^ k) (w : ↥(locF 𝔭 (spanO b))) : red b h𝔭 k (ι c • w) = red b h𝔭 k w := by
  rw [map_smul]
  funext i
  rw [Pi.smul_apply, Algebra.smul_def]
  have : algebraMap (𝓞 K) (𝓞 K ⧸ extP K 𝔭 ^ k) (ι c) = 1 := by
    show Ideal.Quotient.mk _ (ι c) = 1
    rw [← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq, ← map_one ι, ← map_sub]
    exact ι_mem_pow hc
  rw [this, one_mul]

theorem red_eq_of_sub_mem (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (w w' : ↥(locF 𝔭 (spanO b)))
    (hww : (w : V) - w' ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V)) :
    red b h𝔭 k w = red b h𝔭 k w' := by
  have e : (Submodule.Quotient.mk w : ↥(locF 𝔭 (spanO b)) ⧸
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 (spanO b)))) = Submodule.Quotient.mk w' := by
    rw [Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
    exact hww
  show qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w)) =
    qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w'))
  rw [e]

def bM (b : Basis κ K V) (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (j : κ) : ↥(locF 𝔭 (spanO b)) :=
  ⟨b j, le_locF 𝔭 _ (Submodule.subset_span (Set.mem_range_self j))⟩

theorem red_bM (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (k : ℕ) (j : κ) :
    red b h𝔭 k (bM b 𝔭 j) = Pi.single j 1 := by
  have e : (quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk (bM b 𝔭 j)) =
      Submodule.Quotient.mk (bO b j) := by
    rw [LinearEquiv.symm_apply_eq, quotLocF_mk h𝔭 (spanO b) k (bO b j)
      (by rw [bO_apply]; exact (bM b 𝔭 j).2)]
    congr 1
    apply Subtype.ext
    exact (bO_apply b j).symm
  show qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk (bM b 𝔭 j))) = _
  rw [e, qE_bO]

variable [Fact (IsFixF K F)]

theorem red_form (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (w w' : ↥(locF 𝔭 (spanO b))) {z : 𝓞 K} (hz : h (w : V) (w' : V) = algebraMap (𝓞 K) K z) :
    star (red b h𝔭 k w) ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ red b h𝔭 k w') =
      Ideal.Quotient.mk (extP K 𝔭 ^ k) z := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨c, hc, hcw⟩ := exists_approx h𝔭 (spanO b) k w.2
  obtain ⟨c', hc', hcw'⟩ := exists_approx h𝔭 (spanO b) k w'.2
  rw [← red_smul_one b h𝔭 k hc w, ← red_smul_one b h𝔭 k hc' w',
    red_of_mem b h𝔭 k (ι c • w) hcw, red_of_mem b h𝔭 k (ι c' • w') hcw', ← mk_form]
  have e1 := form_eq h b hH ⟨_, hcw⟩ ⟨_, hcw'⟩
  have e2 : h (ι c • (w : V)) (ι c' • (w' : V)) = algebraMap (𝓞 K) K (ι (c * c') * z) := by
    rw [form_smul hF, hz, map_mul (algebraMap (𝓞 K) K)]
  have e3 := FaithfulSMul.algebraMap_injective (𝓞 K) K (e1.symm.trans e2)
  have e4 : Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (c * c')) = 1 := by
    rw [← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq, ← map_one ι, ← map_sub]
    apply ι_mem_pow
    have : c * c' - 1 = (c - 1) * c' + (c' - 1) := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ hc) hc'
  calc _ = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (c * c') * z) := congrArg _ e3
    _ = _ := by rw [map_mul, e4, one_mul]

omit [Fact (IsFixF K F)] in
theorem map_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V}
    (hg : g ∈ autSub h M) {x : V} (hx : x ∈ M) : g x ∈ M := by
  have h2 : Formalism.HermitianLatticesTheory.gmap g M = M := hg.2
  rw [← h2]
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

def gM {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V} (hg : g ∈ autSub h M) :
    ↥M →ₗ[𝓞 K] ↥M :=
  ((g : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict fun _ hx => map_mem hg hx

def gMat {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    [𝔭.IsPrime] (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b))) :
    Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.of fun i j => red b h𝔭 k (gM hg (bM b 𝔭 j)) i

omit [Fact (IsFixF K F)] in
theorem red_gM {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    [𝔭.IsPrime] (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b)))
    (w : ↥(locF 𝔭 (spanO b))) : red b h𝔭 k (gM hg w) = gMat b h𝔭 k hg *ᵥ red b h𝔭 k w := by
  have key : (red b h𝔭 k ∘ₗ gM hg) ∘ₗ Submodule.inclusion (le_locF 𝔭 (spanO b)) =
      (((gMat b h𝔭 k hg).mulVecLin.restrictScalars (𝓞 K)) ∘ₗ red b h𝔭 k) ∘ₗ
        Submodule.inclusion (le_locF 𝔭 (spanO b)) := by
    apply (bO b).ext
    intro j
    have e : Submodule.inclusion (le_locF 𝔭 (spanO b)) (bO b j) = bM b 𝔭 j := by
      apply Subtype.ext
      exact bO_apply b j
    simp only [LinearMap.comp_apply, e, LinearMap.restrictScalars_apply, mulVecLin_apply]
    rw [red_bM, mulVec_single_one]
    rfl
  obtain ⟨c, hc, hcw⟩ := exists_approx h𝔭 (spanO b) k w.2
  have h1 := LinearMap.congr_fun key ⟨_, hcw⟩
  have e : Submodule.inclusion (le_locF 𝔭 (spanO b)) ⟨_, hcw⟩ = ι c • w := rfl
  simp only [LinearMap.comp_apply, e, LinearMap.restrictScalars_apply, mulVecLin_apply] at h1
  rw [map_smul, red_smul_one b h𝔭 k hc, red_smul_one b h𝔭 k hc] at h1
  exact h1

theorem exists_matrix (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b))) :
    ∃ G G' : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k),
      Gᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * G = H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) ∧
      G * G' = 1 ∧ ∀ w w' : ↥(locF 𝔭 (spanO b)), (w' : V) = g w →
        red b h𝔭 k w' = G *ᵥ red b h𝔭 k w := by
  have := h𝔭.isPrime
  have hg' : g⁻¹ ∈ autSub h (locF 𝔭 (spanO b)) := inv_mem hg
  refine ⟨gMat b h𝔭 k hg, gMat b h𝔭 k hg', ?_, ?_, ?_⟩
  · ext i j
    rw [← form_single (_ᴴ * _ * _) i j, ← form_mulVec, ← red_bM b h𝔭 k i, ← red_bM b h𝔭 k j,
      ← red_gM, ← red_gM, Matrix.map_apply]
    apply red_form h b hH h𝔭 k
    show h (g (b i)) (g (b j)) = _
    rw [hg.1 (b i) (b j), hH]
  · ext i j
    have h1 : (gMat b h𝔭 k hg * gMat b h𝔭 k hg') *ᵥ Pi.single j 1 = Pi.single j 1 := by
      rw [← mulVec_mulVec, ← red_bM b h𝔭 k j, ← red_gM, ← red_gM]
      congr 1
      apply Subtype.ext
      show g (g⁻¹ (b j)) = b j
      exact g.apply_symm_apply (b j)
    have h2 := congrFun h1 i
    rw [mulVec_single_one] at h2
    rw [Matrix.one_apply, ← Pi.single_apply]
    exact h2
  · intro w w' hww
    rw [← red_gM]
    congr 1
    apply Subtype.ext
    exact hww

end Formalism.HermitianLattices.Ext.L3.PinG
end
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinB

open idealPowerSpanBounds integralBasisSpans

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

omit [NumberField K] [FiniteDimensional K V] [FiniteDimensional K V'] in

def prodEquiv (S : VecSplit h h') : (K × V') ≃ₗ[K] V :=
  LinearEquiv.ofBijective ((LinearMap.toSpanSingleton K V S.x₀).coprod S.ι) (by
    constructor
    · rintro ⟨c, a⟩ ⟨c', a'⟩ e
      simp only [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply] at e
      obtain ⟨rfl, rfl⟩ := S.comb_eq_iff.1 e
      rfl
    · intro v
      obtain ⟨c, a, rfl⟩ := S.cover v
      exact ⟨(c, a), by simp only [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]⟩)

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem prodEquiv_apply (S : VecSplit h h') (c : K) (a : V') :
    prodEquiv S (c, a) = c • S.x₀ + S.ι a := by
  show (LinearMap.toSpanSingleton K V S.x₀).coprod S.ι (c, a) = _
  rw [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]

def consBasis (S : VecSplit h h') {κ : Type} (b' : Basis κ K V') : Basis (Unit ⊕ κ) K V :=
  ((Basis.singleton Unit K).prod b').map (prodEquiv S)

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem consBasis_inl (S : VecSplit h h') {κ : Type} (b' : Basis κ K V') (u : Unit) :
    consBasis S b' (Sum.inl u) = S.x₀ := by
  simp [consBasis, prodEquiv_apply]

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem consBasis_inr (S : VecSplit h h') {κ : Type} (b' : Basis κ K V') (i : κ) :
    consBasis S b' (Sum.inr i) = S.ι (b' i) := by
  simp [consBasis, prodEquiv_apply]

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem locF_span_consBasis (S : VecSplit h h') {κ : Type} (b' : Basis κ K V')
    {T : Submodule (𝓞 K) V'} (hbT : ∀ i, b' i ∈ T) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hb' : locF 𝔭 (spanO b') = locF 𝔭 T) :
    locF 𝔭 (spanO (consBasis S b')) = locF 𝔭 (S.adjoin T) := by
  have key : ∀ {A B : Submodule (𝓞 K) V}, A ≤ locF 𝔭 B → B ≤ locF 𝔭 A →
      locF 𝔭 A = locF 𝔭 B := by
    intro A B hAB hBA
    apply le_antisymm
    · exact (Formalism.HermitianLatticesTheory.genusCovol_locS_mono _ hAB).trans (Formalism.HermitianLatticesTheory.genusCovol_locS_idem _ _)
    · exact (Formalism.HermitianLatticesTheory.genusCovol_locS_mono _ hBA).trans (Formalism.HermitianLatticesTheory.genusCovol_locS_idem _ _)
  unfold VecSplit.adjoin
  apply key
  · refine le_trans ?_ (Formalism.HermitianLatticesTheory.genusCovol_le_locS _ _)
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with u | i
    · rw [consBasis_inl]
      exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
    · rw [consBasis_inr]
      exact Submodule.mem_sup_right ⟨b' i, hbT i, rfl⟩
  · apply sup_le
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      apply Formalism.HermitianLatticesTheory.genusCovol_le_locS
      rw [← consBasis_inl S b' ()]
      exact Submodule.subset_span ⟨Sum.inl (), rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      have ht' : t ∈ locF 𝔭 (spanO b') := by
        rw [hb']
        exact Formalism.HermitianLatticesTheory.genusCovol_le_locS _ _ ht
      obtain ⟨s, hs, hst⟩ := (Formalism.HermitianLatticesTheory.genusCovol_mem_locS _ _ _).1 ht'
      have hmap : ∀ y ∈ spanO b', S.ι y ∈ spanO (consBasis S b') := by
        intro y hy
        refine Submodule.span_induction (p := fun y _ => S.ι y ∈ spanO (consBasis S b'))
          ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨i, rfl⟩
          rw [← consBasis_inr S b' i]
          exact Submodule.subset_span ⟨Sum.inr i, rfl⟩
        · simp
        · intro x y _ _ hx hy
          rw [map_add]
          exact Submodule.add_mem _ hx hy
        · intro a x _ hx
          have e : S.ι (a • x) = a • S.ι x := (S.ι.restrictScalars (𝓞 K)).map_smul a x
          rw [e]
          exact Submodule.smul_mem _ a hx
      refine (Formalism.HermitianLatticesTheory.genusCovol_mem_locS _ _ _).2 ⟨s, hs, ?_⟩
      have e : S.ι (s • t) = s • S.ι t := (S.ι.restrictScalars (𝓞 K)).map_smul s t
      have := hmap _ hst
      rw [e] at this
      exact this

theorem akCount_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    akCount h L 𝔭 k = nkCount h L 𝔭 k 1 * akCount h' (S.cut L) 𝔭 k := by
  classical
  haveI : 𝔭.IsPrime := h𝔭.isPrime
  haveI : Fact (IsFixF K F) := ⟨hF⟩

  obtain ⟨π, hπ⟩ : ∃ π : V →ₗ[K] V', ∀ v, π v = ((prodEquiv S).symm v).2 :=
    ⟨(LinearMap.snd K K V') ∘ₗ (prodEquiv S).symm.toLinearMap, fun v => rfl⟩
  have hdec : ∀ v : V, v = h S.x₀ v • S.x₀ + S.ι (π v) := by
    intro v
    obtain ⟨c, a, hv⟩ : ∃ c a, (prodEquiv S).symm v = (c, a) := ⟨_, _, rfl⟩
    have hv' : v = c • S.x₀ + S.ι a := by
      rw [← prodEquiv_apply, ← hv, LinearEquiv.apply_symm_apply]
    have hc : h S.x₀ v = c := by
      rw [hv', map_add, map_smul, h1, S.orth]
      simp
    have ha : π v = a := by rw [hπ, hv]
    rw [hc, ha]
    exact hv'
  have hπι : ∀ a, π (S.ι a) = a := by
    intro a
    have e := hdec (S.ι a)
    rw [S.orth, zero_smul, zero_add] at e
    exact (S.inj e).symm
  have hcutEq : S.cut L = L.map (π.restrictScalars (𝓞 K)) := by
    ext a
    constructor
    · intro ha
      exact ⟨S.ι a, ha, hπι a⟩
    · rintro ⟨v, hv, rfl⟩
      show S.ι (π v) ∈ L
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hLi _ hx _ hv)
      have e : S.ι (π v) = v - h S.x₀ v • S.x₀ := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact (hdec v).symm
      rw [e, ← hc, algebraMap_smul]
      exact L.sub_mem hv (L.smul_mem c hx)
  have hcutL : Submodule.IsLattice K (S.cut L) := by
    rw [hcutEq]
    refine ⟨hL.fg.map _, ?_⟩
    rw [Submodule.map_coe]
    change Submodule.span K (π '' (L : Set V)) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact fun a => ⟨S.ι a, hπι a⟩

  obtain ⟨b', hb'L, hb'⟩ := Formalism.HermitianLattices.Ext.L3.LocalSpans.exists_basis_locF hcutL h𝔭
  have hm : ∀ i, S.ι (b' i) ∈ L := hb'L
  have hH'ex : ∀ i j, ∃ z : 𝓞 K, algebraMap (𝓞 K) K z = h' (b' i) (b' j) := by
    intro i j
    have e := hLi _ (hm i) _ (hm j)
    rw [S.isom] at e
    exact Submodule.mem_one.1 e
  obtain ⟨H', hH'⟩ : ∃ H' : Matrix (Fin (finrank K V')) (Fin (finrank K V')) (𝓞 K),
      ∀ i j, algebraMap (𝓞 K) K (H' i j) = h' (b' i) (b' j) :=
    ⟨Matrix.of fun i j => (hH'ex i j).choose, fun i j => (hH'ex i j).choose_spec⟩
  set bb := consBasis S b' with hbbdef
  have hbb : locF 𝔭 (spanO bb) = locF 𝔭 L :=
    (locF_span_consBasis S b' hb'L h𝔭 hb').trans
      (Formalism.HermitianLattices.Ext.L3.PinC.locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭
        (Formalism.HermitianLattices.Ext.L3.LocF.le_locF 𝔭 L hx)).symm
  have hbbL : ∀ p, bb p ∈ L := by
    rintro (u | i)
    · rw [hbbdef, consBasis_inl]; exact hx
    · rw [hbbdef, consBasis_inr]; exact hm i
  have hHH : ∀ p q, algebraMap (𝓞 K) K (Formalism.HermitianLattices.Ext.L3.PinE.HH H' p q) = h (bb p) (bb q) := by
    rintro (u | i) (u' | j)
    · rw [hbbdef]
      simp only [consBasis_inl]
      rw [h1]
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH]
    · rw [hbbdef]
      simp only [consBasis_inl, consBasis_inr]
      rw [S.orth]
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH]
    · rw [hbbdef]
      simp only [consBasis_inl, consBasis_inr]
      have e : starRingEnd K (h S.x₀ (S.ι (b' i))) = h (S.ι (b' i)) S.x₀ := by
        first
          | exact hs S.x₀ (S.ι (b' i))
          | exact hs.eq S.x₀ (S.ι (b' i))
      rw [← e, S.orth]
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH]
    · rw [hbbdef]
      simp only [consBasis_inr]
      rw [S.isom]
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH, hH']
  have hmapHH : (Formalism.HermitianLattices.Ext.L3.PinE.HH H').map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) =
      Formalism.HermitianLattices.Ext.L3.PinE.HH (H'.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) := by
    ext p q
    rcases p with u | i <;> rcases q with u' | j <;>
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH, Matrix.one_apply]

  have htr : ∀ x : Unit ⊕ Fin (finrank K V') → 𝓞 K ⧸ extP K 𝔭 ^ k,
      star x ⬝ᵥ (Formalism.HermitianLattices.Ext.L3.PinE.HH (H'.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) *ᵥ x) = 1 →
      ∃ G G' : Matrix (Unit ⊕ Fin (finrank K V')) (Unit ⊕ Fin (finrank K V')) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Gᴴ * Formalism.HermitianLattices.Ext.L3.PinE.HH (H'.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) * G =
          Formalism.HermitianLattices.Ext.L3.PinE.HH (H'.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) ∧
        G * G' = 1 ∧ G *ᵥ Formalism.HermitianLattices.Ext.L3.PinE.e₀ = x := by
    intro x hx1
    obtain ⟨c, hc⟩ : ∃ c : Unit ⊕ Fin (finrank K V') → 𝓞 K,
        ∀ p, Ideal.Quotient.mk (extP K 𝔭 ^ k) (c p) = x p :=
      ⟨fun p => (Ideal.Quotient.mk_surjective (x p)).choose,
        fun p => (Ideal.Quotient.mk_surjective (x p)).choose_spec⟩
    set w : ↥(locF 𝔭 (spanO bb)) := ∑ p, c p • Formalism.HermitianLattices.Ext.L3.PinG.bM bb 𝔭 p with hwdef
    have hred : Formalism.HermitianLattices.Ext.L3.PinG.red bb h𝔭 k w = x := by
      funext q
      simp [hwdef, map_sum, map_smul, Formalism.HermitianLattices.Ext.L3.PinG.red_bM, Pi.single_apply, hc,
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
      rcases q with ⟨⟩ | i <;> simp
    have hwL : (w : V) ∈ L := by
      rw [hwdef, Submodule.coe_sum]
      exact Submodule.sum_mem _ (fun p _ => by
        rw [Submodule.coe_smul]
        exact Submodule.smul_mem _ _ (hbbL p))
    obtain ⟨z, hz⟩ := Submodule.mem_one.1 (hLi _ hwL _ hwL)
    have hform := Formalism.HermitianLattices.Ext.L3.PinG.red_form h bb hHH h𝔭 k w w hz.symm
    rw [hred, hmapHH, hx1] at hform
    have hcong : CongrP 𝔭 k (h (w : V) (w : V)) 1 := by
      have e := (Formalism.HermitianLattices.Ext.L3.integralBasisSpans.congrP_int h𝔭 k z 1).2 (by rw [map_one]; exact hform.symm)
      rwa [map_one, hz] at e
    obtain ⟨z', hz'L, hz'1, hz'd⟩ :=
      Formalism.HermitianLattices.Ext.L3.PinF.exists_exact_lift hK hF hs hd hL hLi h𝔭 h1 hk hwL hcong
    obtain ⟨g, hg, hgx⟩ :=
      Formalism.HermitianLattices.Ext.L3.PinC.exists_aut_map hK hF hs hd S h1 hL hLi hx h𝔭 hv hz'L hz'1
    rw [← hbb] at hg
    obtain ⟨G, G', hGf, hGG, hGred⟩ := Formalism.HermitianLattices.Ext.L3.PinG.exists_matrix h bb hHH h𝔭 k hg
    refine ⟨G, G', by rw [← hmapHH]; exact hGf, hGG, ?_⟩
    have hz'm : z' ∈ locF 𝔭 (spanO bb) := by rw [hbb]; exact hz'L
    have e1 := hGred (Formalism.HermitianLattices.Ext.L3.PinG.bM bb 𝔭 (Sum.inl ())) ⟨z', hz'm⟩ (by
      show z' = g (bb (Sum.inl ()))
      rw [hbbdef, consBasis_inl, hgx])
    rw [Formalism.HermitianLattices.Ext.L3.PinG.red_bM] at e1
    have e2 : Formalism.HermitianLattices.Ext.L3.PinG.red bb h𝔭 k ⟨z', hz'm⟩ = Formalism.HermitianLattices.Ext.L3.PinG.red bb h𝔭 k w :=
      Formalism.HermitianLattices.Ext.L3.PinG.red_eq_of_sub_mem bb h𝔭 k _ _ (by
        have e := hz'd
        rw [← hbb] at e
        exact e)
    rw [← hred, ← e2, e1]
    rfl
  haveI : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.finite_quot (K := K) h𝔭 k
  rw [Formalism.HermitianLattices.Ext.L3.integralBasisSpans.akCount_eq h h𝔭 bb hbb hHH k, hmapHH,
    Formalism.HermitianLattices.Ext.L3.PinE.card_split _ htr,
    Formalism.HermitianLattices.Ext.L3.integralBasisSpans.nkCount_eq h h𝔭 bb hbb hHH k 1, hmapHH,
    Formalism.HermitianLattices.Ext.L3.integralBasisSpans.akCount_eq h' h𝔭 b' hb' hH' k]
  simp

end Formalism.HermitianLattices.Ext.L3.PinB
end
end

section
open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinD

section One

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [NumberField F] in
theorem star_cK (hF : IsFixF K F) (c : F) : star (algebraMap F K c) = algebraMap F K c :=
  (hF _).2 ⟨c, rfl⟩

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K] in
theorem smul_form_apply (c : K) (h : V →ₗ⋆[K] V →ₗ[K] K) (x y : V) : (c • h) x y = c * h x y := by
  rfl

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K]
  [NumberField F] in
theorem isSymm_of_smul (hF : IsFixF K F) {c : F} (hc : algebraMap F K c ≠ 0)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : (algebraMap F K c • h).IsSymm) : h.IsSymm := by
  refine ⟨fun x y => ?_⟩
  have hxy := hs.eq x y
  rw [smul_form_apply, smul_form_apply, map_mul] at hxy
  have hst : (starRingEnd K) (algebraMap F K c) = algebraMap F K c := star_cK hF c
  rw [hst] at hxy
  exact mul_left_cancel₀ hc hxy

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField F] in
theorem isTotPosDef_of_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {c : F}
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef (algebraMap F K c • h)) {x₀ : V}
    (h1 : h x₀ x₀ = 1) : IsTotPosDef h := by
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    simp at h1
  intro x hx φ
  have hreal : ∀ a : K, star a = a → (φ a).im = 0 := by
    intro a ha
    have := hK.2.1 φ a
    rw [ha] at this
    exact Complex.conj_eq_iff_im.1 this.symm
  have hc0 := hd x₀ hx0 φ
  rw [smul_form_apply, h1, mul_one] at hc0
  have hcx := hd x hx φ
  rw [smul_form_apply, map_mul] at hcx
  have hcr : (φ (algebraMap F K c)).im = 0 := hreal _ (star_cK hF c)
  rw [Complex.mul_re, hcr, zero_mul, sub_zero] at hcx
  exact pos_of_mul_pos_right hcx hc0.le


theorem alphaL_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (hs' : (algebraMap F K (c : F) • h).IsSymm)
    (hd' : IsTotPosDef (algebraMap F K (c : F) • h)) :
    alphaL (algebraMap F K (c : F) • h) L 𝔭 =
      (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 c * finrank K V ^ 2) * alphaL h L 𝔭 := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have key : ∀ k, 2 * vd h L 𝔭 + 1 + vF 𝔭 c ≤ k →
      (akCount (algebraMap F K (c : F) • h) L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) =
        (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 c * finrank K V ^ 2) * alphaL h L 𝔭 := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c := ⟨k - vF 𝔭 c, by omega⟩
    rw [PinA.akCount_smul hK hF hs hd hL hLi h𝔭 hc (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel,
      firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := m) (by omega)]
    push_cast
    rw [show (m + vF 𝔭 c) * finrank K V ^ 2 = m * finrank K V ^ 2 + vF 𝔭 c * finrank K V ^ 2 by ring,
      show 2 * vF 𝔭 c * finrank K V ^ 2 = vF 𝔭 c * finrank K V ^ 2 + vF 𝔭 c * finrank K V ^ 2 by ring,
      pow_add, pow_add]
    field_simp <;> ring
  exact (tendsto_const_nhds.congr'
    (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq

theorem alphaN_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (hs' : (algebraMap F K (c : F) • h).IsSymm)
    (hd' : IsTotPosDef (algebraMap F K (c : F) • h)) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ≠ 0) :
    alphaN (algebraMap F K (c : F) • h) L 𝔭 (c * n) =
      (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have key : ∀ k, 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 + vF 𝔭 c ≤ k →
      (nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) : ℝ) /
          (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) =
        (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c := ⟨k - vF 𝔭 c, by omega⟩
    rw [PinA.nkCount_smul hK hF hs hd hL hLi h𝔭 hc n (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel,
      alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn (k := m) (by omega)]
    push_cast
    have h2 : 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V - 1) + vF 𝔭 c := by
      have h3 : 2 * finrank K V = (2 * finrank K V - 1) + 1 := by omega
      calc 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V) := by ring
        _ = vF 𝔭 c * ((2 * finrank K V - 1) + 1) := by rw [← h3]
        _ = _ := by ring
    rw [h2, show (m + vF 𝔭 c) * (2 * finrank K V - 1) =
        m * (2 * finrank K V - 1) + vF 𝔭 c * (2 * finrank K V - 1) by ring, pow_add, pow_add]
    field_simp <;> ring
  exact (tendsto_const_nhds.congr'
    (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq

end One

section Two

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isom_smul {c : K} (hc : c ≠ 0) (h : V →ₗ⋆[K] V →ₗ[K] K) :
    Formalism.HermitianLatticesTheory.isom (c • h) = Formalism.HermitianLatticesTheory.isom h := by
  ext g
  show (∀ x y, (c • h) (g x) (g y) = (c • h) x y) ↔ ∀ x y, h (g x) (g y) = h x y
  simp only [smul_form_apply, mul_right_inj' hc]

def unscale {c : K} (hc : c ≠ 0) (S : VecSplit (c • h) (c • h')) : VecSplit h h' where
  x₀ := S.x₀
  ι := S.ι
  inj := S.inj
  hx₀ := fun e => S.hx₀ (by rw [smul_form_apply, e, mul_zero])
  isom := fun a b => by
    have := S.isom a b
    rw [smul_form_apply, smul_form_apply] at this
    exact mul_left_cancel₀ hc this
  orth := fun a => by
    have := S.orth a
    rw [smul_form_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  cover := S.cover

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem fibLoc_unscale {c : K} (hc : c ≠ 0) (S : VecSplit (c • h) (c • h')) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (T : Submodule (𝓞 K) V') :
    fibLoc S L 𝔭 T = fibLoc (unscale hc S) L 𝔭 T := by
  simp only [fibLoc, isom_smul hc]
  rfl

theorem isLocReps_scale (hF : IsFixF K F) {c : 𝓞 F} (hc : algebraMap F K (c : F) ≠ 0)
    (S : VecSplit (algebraMap F K (c : F) • h) (algebraMap F K (c : F) • h'))
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {s : Finset (Submodule (𝓞 K) V')}
    (hr : IsLocReps (unscale hc S) L 𝔭 s) : IsLocReps S L 𝔭 s := by
  have hLi' := PinA.isIntegralLat_smul hLi c
  have hiso : Formalism.HermitianLatticesTheory.isom (algebraMap F K (c : F) • h') = Formalism.HermitianLatticesTheory.isom h' := isom_smul hc h'
  refine ⟨fun T hT => ?_, fun T hTl hTi hTf => ?_⟩
  · obtain ⟨h1, -, h3⟩ := hr.1 T hT
    rw [← fibLoc_unscale] at h3
    obtain ⟨C, -, hCi, hC⟩ := UnimodularLocalization.exists_lattice_of_fibLoc_ne_zero S hL hLi' h3
    refine ⟨h1, ?_, h3⟩
    have := GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hCi
    rwa [hC, h1] at this
  · rw [fibLoc_unscale hc] at hTf
    obtain ⟨C, -, hCi, hC⟩ := UnimodularLocalization.exists_lattice_of_fibLoc_ne_zero (unscale hc S) hL hLi hTf
    have hTi' : IsIntegralAt 𝔭 h' T := by
      have := GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hCi
      rwa [hC, hTl] at this
    rw [hiso]
    exact hr.2 T hTl hTi' hTf

theorem alphaL_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) :
    alphaL h L 𝔭 = alphaN h L 𝔭 1 * alphaL h' (S.cut L) 𝔭 := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hdim := S.finrank_add_one
  have hA := alphaL_pos hK hF hs hd hL hLi h𝔭
  have h1𝔭 : (1 : 𝓞 F) ∉ 𝔭 ^ (0 + 1) := by
    rw [zero_add, pow_one]; exact (Ideal.ne_top_iff_one 𝔭).1 h𝔭.ne_top
  have key : ∀ k, 2 * vd h L 𝔭 + 2 ≤ k → alphaN h L 𝔭 1 ≠ 0 ∧
      (akCount h' (S.cut L) 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V' ^ 2) =
        alphaL h L 𝔭 / alphaN h L 𝔭 1 := by
    intro k hk
    have eA := firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := k) (by omega)
    have eB := firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 h1𝔭 (k := k) (by omega)
    have eS := PinB.akCount_split hK hF hs hd S h1 hL hLi hx h𝔭 hv (k := k) (by omega)
    rw [eS, Nat.cast_mul] at eA
    have hnk : (nkCount h L 𝔭 k 1 : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul, zero_div] at eA
      linarith
    have hB : alphaN h L 𝔭 1 ≠ 0 := by
      rw [eB]; exact div_ne_zero hnk (pow_ne_zero _ hN)
    refine ⟨hB, ?_⟩
    rw [eA, eB, ← hdim]
    have e1 : k * (finrank K V' + 1) ^ 2 =
        k * (2 * (finrank K V' + 1) - 1) + k * finrank K V' ^ 2 := by
      have : 2 * (finrank K V' + 1) - 1 = 2 * finrank K V' + 1 := by omega
      rw [this]; ring
    rw [e1, pow_add]
    field_simp <;> ring
  obtain ⟨hB, -⟩ := key _ le_rfl
  have hl : alphaL h' (S.cut L) 𝔭 = alphaL h L 𝔭 / alphaN h L 𝔭 1 :=
    (tendsto_const_nhds.congr'
      (Filter.eventually_atTop.2 ⟨_, fun k hk => ((key k hk).2).symm⟩)).limUnder_eq
  rw [hl]
  field_simp

end Two

end Formalism.HermitianLattices.Ext.L3.PinD
end
end
