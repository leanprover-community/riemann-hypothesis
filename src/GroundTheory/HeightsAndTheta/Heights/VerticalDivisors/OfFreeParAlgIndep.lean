import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfChartPointSecPointSpecChart
import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChartPointTrdeg
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecPointSeparable
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenericFormsKer
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsDerivSpanTrdeg
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFreeParAlgIndep
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChart
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChartQuot
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecMax
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartDomain

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem ChartPointTrdeg.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : AffineChartTrdeg.Statement) :
    ChartPointTrdeg.Statement := by
  intro k L _ _ _ n e Q g hQ hg x j₀ hx hj
  have := hQ.isPrime
  have hdim := h₁ k n (e + 1) Q g hQ hg
  have hXj : (X j₀ : MvPolynomial (Fin n) k) ∉ Q := fun h => hj (by simpa using hx _ h)
  have htr := h₂ k n e Q j₀ hQ hdim hXj
  let R := MvPolynomial (Fin n) k ⧸ Q
  let K := FractionRing R
  let π : R →ₐ[k] L := Ideal.Quotient.liftₐ Q (aeval x) hx
  let s : R := Ideal.Quotient.mk Q (X j₀)
  have hs : s ≠ 0 := by
    intro h
    exact hXj (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hπX : ∀ m, π (Ideal.Quotient.mk Q (X m)) = x m := fun m =>
    (AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp Q (aeval x) hx) (X m)).trans (aeval_X x m)
  have hπs : π s = x j₀ := hπX j₀
  have hπu : IsUnit (π s) := by rw [hπs]; exact hj.isUnit
  have hKs : algebraMap R K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs
  let S := Localization.Away s
  let ρ : S →ₐ[k] L := IsLocalization.Away.liftAlgHom s hπu
  let ι : S →ₐ[k] K :=
    IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom k R K) s hKs.isUnit
  have hSinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  have hι : Function.Injective ι := by
    show Function.Injective (IsLocalization.Away.lift (g := algebraMap R K) s hKs.isUnit)
    refine (IsLocalization.lift_injective_iff _).mpr fun a b => ?_
    rw [hSinj.eq_iff, (IsFractionRing.injective R K).eq_iff]
  let y : Fin n → S := fun m => algebraMap R S (Ideal.Quotient.mk Q (X m)) * IsLocalization.Away.invSelf s
  have hinv : ∀ {B : Type} [Field B] [Algebra k B] (φ : S →ₐ[k] B),
      φ (IsLocalization.Away.invSelf s) = (φ (algebraMap R S s))⁻¹ := by
    intro B _ _ φ
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have hιR : ∀ a, ι (algebraMap R S a) = algebraMap R K a := fun a =>
    IsLocalization.Away.lift_eq (g := algebraMap R K) s hKs.isUnit a
  have hρR : ∀ a, ρ (algebraMap R S a) = π a := fun a =>
    IsLocalization.Away.lift_eq (g := (π : R →+* L)) s hπu a
  have hιy : ι ∘ y = fun m => genPt Q m * (genPt Q j₀)⁻¹ := by
    funext m
    simp only [Function.comp_apply, y, map_mul, hinv ι, hιR]
    rfl
  have hρy : ρ ∘ y = fun m => x m * (x j₀)⁻¹ := by
    funext m
    simp only [Function.comp_apply, y, map_mul, hinv ρ, hρR, hπX, s]
  let T := Algebra.adjoin k (Set.range y)
  have hA : T.map ι = Algebra.adjoin k (Set.range fun m => genPt Q m * (genPt Q j₀)⁻¹) := by
    rw [← Algebra.adjoin_image, ← Set.range_comp, hιy]
  have hB : T.map ρ = Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹) := by
    rw [← Algebra.adjoin_image, ← Set.range_comp, hρy]
  have hTA : Algebra.trdeg k T = Algebra.trdeg k (T.map ι) :=
    (Subalgebra.equivMapOfInjective T ι hι).trdeg_eq
  have hBT : Algebra.trdeg k (T.map ρ) ≤ Algebra.trdeg k T := by
    refine trdeg_le_of_surjective ((ρ.comp T.val).codRestrict (T.map ρ)
      (fun t => ⟨t, t.2, rfl⟩)) ?_
    rintro ⟨b, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  rw [← hB]
  rw [hA, htr] at hTA
  exact hBT.trans hTA.le

end

end GroundTheory.Heights₂.Heights.Vertical
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace SecPointSeparable

theorem isSeparable_of_derivation_eq_zero {K L : Type} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] (h : ∀ D : Derivation K L L, D = 0) : Algebra.IsSeparable K L := by
  rw [← Algebra.FormallyUnramified.iff_isSeparable]
  refine ⟨⟨fun a b => ?_⟩⟩
  have key : ∀ ω : Ω[L⁄K], ω = 0 := by
    intro ω
    refine (Module.forall_dual_apply_eq_zero_iff L ω).1 fun φ => ?_
    have : φ = 0 := by
      apply (KaehlerDifferential.linearMapEquivDerivation K L).injective
      rw [map_zero]
      exact h _
    rw [this, LinearMap.zero_apply]
  rw [key a, key b]

end SecPointSeparable

open SecPointSeparable in
theorem SecPointSeparable.proof (h₁ : GenericFormsKer.Statement) (h₂ : DerivSpanTrdeg.Statement)
    (h₃ : FreeParAlgIndep.Statement) : SecPointSeparable.Statement := by
  intro k _ _ n e L _ _ _ _ _ x hx hU hT htr
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, x j₀ ≠ 0 := by
    by_contra! h
    simp [h] at hT
  set z : Fin n → L := fun m => x m * (x j₀)⁻¹ with hz
  obtain ⟨r, hre, b, hb⟩ := h₂ k L (Fin n) z e (htr j₀ hj₀)
  have hind := h₃ k n e L x hx hU hT j₀ hj₀ (htr j₀ hj₀)
  apply isSeparable_of_derivation_eq_zero
  intro D
  obtain ⟨c, hc⟩ := hb (D.restrictScalars k)
  have hc' : ∀ j, D (z j) = ∑ m, c m * (b m j : L) := hc
  have hDK : ∀ a : GenParField k e n, D (algebraMap (GenParField k e n) L a) = 0 :=
    fun a => D.map_algebraMap a
  have hlin : ∀ (a : GenParField k e n) (y : L),
      D (algebraMap (GenParField k e n) L a * y) = algebraMap (GenParField k e n) L a * D y := by
    intro a y
    rw [D.leibniz, hDK, smul_zero, add_zero, smul_eq_mul]
  have hDz₀ : D (z j₀) = 0 := by
    simp only [z, mul_inv_cancel₀ hj₀, Derivation.map_one_eq_zero]
  have hUDz : ∀ i : Fin e,
      ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * D (z j) = 0 := by
    intro i
    have h0 : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j = 0 := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hU i, zero_mul]
    have := congrArg D h0
    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => (hlin _ _).symm
  have hDz : ∀ j, D (z j) = 0 := by
    have key := h₁ (IntermediateField.adjoin k (Set.range z)) L {j : Fin n // j ≠ j₀} e r hre
      (fun p => algebraMap (GenParField k e n) L (genPar k e n (.inl (p.1, p.2.1)))) hind
      (fun m j => b m j.1) c (fun i => ?_)
    · intro j
      by_cases hj : j = j₀
      · rw [hj, hDz₀]
      · rw [hc' j]
        exact key ⟨j, hj⟩
    · have := hUDz i
      rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, hDz₀, mul_zero, zero_add] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc' j.1]
      rfl
  have hx₀ : D (x j₀) = 0 := by
    have hs : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j = (x j₀)⁻¹ := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hT, one_mul]
    have h1 := congrArg D hs
    rw [map_sum, Finset.sum_eq_zero fun j _ => by rw [hlin, hDz, mul_zero], Derivation.leibniz_inv,
      eq_comm, smul_eq_mul, neg_mul, neg_eq_zero, mul_eq_zero] at h1
    exact h1.resolve_left (pow_ne_zero _ (inv_ne_zero hj₀))
  have hxj : ∀ j, D (x j) = 0 := by
    intro j
    have hxz : x j = z j * x j₀ := by simp only [z, mul_assoc, inv_mul_cancel₀ hj₀, mul_one]
    rw [hxz, D.leibniz, hx₀, hDz, smul_zero, smul_zero, add_zero]
  exact Derivation.ext_of_adjoin_eq_top (Set.range x) hx (by rintro _ ⟨j, rfl⟩; simpa using hxj j)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

set_option linter.unusedSectionVars false

namespace SpecChart

theorem solve_inl {L : Type*} [CommRing L] {u x ci S : L} (h : u * x + S = 0) (hc : ci * x = 1) :
    -(ci * S) = u := by
  linear_combination (-ci) * h + u * hc

theorem solve_inr {L : Type*} [CommRing L] {u x ci S : L} (h : u * x + S = 1) (hc : ci * x = 1) :
    ci * (1 - S) = u := by
  linear_combination (-ci) * h + u * hc

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)

abbrev FreePar : Type := (Fin e × {m : Fin n // m ≠ j}) ⊕ {m : Fin n // m ≠ j}

def FreePar.val : FreePar e j → Par e n
  | .inl (i, m) => .inl (i, m.1)
  | .inr m => .inr m.1

abbrev Base : Type := ChartDomain.Base (integralModel I) j

abbrev Poly : Type := MvPolynomial (FreePar e j) (Base I j)

def toBase : MvPolynomial (Fin n) (𝓞 K) →+* Base I j :=
  (algebraMap _ (Base I j)).comp (Ideal.Quotient.mk (integralModel I))

def cx (l : Fin n) : Poly e I j := C (toBase I j (X l))

def cinv : Poly e I j := C (IsLocalization.Away.invSelf (Ideal.Quotient.mk (integralModel I) (X j)))

theorem cinv_mul_cx : cinv e I j * cx e I j j = 1 := by
  rw [cinv, cx, ← map_mul, toBase, RingHom.comp_apply, mul_comm, IsLocalization.Away.mul_invSelf, map_one]

def val : Par e n → Poly e I j
  | .inl (i, l) => if h : l = j then -(cinv e I j * ∑ m : {m : Fin n // m ≠ j}, X (.inl (i, m)) * cx e I j m)
      else X (.inl (i, ⟨l, h⟩))
  | .inr l => if h : l = j then cinv e I j * (1 - ∑ m : {m : Fin n // m ≠ j}, X (.inr m) * cx e I j m)
      else X (.inr ⟨l, h⟩)

theorem val_free (y : FreePar e j) : val e I j (FreePar.val e j y) = X y := by
  rcases y with ⟨i, m⟩ | m <;> simp [FreePar.val, val, m.2]

def σ : MvPolynomial (Par e n) (𝓞 K) →+* Poly e I j :=
  eval₂Hom (C.comp ((toBase I j).comp C)) (val e I j)

theorem σ_X (p : Par e n) : σ e I j (X p) = val e I j p := eval₂Hom_X' _ _ _

theorem σ_C (c : 𝓞 K) : σ e I j (C c) = C (toBase I j (C c)) := by simp [σ]

theorem sum_val_inl (i : Fin e) : ∑ m, val e I j (.inl (i, m)) * cx e I j m = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  have h : ∀ m : {m : Fin n // m ≠ j}, val e I j (.inl (i, m.1)) = X (.inl (i, m)) := fun m => by
    simp [val, m.2]
  simp only [h]
  simp only [val, dite_true]
  linear_combination (-(∑ m : {m : Fin n // m ≠ j}, X (.inl (i, m)) * cx e I j m)) * cinv_mul_cx e I j

theorem sum_val_inr : ∑ m, val e I j (.inr m) * cx e I j m - 1 = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  have h : ∀ m : {m : Fin n // m ≠ j}, val e I j (.inr m.1) = X (.inr m) := fun m => by
    simp [val, m.2]
  simp only [h]
  simp only [val, dite_true]
  linear_combination (1 - ∑ m : {m : Fin n // m ≠ j}, X (.inr m) * cx e I j m) * cinv_mul_cx e I j

variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))

def Wb : Ideal (Base I j) :=
  (W.map (Ideal.Quotient.mk (integralModel I))).map (algebraMap _ (Base I j))

def Q : Ideal (Poly e I j) :=
  RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk (Wb I j W)) :
    Poly e I j →+* MvPolynomial (FreePar e j) (Base I j ⧸ Wb I j W))

theorem Q_eq : Q e I j W = (Wb I j W).map C := by
  rw [Q, MvPolynomial.ker_map, Ideal.mk_ker]

variable {I W}

theorem mem_of_mk_mem [W.IsPrime] (hPW : integralModel I ≤ W) {g : MvPolynomial (Fin n) (𝓞 K)}
    (h : Ideal.Quotient.mk (integralModel I) g ∈ W.map (Ideal.Quotient.mk _)) : g ∈ W := by
  have h2 : g ∈ Ideal.comap (Ideal.Quotient.mk (integralModel I)) (W.map (Ideal.Quotient.mk _)) := h
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr hPW] at h2
  exact h2

theorem map_mk_isPrime [W.IsPrime] (hPW : integralModel I ≤ W) :
    (W.map (Ideal.Quotient.mk (integralModel I))).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

theorem disjoint_powers [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W) :
    Disjoint (↑(Submonoid.powers (Ideal.Quotient.mk (integralModel I) (X j))) :
        Set (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I))
      ↑(W.map (Ideal.Quotient.mk (integralModel I))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨k, rfl⟩ hk
  simp only [SetLike.mem_coe] at hk
  rw [← map_pow] at hk
  exact hXj (Ideal.IsPrime.mem_of_pow_mem ‹_› k (mem_of_mk_mem hPW hk))

theorem Wb_isPrime [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W) : (Wb I j W).IsPrime :=
  have := map_mk_isPrime hPW
  IsLocalization.isPrime_of_isPrime_disjoint _ _ _ this (disjoint_powers j hPW hXj)

theorem mem_of_toBase_mem [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    {g : MvPolynomial (Fin n) (𝓞 K)} (h : toBase I j g ∈ Wb I j W) : g ∈ W := by
  have := map_mk_isPrime hPW
  have h2 := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers _) (Base I j) this
    (disjoint_powers j hPW hXj)
  apply mem_of_mk_mem hPW
  rw [← h2]
  exact h

theorem Q_isPrime [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W) : (Q e I j W).IsPrime := by
  have := Wb_isPrime j hPW hXj
  exact RingHom.ker_isPrime _

theorem C_toBase_mem_Q {g : MvPolynomial (Fin n) (𝓞 K)} (hg : g ∈ W) : C (toBase I j g) ∈ Q e I j W := by
  rw [Q_eq]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hg))

theorem mem_of_C_toBase_mem_Q [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    {g : MvPolynomial (Fin n) (𝓞 K)} (h : C (toBase I j g) ∈ Q e I j W) : g ∈ W := by
  rw [Q, RingHom.mem_ker, map_C, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h
  exact mem_of_toBase_mem j hPW hXj h

variable {v : HeightOneSpectrum (𝓞 K)}

theorem toSecB_le : integralModel I ≤ RingHom.ker (toSecB e I v) := fun g hg => by
  rw [RingHom.mem_ker, toSecB, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))

theorem secB_secForm (i : Fin e) :
    ∑ m, algebraMap (ParDVR e n v) (SecB e I v) (parY e n v (.inl (i, m))) * toSecB e I v (X m) = 0 := by
  have h : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (secForm (parY e n v) i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
  rw [← h, secForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  simp [toSecB]

theorem secB_chartForm :
    ∑ m, algebraMap (ParDVR e n v) (SecB e I v) (parY e n v (.inr m)) * toSecB e I v (X m) = 1 := by
  have h : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (chartForm (parY e n v)) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  rw [← h, chartForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  simp [toSecB]

variable (𝔫 : Ideal (SecB e I v)) [𝔫.IsPrime]

def quotToBn : MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I →+* Localization.AtPrime 𝔫 :=
  Ideal.Quotient.lift _ ((algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp (toSecB e I v))
    (fun g hg => by rw [RingHom.comp_apply, RingHom.mem_ker.mp (toSecB_le e hg), map_zero])

theorem quotToBn_mk (g : MvPolynomial (Fin n) (𝓞 K)) :
    quotToBn e 𝔫 (Ideal.Quotient.mk _ g) = algebraMap _ (Localization.AtPrime 𝔫) (toSecB e I v g) :=
  Ideal.Quotient.lift_mk _ _ _

def parB (p : Par e n) : Localization.AtPrime 𝔫 :=
  algebraMap (SecB e I v) _ (algebraMap (ParDVR e n v) (SecB e I v) (parY e n v p))

variable {e j 𝔫}

def baseToBn (hj : toSecB e I v (X j) ∉ 𝔫) : Base I j →+* Localization.AtPrime 𝔫 :=
  IsLocalization.Away.lift (Ideal.Quotient.mk (integralModel I) (X j)) (g := quotToBn e 𝔫)
    (by
      rw [quotToBn_mk]
      exact IsLocalization.map_units (Localization.AtPrime 𝔫) (⟨toSecB e I v (X j), hj⟩ : 𝔫.primeCompl))

theorem baseToBn_toBase (hj : toSecB e I v (X j) ∉ 𝔫) (g : MvPolynomial (Fin n) (𝓞 K)) :
    baseToBn hj (toBase I j g) = algebraMap _ _ (toSecB e I v g) := by
  rw [toBase, RingHom.comp_apply, baseToBn, IsLocalization.Away.lift_eq, quotToBn_mk]

def Φ (hj : toSecB e I v (X j) ∉ 𝔫) : Poly e I j →+* Localization.AtPrime 𝔫 :=
  eval₂Hom (baseToBn hj) fun y => parB e 𝔫 (FreePar.val e j y)

theorem Φ_C (hj : toSecB e I v (X j) ∉ 𝔫) (b : Base I j) : Φ hj (C b) = baseToBn hj b := eval₂Hom_C _ _ _

theorem Φ_X (hj : toSecB e I v (X j) ∉ 𝔫) (y : FreePar e j) : Φ hj (X y) = parB e 𝔫 (FreePar.val e j y) :=
  eval₂Hom_X' _ _ _

theorem Φ_cx (hj : toSecB e I v (X j) ∉ 𝔫) (l : Fin n) :
    Φ hj (cx e I j l) = algebraMap _ _ (toSecB e I v (X l)) := by
  rw [cx, Φ_C, baseToBn_toBase]

theorem Φ_cinv_mul (hj : toSecB e I v (X j) ∉ 𝔫) :
    Φ hj (cinv e I j) * algebraMap _ _ (toSecB e I v (X j)) = 1 := by
  rw [← Φ_cx hj, ← map_mul, cinv_mul_cx, map_one]

theorem Φ_val (hj : toSecB e I v (X j) ∉ 𝔫) (p : Par e n) : Φ hj (val e I j p) = parB e 𝔫 p := by
  have hc := Φ_cinv_mul hj
  rcases p with ⟨i, l⟩ | l
  · by_cases hl : l = j
    · subst hl
      have h := congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) (secB_secForm e (I := I) (v := v) i)
      rw [map_sum, map_zero, Fintype.sum_eq_add_sum_subtype_ne _ l] at h
      simp only [map_mul] at h
      simp only [val, dite_true, map_neg, map_mul, map_sum, Φ_X, Φ_cx, FreePar.val, parB]
      exact solve_inl (L := Localization.AtPrime 𝔫) h hc
    · simp only [val, hl, dite_false, Φ_X, FreePar.val]
  · by_cases hl : l = j
    · subst hl
      have h := congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) (secB_chartForm e (I := I) (v := v))
      rw [map_sum, map_one, Fintype.sum_eq_add_sum_subtype_ne _ l] at h
      simp only [map_mul] at h
      simp only [val, dite_true, map_sub, map_one, map_mul, map_sum, Φ_X, Φ_cx, FreePar.val, parB]
      exact solve_inr (L := Localization.AtPrime 𝔫) h hc
    · simp only [val, hl, dite_false, Φ_X, FreePar.val]

theorem Φ_σ (hj : toSecB e I v (X j) ∉ 𝔫) :
    (Φ hj).comp (σ e I j) = (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp
      ((algebraMap (ParDVR e n v) (SecB e I v)).comp (algebraMap _ (ParDVR e n v))) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, σ_C, Φ_C, baseToBn_toBase, toSecB_C]
  · intro p
    simp only [RingHom.comp_apply, σ_X, Φ_val, parB, parY]

end SpecChart

end

end GroundTheory.Heights₂.Heights.Vertical
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

set_option linter.unusedSectionVars false

namespace SpecChart

variable {K : Type} [Field K] [NumberField K] {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) K)} {j : Fin n}
  {v : HeightOneSpectrum (𝓞 K)} {W : Ideal (MvPolynomial (Fin n) (𝓞 K))}

theorem Q_le_comap {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime] (hj : toSecB e I v (X j) ∉ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) :
    Q e I j W ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫)).comap (Φ hj) := by
  rw [Q_eq, Ideal.map_le_iff_le_comap, Ideal.comap_comap, Wb, Ideal.map_le_iff_le_comap,
    Ideal.comap_comap, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro w hw
  rw [Ideal.mem_comap]
  change Φ hj (C (toBase I j w)) ∈ _
  rw [Φ_C, baseToBn_toBase, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔫) 𝔫, ← h𝔫]
  exact Ideal.mem_map_of_mem _ hw

theorem σ_not_mem {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime] (hj : toSecB e I v (X j) ∉ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) (s : MvPolynomial (Par e n) (𝓞 K))
    (hs : s ∈ (parPrime e n v).primeCompl) : σ e I j s ∉ Q e I j W := by
  intro hQ
  have h1 := Q_le_comap hj h𝔫 hQ
  rw [Ideal.mem_comap, ← RingHom.comp_apply, Φ_σ] at h1
  simp only [RingHom.comp_apply] at h1
  have hu : IsUnit (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) s) :=
    IsLocalization.map_units (ParDVR e n v) (⟨s, hs⟩ : (parPrime e n v).primeCompl)
  exact IsLocalRing.notMem_maximalIdeal.mpr ((hu.map _).map _) h1

section Back

variable [(Q e I j W).IsPrime]

def ρ (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    ParDVR e n v →+* Localization.AtPrime (Q e I j W) :=
  IsLocalization.lift (M := (parPrime e n v).primeCompl)
    (g := (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp (σ e I j)) fun s => by
      rw [RingHom.comp_apply, ← IsLocalRing.notMem_maximalIdeal,
        IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)]
      exact hσ s s.2

theorem ρ_algebraMap (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (s : MvPolynomial (Par e n) (𝓞 K)) :
    ρ hσ (algebraMap _ (ParDVR e n v) s) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (σ e I j s) :=
  IsLocalization.lift_eq _ _

theorem ρ_parY (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) (p : Par e n) :
    ρ hσ (parY e n v p) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (val e I j p) := by
  rw [parY, ρ_algebraMap, σ_X]

def G' (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    MvPolynomial (Fin n) (ParDVR e n v) →+* Localization.AtPrime (Q e I j W) :=
  eval₂Hom (ρ hσ) fun l => algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (cx e I j l)

theorem G'_map (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (g : MvPolynomial (Fin n) (𝓞 K)) :
    G' hσ (g.map (algebraMap (𝓞 K) (ParDVR e n v))) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g)) := by
  have h : (G' hσ).comp (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v))) =
      (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp (C.comp (toBase I j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, map_C, G', eval₂Hom_C]
      rw [IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v),
        ρ_algebraMap, MvPolynomial.algebraMap_eq, σ_C]
    · intro l
      simp only [RingHom.comp_apply, map_X, G', eval₂Hom_X', cx]
  exact RingHom.congr_fun h g

theorem G'_kills (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    secIdeal (modelR e I v) (parY e n v) ≤ RingHom.ker (G' hσ) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [modelR, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, G'_map, toBase, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero, map_zero, map_zero]
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    rw [SetLike.mem_coe, RingHom.mem_ker, secForm, linForm, map_sum]
    simp only [map_mul, G', eval₂Hom_C, eval₂Hom_X', ρ_parY]
    have h := congrArg (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))) (sum_val_inl e I j i)
    simpa only [map_sum, map_mul, map_zero] using h
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    rw [SetLike.mem_coe, RingHom.mem_ker, chartForm, linForm, map_sub, map_sum, map_one]
    simp only [map_mul, G', eval₂Hom_C, eval₂Hom_X', ρ_parY]
    have h := congrArg (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))) (sum_val_inr e I j)
    simpa only [map_sum, map_mul, map_sub, map_one, map_zero] using h

def G (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    SecB e I v →+* Localization.AtPrime (Q e I j W) :=
  Ideal.Quotient.lift _ (G' hσ) fun _ ha => RingHom.mem_ker.mp (G'_kills hσ ha)

theorem G_toSecB (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (g : MvPolynomial (Fin n) (𝓞 K)) : G hσ (toSecB e I v g) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g)) := by
  rw [toSecB, RingHom.comp_apply, G, Ideal.Quotient.lift_mk, G'_map]

theorem G_algebraMap (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (r : ParDVR e n v) : G hσ (algebraMap _ (SecB e I v) r) = ρ hσ r := by
  rw [← Ideal.Quotient.mk_algebraMap, G, Ideal.Quotient.lift_mk, MvPolynomial.algebraMap_eq, G', eval₂Hom_C]

theorem G_mem (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} (h𝔫 : W.map (toSecB e I v) = 𝔫) {b : SecB e I v} (hb : b ∈ 𝔫) :
    G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) := by
  rw [← h𝔫] at hb
  have h : W.map (toSecB e I v) ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))).comap (G hσ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro w hw
    rw [Ideal.mem_comap, Ideal.mem_comap, G_toSecB, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)]
    exact C_toBase_mem_Q e j hw
  exact h hb

theorem mem_of_toSecB_mem [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} (h𝔫 : W.map (toSecB e I v) = 𝔫) {g : MvPolynomial (Fin n) (𝓞 K)}
    (hg : toSecB e I v g ∈ 𝔫) : g ∈ W := by
  have h := G_mem hσ h𝔫 hg
  rw [G_toSecB, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)] at h
  exact mem_of_C_toBase_mem_Q e j hPW hXj h

theorem mem_of_G_mem (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} [𝔫.IsMaximal] (h𝔫 : W.map (toSecB e I v) = 𝔫) {b : SecB e I v}
    (hb : G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))) : b ∈ 𝔫 := by
  have h : 𝔫 = (IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))).comap (G hσ) :=
    Ideal.IsMaximal.eq_of_le ‹_› (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
      (fun _ hb => G_mem hσ h𝔫 hb)
  rw [h]
  exact hb

variable {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime]

def Gloc (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫) :
    Localization.AtPrime 𝔫 →+* Localization.AtPrime (Q e I j W) :=
  IsLocalization.lift (M := 𝔫.primeCompl) (g := G hσ) fun b =>
    IsLocalRing.notMem_maximalIdeal.mp fun h => b.2 (hG _ h)

theorem Gloc_algebraMap (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (b : SecB e I v) : Gloc hσ hG (algebraMap _ _ b) = G hσ b :=
  IsLocalization.lift_eq _ _

theorem Gloc_max (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) {x : Localization.AtPrime 𝔫}
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫)) :
    Gloc hσ hG x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at hx
  have h : 𝔫.map (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))).comap (Gloc hσ hG) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, Ideal.mem_comap, Gloc_algebraMap]
    exact G_mem hσ h𝔫 hb
  exact h hx

theorem Gloc_Φ (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫) :
    (Gloc hσ hG).comp (Φ hj) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, Φ_C]
    have h : (Gloc hσ hG).comp (baseToBn hj) =
        (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp C := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (integralModel I) (X j)))
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun g => ?_
      change Gloc hσ hG (baseToBn hj (toBase I j g)) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g))
      rw [baseToBn_toBase, Gloc_algebraMap, G_toSecB]
    exact RingHom.congr_fun h b
  · intro y
    simp only [RingHom.comp_apply, Φ_X, parB, Gloc_algebraMap, G_algebraMap, ρ_parY, val_free]

theorem Φ_isUnit (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) (c : Poly e I j) (hc : c ∈ (Q e I j W).primeCompl) :
    IsUnit (Φ hj c) := by
  by_contra hu
  rw [← IsLocalRing.notMem_maximalIdeal, not_not] at hu
  have h2 := Gloc_max hσ hG h𝔫 hu
  rw [← RingHom.comp_apply, Gloc_Φ, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)] at h2
  exact hc h2

def Φloc (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : Localization.AtPrime (Q e I j W) →+* Localization.AtPrime 𝔫 :=
  IsLocalization.lift (M := (Q e I j W).primeCompl) (g := Φ hj) fun c => Φ_isUnit hj hσ hG h𝔫 c c.2

theorem Φloc_algebraMap (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) (c : Poly e I j) :
    Φloc hj hσ hG h𝔫 (algebraMap _ _ c) = Φ hj c :=
  IsLocalization.lift_eq _ _

theorem Gloc_Φloc (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : (Gloc hσ hG).comp (Φloc hj hσ hG h𝔫) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Q e I j W).primeCompl
  refine RingHom.ext fun c => ?_
  simp only [RingHom.comp_apply, Φloc_algebraMap, RingHom.id_apply]
  rw [← RingHom.comp_apply, Gloc_Φ]

theorem Φloc_Gloc (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : (Φloc hj hσ hG h𝔫).comp (Gloc hσ hG) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext 𝔫.primeCompl
  have hρ : (Φloc hj hσ hG h𝔫).comp (ρ hσ) =
      (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp (algebraMap (ParDVR e n v) (SecB e I v)) := by
    apply IsLocalization.ringHom_ext (parPrime e n v).primeCompl
    refine RingHom.ext fun s => ?_
    simp only [RingHom.comp_apply, ρ_algebraMap, Φloc_algebraMap]
    rw [← RingHom.comp_apply (Φ hj), Φ_σ]
    rfl
  have h : (Φloc hj hσ hG h𝔫).comp (G hσ) = algebraMap (SecB e I v) (Localization.AtPrime 𝔫) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      have := RingHom.congr_fun hρ r
      simp only [RingHom.comp_apply] at this ⊢
      rw [G, Ideal.Quotient.lift_mk, G', eval₂Hom_C, this, ← Ideal.Quotient.mk_algebraMap,
        MvPolynomial.algebraMap_eq]
    · intro l
      simp only [RingHom.comp_apply]
      rw [G, Ideal.Quotient.lift_mk, G', eval₂Hom_X', Φloc_algebraMap, Φ_cx]
      simp [toSecB]
  refine RingHom.ext fun b => ?_
  simp only [RingHom.comp_apply, Gloc_algebraMap, RingHom.id_apply]
  exact RingHom.congr_fun h b

theorem quotToBn_flat (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : RingHom.Flat (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (S := Localization.AtPrime 𝔫) (quotToBn e 𝔫) := by
  have h : quotToBn e 𝔫 = (Φloc hj hσ hG h𝔫).comp
      ((algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp
        ((C : Base I j →+* Poly e I j).comp
          (algebraMap (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (Base I j)))) := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun g => ?_
    change quotToBn e 𝔫 (Ideal.Quotient.mk _ g) =
      Φloc hj hσ hG h𝔫 (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g)))
    rw [quotToBn_mk, Φloc_algebraMap, Φ_C, baseToBn_toBase]
  have hbij : Function.Bijective (Φloc hj hσ hG h𝔫) :=
    Function.bijective_iff_has_inverse.mpr ⟨Gloc hσ hG,
      fun x => RingHom.congr_fun (Gloc_Φloc hj hσ hG h𝔫) x,
      fun y => RingHom.congr_fun (Φloc_Gloc hj hσ hG h𝔫) y⟩
  have h1 : (algebraMap (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (Base I j)).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Base I j) (Submonoid.powers (Ideal.Quotient.mk (integralModel I) (X j))))
  have h2 : (C : Base I j →+* Poly e I j).Flat := by
    rw [← MvPolynomial.algebraMap_eq]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have h3 : RingHom.Flat (R := Poly e I j) (S := Localization.AtPrime (Q e I j W))
      (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))) :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization.AtPrime (Q e I j W)) (Q e I j W).primeCompl)
  rw [h]
  exact RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.comp h1 h2) h3) (RingHom.Flat.of_bijective hbij)

end Back

theorem contraction_and_flat [W.IsPrime] (𝔫 : Ideal (SecB e I v)) [𝔫.IsMaximal]
    (hPW : integralModel I ≤ W) (h𝔫 : W.map (toSecB e I v) = 𝔫) :
    (∀ g, toSecB e I v g ∈ 𝔫 → g ∈ W) ∧ RingHom.Flat (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (S := Localization.AtPrime 𝔫) (quotToBn e 𝔫) := by
  obtain ⟨j, hj⟩ := exists_secCoord_not_mem e I v 𝔫 (Ideal.IsMaximal.ne_top ‹_›)
  have hXj : X j ∉ W := fun h => hj (h𝔫 ▸ Ideal.mem_map_of_mem _ h)
  have := Q_isPrime e j hPW hXj
  have hσ := σ_not_mem hj h𝔫
  have hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫 :=
    fun b hb => mem_of_G_mem hσ h𝔫 hb
  exact ⟨fun g hg => mem_of_toSecB_mem hPW hXj hσ h𝔫 hg, quotToBn_flat hj hσ hG h𝔫⟩

end SpecChart

end

end GroundTheory.Heights₂.Heights.Vertical
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem SpecChart.proof : SpecChart.Statement := by
  intro K _ _ n e I v _ 𝔫 W _ hW h𝔫
  have := 𝔫.isMaximal
  have hPW : integralModel I ≤ W := le_trans le_sup_left hW.1.1.2
  have h𝔫' : W.map (toSecB e I v) = 𝔫.asIdeal := by rw [← secIdealOf_eq_map]; exact h𝔫
  obtain ⟨hcontr, hflat⟩ := SpecChart.contraction_and_flat 𝔫.asIdeal hPW h𝔫'
  have hunit : ∀ s : W.primeCompl, IsUnit (((algebraMap (SecB e I v)
      (Localization.AtPrime 𝔫.asIdeal)).comp (toSecB e I v)) s) := fun s =>
    IsLocalization.map_units (Localization.AtPrime 𝔫.asIdeal)
      (⟨toSecB e I v s, fun h => s.2 (hcontr _ h)⟩ : 𝔫.asIdeal.primeCompl)
  let ψ0 : Localization.AtPrime W →+* Localization.AtPrime 𝔫.asIdeal :=
    IsLocalization.lift (M := W.primeCompl) hunit
  have hψ0 : ∀ g, ψ0 (algebraMap _ (Localization.AtPrime W) g) =
      algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal) (toSecB e I v g) :=
    fun g => IsLocalization.lift_eq hunit g
  have hker : (integralModel I).map (algebraMap _ (Localization.AtPrime W)) ≤ RingHom.ker ψ0 := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, hψ0, RingHom.mem_ker.mp (SpecChart.toSecB_le e hg), map_zero]
  have hker' : ∀ a ∈ (integralModel I).map (algebraMap _ (Localization.AtPrime W)), ψ0 a = 0 :=
    fun a ha => RingHom.mem_ker.mp (hker ha)
  let ψ := Ideal.Quotient.lift _ ψ0 hker'
  have hψ : ∀ g, ψ (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime W) g)) =
      algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal) (toSecB e I v g) := fun g => by
    show Ideal.Quotient.lift _ ψ0 hker' (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk, hψ0]
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map (ψ.comp (Ideal.Quotient.mk _)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫.asIdeal) := by
    have hcomp : (ψ.comp (Ideal.Quotient.mk _)).comp (algebraMap _ (Localization.AtPrime W)) =
        (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)).comp (toSecB e I v) :=
      RingHom.ext fun g => hψ g
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := W), Ideal.map_map, hcomp, ← Ideal.map_map, h𝔫',
      Localization.AtPrime.map_eq_maximalIdeal]
  refine ⟨ψ, fun g => ?_, ?_, ?_, hmax⟩
  · rw [hψ]
    rfl
  · exact ((IsLocalRing.local_hom_TFAE (ψ.comp (Ideal.Quotient.mk _))).out 2 0).mp hmax.le
  · have := SpecChart.isLocalization_quot W (integralModel I)
    refine SpecChart.flat_of_isLocalization_comp (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I)
      (S := Localization.AtPrime W ⧸ (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
      (T := Localization.AtPrime 𝔫.asIdeal) (W.primeCompl.map (Ideal.Quotient.mk (integralModel I))) ψ ?_
    have h : ψ.comp (algebraMap (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I)
        (Localization.AtPrime W ⧸ (integralModel I).map (algebraMap _ (Localization.AtPrime W)))) =
        SpecChart.quotToBn e 𝔫.asIdeal := by
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun g => ?_
      simp only [RingHom.comp_apply]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, hψ, SpecChart.quotToBn_mk]
    rw [h]
    exact hflat

end

end GroundTheory.Heights₂.Heights.Vertical
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem GenericFormsKer.proof : GenericFormsKer.Statement := by
  intro F L _ _ _ ι _ e r hre u hu b c h j
  classical

  set V : Submodule F (ι → F) := Submodule.span F (Set.range b) with hV
  set B := Module.finBasis F V
  set r' := Module.finrank F V
  have hr' : r' ≤ e := (finrank_range_le_card b).trans (by simpa using hre)
  let v : Fin r' → ι → F := fun l => (B l : ι → F)
  have hbm : ∀ m, b m ∈ V := fun m => Submodule.subset_span ⟨m, rfl⟩

  let c' : Fin r' → L := fun l => ∑ m, c m * algebraMap F L (B.repr ⟨b m, hbm m⟩ l)
  have hw : ∀ j, ∑ m, c m * algebraMap F L (b m j) = ∑ l, c' l * algebraMap F L (v l j) := by
    intro j
    have hexp : ∀ m, b m j = ∑ l, B.repr ⟨b m, hbm m⟩ l * v l j := by
      intro m
      have := congrFun (congrArg Subtype.val (B.sum_repr ⟨b m, hbm m⟩)) j
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      exact this.symm
    simp only [hexp, map_sum, map_mul, Finset.mul_sum, c', Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring

  let M : Matrix (Fin r') (Fin r') L :=
    fun i l => ∑ j, u (Fin.castLE hr' i, j) * algebraMap F L (v l j)
  have hMc : M.mulVec c' = 0 := by
    funext i
    have hi := h (Fin.castLE hr' i)
    simp only [hw] at hi
    simp only [Matrix.mulVec, dotProduct, M, Pi.zero_apply, Finset.sum_mul]
    rw [Finset.sum_comm, ← hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

  let P : Matrix (Fin r') (Fin r') (MvPolynomial (Fin e × ι) F) :=
    fun i l => ∑ j, X (Fin.castLE hr' i, j) * C (v l j)
  have hPM : (aeval u : MvPolynomial (Fin e × ι) F →ₐ[F] L).toRingHom.mapMatrix P = M := by
    ext i l
    change aeval u (∑ j, X (Fin.castLE hr' i, j) * C (v l j)) = M i l
    simp only [map_sum, map_mul, aeval_X, aeval_C, M]

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype
  let A₀ : Fin r' → ι → F := fun l j => B.repr (g (Pi.single j 1)) l
  have hA₀ : ∀ i l, ∑ j, A₀ i j * v l j = if i = l then 1 else 0 := by
    intro i l
    have hvl : (∑ j, v l j • (Pi.single j (1 : F) : ι → F)) = V.subtype (B l) := by
      funext k
      simp [v, Finset.sum_apply, Pi.single_apply]
    have := congrArg (fun x => B.repr (g x) i) hvl
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul] at this
    rw [← LinearMap.comp_apply, hg, LinearMap.id_apply, Module.Basis.repr_self_apply] at this
    have hil : (if i = l then (1 : F) else 0) = if l = i then 1 else 0 := by
      by_cases hh : i = l
      · simp [hh]
      · simp [hh, Ne.symm hh]
    rw [hil, ← this]
    simp only [A₀]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

  let x : Fin e × ι → F := fun p => if hp : p.1.val < r' then A₀ ⟨p.1.val, hp⟩ p.2 else 0
  have hPx : (eval x).mapMatrix P = 1 := by
    ext i l
    change eval x (∑ j, X (Fin.castLE hr' i, j) * C (v l j)) = (1 : Matrix (Fin r') (Fin r') F) i l
    simp only [map_sum, map_mul, eval_X, eval_C, Matrix.one_apply]
    rw [← hA₀]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [x, Fin.castLE]
  have hPdet : P.det ≠ 0 := by
    intro h0
    have := congrArg (eval x) h0
    rw [RingHom.map_det, hPx, Matrix.det_one, map_zero] at this
    exact one_ne_zero this
  have hMdet : M.det ≠ 0 := by
    rw [← hPM, ← RingHom.map_det]
    have hinj : Function.Injective (aeval u : MvPolynomial (Fin e × ι) F →ₐ[F] L) :=
      algebraicIndependent_iff_injective_aeval.1 hu
    exact (map_ne_zero_iff _ hinj).2 hPdet
  have hc' : c' = 0 := Matrix.eq_zero_of_mulVec_eq_zero hMdet hMc
  rw [hw]
  simp [hc']

end

end GroundTheory.Heights₂.Heights.Vertical
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin

theorem DerivSpanTrdeg.derivation_eq_zero_of_isSeparable {k K M : Type*} [Field k] [Field K]
    [Algebra k K] [AddCommGroup M] [Module K M] [Module k M] [IsScalarTower k K M] (s : Set K)
    [Algebra.IsSeparable (IntermediateField.adjoin k s) K] (D : Derivation k K M)
    (hs : ∀ x ∈ s, D x = 0) : D = 0 := by
  have hE : ∀ x ∈ IntermediateField.adjoin k s, D x = 0 := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact hs x hx
    | algebraMap x => exact D.map_algebraMap x
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | inv x _ hx => rw [Derivation.leibniz_inv, hx, smul_zero]
    | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  ext α
  set E := IntermediateField.adjoin k s
  have hsep : IsSeparable E α := Algebra.IsSeparable.isSeparable E α
  set g : Polynomial K := (minpoly E α).map (algebraMap E K)
  have h0 : D (g.eval α) = 0 := by
    rw [Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
  have hc : D.mapCoeffs g = 0 := by
    ext i
    simp only [Derivation.mapCoeffs_apply, g, Polynomial.coeff_map]
    exact (hE _ ((minpoly E α).coeff i).2).trans (by simp)
  rw [Derivation.apply_eval_eq, hc, map_zero, zero_add] at h0
  have hne : g.derivative.eval α ≠ 0 := by
    simp only [g]
    rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval E α)
  simpa [hne] using h0

theorem DerivSpanTrdeg.proof : DerivSpanTrdeg.Statement := by
  intro k L _ _ _ _ ι _ z e he
  classical
  set F₀ := IntermediateField.adjoin k (Set.range z)
  have : Algebra.EssFiniteType k F₀ := by
    rw [IntermediateField.essFiniteType_iff]
    exact ⟨Finset.univ.image z, by simp [F₀]⟩
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F₀
  have htr : Algebra.trdeg k F₀ = Algebra.trdeg k (Algebra.adjoin k (Set.range z)) := by
    have := trdeg_add_eq k (Algebra.adjoin k (Set.range z)) (A := F₀)
    rw [trdeg_eq_zero (R := Algebra.adjoin k (Set.range z)) (A := F₀), add_zero] at this
    exact this.symm
  have hcard : s.card ≤ e := by
    have h1 := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset, htr] at h1
    exact_mod_cast h1 ▸ he
  let N : Submodule F₀ Ω[F₀⁄k] :=
    Submodule.span F₀ (Set.range fun x : s => KaehlerDifferential.D k F₀ x)
  have hspan : N = ⊤ := by
    have hD := DerivSpanTrdeg.derivation_eq_zero_of_isSeparable (M := Ω[F₀⁄k] ⧸ N) (s : Set F₀)
      (N.mkQ.compDer (KaehlerDifferential.D k F₀)) (fun x hx => by
        change N.mkQ (KaehlerDifferential.D k F₀ x) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have := congrArg (fun D => D x) hD
    simpa [Submodule.Quotient.mk_eq_zero] using this
  have hr : Module.finrank F₀ Ω[F₀⁄k] ≤ e := by
    have h := finrank_range_le_card (R := F₀) (fun x : s => KaehlerDifferential.D k F₀ x)
    change Module.finrank F₀ N ≤ _ at h
    rw [hspan, finrank_top, Fintype.card_coe] at h
    exact h.trans hcard
  let ω := Module.finBasis F₀ Ω[F₀⁄k]
  refine ⟨Module.finrank F₀ Ω[F₀⁄k], hr, fun m j =>
    ω.repr (KaehlerDifferential.D k F₀ ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) m, ?_⟩
  intro D
  let D' : Derivation k F₀ L := D.compAlgebraMap F₀
  let φ := (KaehlerDifferential.linearMapEquivDerivation k F₀).symm D'
  refine ⟨fun m => φ (ω m), fun j => ?_⟩
  have h1 : D (z j) =
      φ (KaehlerDifferential.D k F₀ ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) := by
    have h := LinearEquiv.apply_symm_apply (KaehlerDifferential.linearMapEquivDerivation k F₀) D'
    exact (congrArg (fun D'' : Derivation k F₀ L =>
      D'' ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) h).symm
  rw [h1, ← ω.sum_repr (KaehlerDifferential.D k F₀ _), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, Algebra.smul_def, mul_comm]
  rfl

end

end GroundTheory.Heights₂.Heights.Vertical
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

private theorem coneDim₃ : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof
    (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof)
    GroundTheory.Heights₂.Heights.IncIdealPrime.full

theorem ChartPointTrdeg.full : ChartPointTrdeg.Statement :=
  ChartPointTrdeg.proof coneDim₃ GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof
theorem SpecChart.full : SpecChart.Statement := SpecChart.proof
theorem GenericFormsKer.full : GenericFormsKer.Statement := GenericFormsKer.proof
theorem DerivSpanTrdeg.full : DerivSpanTrdeg.Statement := DerivSpanTrdeg.proof

theorem SecPointSeparable.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    SecPointSeparable.Statement :=
  SecPointSeparable.proof GenericFormsKer.full DerivSpanTrdeg.full h

theorem GenSecSeparable.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    GenSecSeparable.Statement :=
  GenSecSeparable.proof SecAlgFinite.full GenSecDomain.full ChartPointTrdeg.full
    (SecPointSeparable.of_freeParAlgIndep h)

theorem SpecLength.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) : SpecLength.Statement := by
  have cnf : ChowNormForm.Statement :=
    ChowNormForm.proof
      (ChowNormFormGeneric.proof SecAlgFinite.full GenSecDomain.full (GenSecSeparable.of_freeParAlgIndep h)
        ChowSecDvd.full NormFormIrreducible.full GenChowIrreducible.full NormFormDvd.full)
      SecAlgFieldChange.full
  have nzd : SecLinNZD.Statement := SecLinNZD.proof cnf NormFormEval.full SpecFirstNeField.full
  exact SpecLength.proof SpecChart.full FiniteOrd.full ParDVRIsDVR.full SecBFinite.full
    (SecBLinInj.proof SecBGeneric.full SecBTorsionFree.full nzd ParAlgIndep.full)

theorem ChowFormSectionVertical.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    ChowFormSectionVertical.Statement :=
  ChowFormSectionVertical.of_chartPoint_secPoint_specChart ChartPointTrdeg.full
    (SecPointSeparable.of_freeParAlgIndep h) SpecChart.full

end GroundTheory.Heights₂.Heights.Vertical
end
