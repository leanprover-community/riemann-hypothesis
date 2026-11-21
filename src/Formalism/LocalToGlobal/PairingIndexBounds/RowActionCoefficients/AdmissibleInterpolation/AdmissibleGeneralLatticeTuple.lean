import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.WeylComplementInDetCoeffSpan
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.CoefficientProductHolds
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.CoefProd
import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.ShapeEvenHolds
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.HighestVectorFullHolds

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

section Coeff

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] {τ : Type*}

theorem eval_mem_span (F : MvPolynomial τ A) (p : τ → R) :
    eval (fun t => algebraMap R A (p t)) F ∈ Submodule.span R (Set.range fun m => coeff m F) := by
  classical
  rw [MvPolynomial.eval_eq]
  refine Submodule.sum_mem _ fun d _ => ?_
  have : (∏ i ∈ d.support, algebraMap R A (p i) ^ d i) = algebraMap R A (∏ i ∈ d.support, p i ^ d i) := by
    simp only [map_prod, map_pow]
  rw [this, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, rfl⟩)

theorem coeff_twist_mem (ρ : A →+* Polynomial A) (ψ : τ → MvPolynomial τ (Polynomial R)) (H : MvPolynomial τ A)
    (hH : map ρ H = eval₂ ((C : Polynomial A →+* MvPolynomial τ (Polynomial A)).comp Polynomial.C)
        (fun t => map (Polynomial.mapRingHom (algebraMap R A)) (ψ t)) H) (m : τ →₀ ℕ) (k : ℕ) :
    (ρ (coeff m H)).coeff k ∈ Submodule.span R (Set.range fun m => coeff m H) := by
  classical
  set g : τ → MvPolynomial τ (Polynomial A) := fun t => map (Polynomial.mapRingHom (algebraMap R A)) (ψ t) with hg
  set f := (C : Polynomial A →+* MvPolynomial τ (Polynomial A)).comp Polynomial.C with hf
  have e1 : eval₂ f g H = ∑ d ∈ H.support, eval₂ f g (monomial d (coeff d H)) := by
    conv_lhs => rw [H.as_sum]
    exact map_sum (eval₂Hom f g) _ _
  rw [← coeff_map, hH, e1, coeff_sum, Polynomial.finsetSum_coeff]
  refine Submodule.sum_mem _ fun d _ => ?_
  have e2 : (d.prod fun n e => g n ^ e) =
      map (Polynomial.mapRingHom (algebraMap R A)) (d.prod fun n e => ψ n ^ e) := by
    simp only [Finsupp.prod, map_prod, map_pow, hg]
  rw [eval₂_monomial, e2, hf, RingHom.comp_apply, coeff_C_mul, coeff_map, Polynomial.coeff_C_mul,
    Polynomial.coe_mapRingHom, Polynomial.coeff_map, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, rfl⟩)

end Coeff

section Row

variable {R : Type*} [CommRing R]

def rowDivL {n : ℕ} (a b : Fin n) (k : ℕ) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] MvPolynomial (Fin n × Fin n) R where
  toFun := rowDiv R a b k
  map_add' f g := by simp only [rowDiv, map_add, Polynomial.coeff_add]
  map_smul' c f := by simp only [rowDiv, map_smul, Polynomial.coeff_smul, RingHom.id_apply]

theorem rowDiv_span {n : ℕ} (a b : Fin n) (k : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) R))
    (hS : ∀ f ∈ S, rowDiv R a b k f ∈ Submodule.span R S) :
    ∀ f ∈ Submodule.span R S, rowDiv R a b k f ∈ Submodule.span R S := by
  have : Submodule.span R S ≤ (Submodule.span R S).comap (rowDivL a b k) :=
    Submodule.span_le.mpr fun f hf => hS f hf
  exact fun f hf => this hf

theorem rowGen_diag_monomial {n : ℕ} (a : Fin n) (d : Fin n × Fin n →₀ ℕ) (c : R) :
    rowGen R a a (monomial d c) = Polynomial.C (monomial d c) *
      (Polynomial.X + 1) ^ (∑ v ∈ d.support, if v.1 = a then d v else 0) := by
  classical
  have hg : ∀ v : Fin n × Fin n, (Polynomial.C (X v) +
      (if v.1 = a then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) : Polynomial (MvPolynomial (Fin n × Fin n) R)) =
      Polynomial.C (X v) * (if v.1 = a then Polynomial.X + 1 else 1) := by
    intro v
    split_ifs with h
    · have : (a, v.2) = v := by rw [← h]
      rw [this]; ring
    · ring
  unfold rowGen
  rw [aeval_monomial]
  simp only [hg, mul_pow]
  rw [Finsupp.prod_mul]
  have h1 : (d.prod fun v e => (Polynomial.C (X v) : Polynomial (MvPolynomial (Fin n × Fin n) R)) ^ e) =
      Polynomial.C (monomial d 1) := by
    rw [monomial_eq, C_1, one_mul]
    simp only [Finsupp.prod, map_prod, map_pow]
  have h2 : (d.prod fun v e => ((if v.1 = a then Polynomial.X + 1 else 1 : Polynomial (MvPolynomial (Fin n × Fin n) R))) ^ e) =
      (Polynomial.X + 1) ^ (∑ v ∈ d.support, if v.1 = a then d v else 0) := by
    rw [Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun v _ => ?_
    split_ifs <;> simp
  rw [h1, h2, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, ← mul_assoc, ← Polynomial.C_mul, C_mul_monomial,
    mul_one]

def rowInd {n : ℕ} (a : Fin n) : Fin n × Fin n → ℤ := fun v => if v.1 = a then 1 else 0

theorem weight_rowInd {n : ℕ} (a : Fin n) (d : Fin n × Fin n →₀ ℕ) :
    Finsupp.weight (rowInd a) d = ((∑ v ∈ d.support, if v.1 = a then d v else 0 : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold rowInd
  split_ifs <;> simp

theorem rowDiv_diag {n : ℕ} (a : Fin n) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) R) (z : ℤ)
    (hf : IsWeightedHomogeneous (rowInd a) f z) : rowDiv R a a k f = (z.toNat.choose k) • f := by
  classical
  have e : ∀ d ∈ f.support, rowDiv R a a k (monomial d (coeff d f)) = (z.toNat.choose k) • monomial d (coeff d f) := by
    intro d hd
    have hw := hf (mem_support_iff.mp hd)
    rw [weight_rowInd] at hw
    rw [rowDiv, rowGen_diag_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow, ← hw, Int.toNat_natCast,
      mul_comm, ← nsmul_eq_mul]
  conv_lhs => rw [f.as_sum]
  rw [show rowDiv R a a k (∑ d ∈ f.support, monomial d (coeff d f)) = rowDivL a a k (∑ d ∈ f.support, monomial d (coeff d f))
    from rfl, map_sum]
  conv_rhs => rw [f.as_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl e

end Row

section Grade

variable {r : ℕ} (ht : Fin r → ℤ)

def htW (n : ℕ) : Fin r × Fin n → ℤ := fun v => ht v.1

def GShift {R : Type*} [CommRing R] {n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ δ : ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous (htW ht n) (P.coeff k) (μ + k * δ)

variable {ht}

theorem gShift_mul {R : Type*} [CommRing R] {n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : ℤ}
    (hP : GShift ht P μ δ) (hQ : GShift ht Q μ' δ) : GShift ht (P * Q) (μ + μ') δ := by
  intro k
  rw [Polynomial.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have e : μ + μ' + (k : ℤ) * δ = (μ + (x.1 : ℤ) * δ) + (μ' + (x.2 : ℤ) * δ) := by
    rw [← hx']; push_cast; ring
  rw [e]
  exact (hP x.1).mul (hQ x.2)

theorem gShift_one {R : Type*} [CommRing R] {n : ℕ} (δ : ℤ) :
    GShift ht (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 δ := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs with h
  · have hk : k = 0 := by omega
    subst hk
    simpa using isWeightedHomogeneous_one R (htW ht n)
  · exact isWeightedHomogeneous_zero R _ _

theorem gShift_pow {R : Type*} [CommRing R] {n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : ℤ}
    (hP : GShift ht P μ δ) (e : ℕ) : GShift ht (P ^ e) (e • μ) δ := by
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact gShift_one δ
  | succ e ih => rw [pow_succ, succ_nsmul]; exact gShift_mul ih hP

theorem gShift_prod {R : Type*} [CommRing R] {n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, GShift ht (P i) (μ i) δ) : GShift ht (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (gShift_one (ht := ht) (R := R) (n := n) δ)
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact gShift_mul (h i (Finset.mem_insert_self _ _))
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem gShift_algebraMap {R : Type*} [CommRing R] {n : ℕ} (c : R) (δ : ℤ) :
    GShift ht (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    rw [MvPolynomial.algebraMap_eq]
    simpa using isWeightedHomogeneous_C (htW ht n) c
  · exact isWeightedHomogeneous_zero R _ _

theorem gShift_gen {R : Type*} [CommRing R] {n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    GShift ht (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (htW ht n v) (ht a - ht b) := by
  intro k
  have hX : IsWeightedHomogeneous (htW ht n) (X v : MvPolynomial (Fin r × Fin n) R)
      (htW ht n v) := isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (htW ht n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (htW ht n (a, v.2)) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs with h
    · subst h; simpa using hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs with hb
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h
        have e : htW ht n v + ((1 : ℕ) : ℤ) * (ht a - ht b) = htW ht n (a, v.2) := by
          simp [htW, hb]
        rw [e]; exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _

theorem gShift_rowGen_monomial (R : Type*) [CommRing R] {n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    GShift ht (rowGen R a b (monomial d c)) (Finsupp.weight (htW ht n) d) (ht a - ht b) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine gShift_mul (gShift_algebraMap c _) ?_
  unfold Finsupp.prod Finsupp.sum
  exact gShift_prod _ _ _ _ fun v _ => gShift_pow (gShift_gen a b v) _

theorem g_rowDiv_shift (R : Type*) [CommRing R] {n : ℕ} (H : ℤ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (htW ht n) f H) :
    IsWeightedHomogeneous (htW ht n) (rowDiv R a b k f) (H + k * (ht a - ht b)) := by
  unfold rowDiv
  conv => enter [2, 1, 2]; rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := gShift_rowGen_monomial (ht := ht) R a b d (coeff d f) k
  rwa [hf (mem_support_iff.mp hd)] at this

theorem g_weight {n : ℕ} (d : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (htW ht n) d = ∑ a : Fin r, ht a * ((Finsupp.weight (rowW r n) d a : ℕ) : ℤ) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib, hf, hg]
  | single v c =>
    simp [Finsupp.weight_apply, htW, rowW, Pi.single_apply, Finsupp.sum_single_index, mul_comm]

theorem g_of_rowW {R : Type*} [CommRing R] {n : ℕ} {f : MvPolynomial (Fin r × Fin n) R} {μ : Fin r → ℕ}
    (hf : IsWeightedHomogeneous (rowW r n) f μ) :
    IsWeightedHomogeneous (htW ht n) f (∑ a : Fin r, ht a * (μ a : ℤ)) := by
  intro d hd
  rw [g_weight, hf hd]

theorem g_applyWord (R : Type) [CommRing R] {n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (w : List (Fin r × Fin r × ℕ)) :
    ∃ z : ℤ, IsWeightedHomogeneous (htW ht n) (applyWord R w (hw R hn ν)) z := by
  induction w with
  | nil => exact ⟨_, g_of_rowW (hwRowWeight R r n hn ν hν)⟩
  | cons x w ih =>
    obtain ⟨z, hz⟩ := ih
    exact ⟨_, g_rowDiv_shift R z x.1 x.2.1 x.2.2 _ hz⟩

end Grade

theorem weyl_le_of {R : Type} [CommRing R] {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν)
    (S : Set (MvPolynomial (Fin n × Fin n) R)) (h0 : hw R le_rfl ν ∈ Submodule.span R S)
    (hS : ∀ a b : Fin n, a ≠ b → ∀ k, ∀ f ∈ S, rowDiv R a b k f ∈ Submodule.span R S) :
    weyl R n n le_rfl ν ≤ Submodule.span R S := by
  have hw' : ∀ w : List (Fin n × Fin n × ℕ), applyWord R w (hw R le_rfl ν) ∈ Submodule.span R S := by
    intro w
    induction w with
    | nil => exact h0
    | cons x w ih =>
      show rowDiv R x.1 x.2.1 x.2.2 (applyWord R w (hw R le_rfl ν)) ∈ _
      by_cases hab : x.1 = x.2.1
      · obtain ⟨z, hz⟩ := g_applyWord (ht := fun b => if b = x.1 then (1 : ℤ) else 0) R le_rfl ν hν w
        rw [← hab, rowDiv_diag x.1 x.2.2 _ z hz]
        exact Submodule.smul_of_tower_mem _ _ ih
      · exact rowDiv_span x.1 x.2.1 x.2.2 S (hS _ _ hab _) _ ih
  exact Submodule.span_le.mpr (by rintro _ ⟨w, rfl⟩; exact hw' w)

section Count

theorem colH_ge_iff {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) (k : ℕ) (s : Fin n) :
    s.val + 1 ≤ colH ν k ↔ k < ν s := by
  unfold colH
  constructor
  · intro h
    by_contra hk
    push Not at hk
    have hsub : (Finset.univ.filter fun t : Fin n => k < ν t) ⊆ Finset.univ.filter fun t : Fin n => t.val < s.val := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      by_contra hts
      push Not at hts
      have := hν (show s ≤ t from Fin.le_iff_val_le_val.mpr hts)
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_filter_val_lt] at this
    omega
  · intro hk
    have hsub : (Finset.univ.filter fun t : Fin n => t.val < s.val + 1) ⊆ Finset.univ.filter fun t : Fin n => k < ν t := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      have := hν (show t ≤ s from Fin.le_iff_val_le_val.mpr (by omega))
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_filter_val_lt] at this
    have := s.isLt
    omega

theorem colH_eq_iff {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) (k : ℕ) (s : Fin n) :
    colH ν k = s.val + 1 ↔ nuNext ν s ≤ k ∧ k < ν s := by
  have h1 := colH_ge_iff ν hν k s
  have hle := colH_le ν k
  unfold nuNext
  split_ifs with hs
  · have h2 := colH_ge_iff ν hν k ⟨s.val + 1, hs⟩
    simp only at h2
    constructor
    · intro h
      refine ⟨?_, h1.mp (by omega)⟩
      by_contra hc
      push Not at hc
      have := h2.mpr hc
      omega
    · rintro ⟨ha, hb⟩
      have := h1.mpr hb
      have : ¬ (s.val + 1 + 1 ≤ colH ν k) := fun hh => by have := h2.mp hh; omega
      omega
  · constructor
    · intro h
      exact ⟨Nat.zero_le _, h1.mp (by omega)⟩
    · rintro ⟨_, hb⟩
      have := h1.mpr hb
      have := s.isLt
      omega

theorem card_Ico_fin (c a b : ℕ) (hb : b ≤ c) :
    (Finset.univ.filter fun k : Fin c => a ≤ k.val ∧ k.val < b).card = b - a := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun k : Fin c => k.val < b)
    (fun k : Fin c => k.val < a)
  rw [Finset.filter_filter, Finset.filter_filter, Fin.card_filter_val_lt] at h
  have e1 : (Finset.univ.filter fun k : Fin c => k.val < b ∧ k.val < a) =
      Finset.univ.filter fun k : Fin c => k.val < min a b := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have e2 : (Finset.univ.filter fun k : Fin c => k.val < b ∧ ¬ k.val < a) =
      Finset.univ.filter fun k : Fin c => a ≤ k.val ∧ k.val < b := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [e1, e2, Fin.card_filter_val_lt] at h
  omega

theorem prod_fin_count {M : Type*} [CommMonoid M] {c n : ℕ} (g : Fin c → ℕ) (hg : ∀ k, g k ≤ n) (F : ℕ → M)
    (hF : F 0 = 1) :
    ∏ k : Fin c, F (g k) =
      ∏ s : Fin n, F (s.val + 1) ^ (Finset.univ.filter fun k : Fin c => g k = s.val + 1).card := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (n + 1)) (g := g)
    (fun k _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hg k)))]
  have inner : ∀ j, ∏ i ∈ Finset.univ.filter (fun i => g i = j), F (g i) =
      F j ^ (Finset.univ.filter fun i => g i = j).card := fun j => by
    rw [Finset.prod_congr rfl (fun i hi => congrArg F (Finset.mem_filter.mp hi).2), Finset.prod_const]
  simp only [inner]
  rw [Finset.prod_range_succ', hF, one_pow, mul_one,
    Fin.prod_univ_eq_prod_range (fun s => F (s + 1) ^ (Finset.univ.filter fun k : Fin c => g k = s + 1).card) n]

theorem count_even {n c : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) (hc : ∀ t, ν t ≤ c) (s : Fin n) :
    (Finset.univ.filter fun k : Fin c => colH ν k.val = s.val + 1).card = ν s - nuNext ν s := by
  have e : (Finset.univ.filter fun k : Fin c => colH ν k.val = s.val + 1) =
      Finset.univ.filter fun k : Fin c => nuNext ν s ≤ k.val ∧ k.val < ν s := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact colH_eq_iff ν hν k.val s
  rw [e, card_Ico_fin c _ _ (hc s)]

theorem count_odd {n c : ℕ} (μ : Fin n → ℕ) (hμ : Antitone μ) (hc : ∀ t, μ t ≤ c) (s : Fin n) :
    (Finset.univ.filter fun k : Fin c => n - colH μ k.val = s.val + 1).card =
      (fun t : Fin n => c - μ t.rev) s - nuNext (fun t : Fin n => c - μ t.rev) s := by
  have hs := s.isLt
  by_cases hl : s.val + 1 < n
  · set s' : Fin n := ⟨n - 2 - s.val, by omega⟩ with hs'
    have e : (Finset.univ.filter fun k : Fin c => n - colH μ k.val = s.val + 1) =
        Finset.univ.filter fun k : Fin c => nuNext μ s' ≤ k.val ∧ k.val < μ s' := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← colH_eq_iff μ hμ k.val s']
      have := colH_le μ k.val
      simp only [hs']
      omega
    rw [e, card_Ico_fin c _ _ (hc s')]
    unfold nuNext
    rw [dif_pos hl, dif_pos (show s'.val + 1 < n by simp only [hs']; omega)]
    have r1 : (⟨s.val + 1, hl⟩ : Fin n).rev = s' := Fin.ext (by simp only [Fin.val_rev, hs']; omega)
    have r2 : s.rev = ⟨s'.val + 1, by simp only [hs']; omega⟩ := Fin.ext (by simp only [Fin.val_rev, hs']; omega)
    simp only [r1, r2]
    have := hμ (show s' ≤ ⟨s'.val + 1, by simp only [hs']; omega⟩ from Fin.le_iff_val_le_val.mpr (by simp))
    have := hc s'
    omega
  · have hn : s.val + 1 = n := by omega
    have e : (Finset.univ.filter fun k : Fin c => n - colH μ k.val = s.val + 1) =
        Finset.univ.filter fun k : Fin c => μ ⟨0, by omega⟩ ≤ k.val ∧ k.val < c := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := colH_ge_iff μ hμ k.val ⟨0, by omega⟩
      have := colH_le μ k.val
      have := k.isLt
      simp only [zero_add] at h1
      constructor
      · intro h
        refine ⟨?_, k.isLt⟩
        by_contra hh
        push Not at hh
        have := h1.mpr hh
        omega
      · rintro ⟨h, _⟩
        have : ¬ 1 ≤ colH μ k.val := fun hh => by have := h1.mp hh; omega
        omega
    rw [e, card_Ico_fin c _ _ le_rfl]
    unfold nuNext
    rw [dif_neg hl]
    have r2 : s.rev = ⟨0, by omega⟩ := Fin.ext (by simp only [Fin.val_rev]; omega)
    simp only [r2]
    omega

end Count

section Even

variable {R : Type} [CommRing R] {n : ℕ}

def lpF (R : Type) [CommRing R] (n s : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  if h : s ≤ n then lpMinor R s h h else 1

theorem lpF_zero : lpF R n 0 = 1 := by
  unfold lpF lpMinor
  rw [dif_pos (Nat.zero_le n), Matrix.det_isEmpty]

theorem prod_lpF_eq_hw (ν : Fin n → ℕ) (c : ℕ) (g : Fin c → ℕ) (hg : ∀ k, g k ≤ n)
    (hcount : ∀ s : Fin n, (Finset.univ.filter fun k : Fin c => g k = s.val + 1).card = ν s - nuNext ν s) :
    ∏ k : Fin c, lpF R n (g k) = hw R le_rfl ν := by
  rw [prod_fin_count g hg (lpF R n) lpF_zero]
  unfold hw
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hcount s, lpF, dif_pos (show s.val + 1 ≤ n from s.isLt)]

def ptE (R : Type) [CommRing R] (n : ℕ) : ℕ × Fin n → R := fun v => if v.1 = v.2.val then 1 else 0

theorem eval_detX (e : ℕ) :
    eval (fun v => algebraMap R (MvPolynomial (Fin n × Fin n) R) (ptE R n v))
      ((Matrix.of fun a i : Fin n => gX R n a i.val).det ^ e) = 1 := by
  rw [map_pow, RingHom.map_det]
  have : (eval fun v => algebraMap R (MvPolynomial (Fin n × Fin n) R) (ptE R n v)).mapMatrix
      (Matrix.of fun a i : Fin n => gX R n a i.val) = 1 := by
    ext a i
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, gX, eval_X, ptE, Matrix.one_apply]
    by_cases h : a = i
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'.symm)), map_zero]
  rw [this, Matrix.det_one, one_pow]

theorem eval_hvE (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ n) :
    eval (fun v => algebraMap R (MvPolynomial (Fin n × Fin n) R) (ptE R n v)) (hvE (gX R n) (gY R n) c h hh) =
      ∏ k, lpF R n (h k) := by
  unfold hvE
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det, lpF, dif_pos (hh k)]
  unfold lpMinor
  congr 1
  ext i t
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, gX, gY, map_sum, map_mul, eval_X, eval_C, ptE]
  rw [Finset.sum_eq_single (Fin.castLE (hh k) i)]
  · simp
  · intro b _ hb
    rw [if_neg (fun h' => hb (Fin.ext (by simp [h']))), map_zero, zero_mul]
  · simp

def psiE (R : Type) [CommRing R] (a b : Fin n) : ℕ × Fin n → MvPolynomial (ℕ × Fin n) (Polynomial R) :=
  fun v => X v + if v.2 = a then C Polynomial.X * X (v.1, b) else 0

theorem rowGen_X (a b : Fin n) (v : Fin n × Fin n) :
    rowGen R a b (X v) = Polynomial.C (X v) + (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  unfold rowGen; rw [aeval_X]

theorem entry_even (a b : Fin n) (i : ℕ) (t : Fin n) :
    map (rowGen R (n := n) a b).toRingHom
        (∑ a' : Fin n, (X (i, a') : GenR R n) * C (X (a', t))) =
      eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiE R a b v))
        (∑ a' : Fin n, (X (i, a') : GenR R n) * C (X (a', t))) := by
  simp only [map_sum, map_mul, map_X, map_C, eval₂Hom_X', eval₂Hom_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowGen_X, psiE,
    map_add, map_X]
  have hL : ∀ a' : Fin n, (X (i, a') : MvPolynomial (ℕ × Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R))) *
      (C (Polynomial.C (X (a', t))) + C (if a' = b then Polynomial.X * Polynomial.C (X (a, t)) else 0)) =
      X (i, a') * C (Polynomial.C (X (a', t))) +
        if a' = b then X (i, b) * C (Polynomial.X * Polynomial.C (X (a, t))) else 0 := by
    intro a'
    split_ifs with h
    · subst h; rw [mul_add]
    · simp
  have hR : ∀ a' : Fin n, ((X (i, a') : MvPolynomial (ℕ × Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R))) +
      map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R)))
        (if a' = a then C Polynomial.X * X (i, b) else 0)) * C (Polynomial.C (X (a', t))) =
      X (i, a') * C (Polynomial.C (X (a', t))) +
        if a' = a then C Polynomial.X * X (i, b) * C (Polynomial.C (X (a, t))) else 0 := by
    intro a'
    split_ifs with h
    · subst h; rw [map_mul, map_C, map_X, Polynomial.coe_mapRingHom, Polynomial.map_X, add_mul]
    · rw [map_zero, add_zero, add_zero]
  rw [Finset.sum_congr rfl fun a' _ => hL a', Finset.sum_congr rfl fun a' _ => hR a', Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _),
    C_mul]
  ring

theorem detX_even (a b : Fin n) (hab : a ≠ b) :
    map (rowGen R (n := n) a b).toRingHom (Matrix.of fun a i : Fin n => gX R n a i.val).det =
      eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiE R a b v))
        (Matrix.of fun a i : Fin n => gX R n a i.val).det := by
  rw [RingHom.map_det, RingHom.map_det]
  set Xm : Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R))) :=
    Matrix.of fun a i : Fin n => X (i.val, a) with hXm
  have h1 : (map (rowGen R (n := n) a b).toRingHom).mapMatrix (Matrix.of fun a i : Fin n => gX R n a i.val) = Xm := by
    refine Matrix.ext fun a' i => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, gX, map_X, hXm]
  have h2 : (eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiE R a b v))).mapMatrix
        (Matrix.of fun a i : Fin n => gX R n a i.val) = Xm.updateRow a (Xm a + (C (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) :
          MvPolynomial (ℕ × Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R))) • Xm b) := by
    refine Matrix.ext fun a' i => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, gX, eval₂Hom_X', psiE, map_add, map_X, hXm]
    by_cases h : a' = a
    · subst h
      rw [Matrix.updateRow_self, if_pos rfl, map_mul, map_C, map_X, Polynomial.coe_mapRingHom, Polynomial.map_X]
      simp only [Pi.add_apply, Pi.smul_apply, Matrix.of_apply, smul_eq_mul]
    · rw [Matrix.updateRow_ne h, if_neg h, map_zero, add_zero]
      rfl
  rw [h1, h2, Matrix.det_updateRow_add_smul_self _ hab]

theorem hvE_even (a b : Fin n) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ n) :
    map (rowGen R (n := n) a b).toRingHom (hvE (gX R n) (gY R n) c h hh) =
      eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiE R a b v))
        (hvE (gX R n) (gY R n) c h hh) := by
  unfold hvE
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i t => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, gX, gY]
  exact entry_even (R := R) a b i.val (Fin.castLE (hh k) t)

theorem twist_even (a b : Fin n) (hab : a ≠ b) (c e : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ n) :
    map (rowGen R (n := n) a b).toRingHom
        ((Matrix.of fun a i : Fin n => gX R n a i.val).det ^ e * hvE (gX R n) (gY R n) c h hh) =
      eval₂ ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiE R a b v))
        ((Matrix.of fun a i : Fin n => gX R n a i.val).det ^ e * hvE (gX R n) (gY R n) c h hh) := by
  rw [← coe_eval₂Hom, map_mul, map_mul, map_pow, map_pow, detX_even a b hab, hvE_even a b c h hh]

end Even

theorem weyl_lattice_det_coeff_span : WeylLatticeInDetCoeffSpan := by
  intro R _ n ν hν c e hc
  refine weyl_le_of ν hν _ ?_ ?_
  · have := eval_mem_span (R := R)
      ((Matrix.of fun a i : Fin n => gX R n a i.val).det ^ e *
        hvE (gX R n) (gY R n) c (fun k => colH ν k.val) (fun k => colH_le ν k.val)) (ptE R n)
    rwa [map_mul, eval_detX, eval_hvE, one_mul,
      prod_lpF_eq_hw ν c (fun k => colH ν k.val) (fun k => colH_le ν k.val) (count_even ν hν hc)] at this
  · rintro a b hab k _ ⟨m, rfl⟩
    exact coeff_twist_mem (rowGen R (n := n) a b).toRingHom (psiE R a b) _ (twist_even a b hab c e _ _) m k

section MatO

variable {S : Type*} [CommRing S] {n : ℕ}

theorem tv_mul_apply (i j : Fin n) (c : S) (M : Matrix (Fin n) (Fin n) S) (a t : Fin n) :
    (Matrix.transvection i j c * M) a t = M a t + if a = i then c * M j t else 0 := by
  rw [Matrix.transvection, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  by_cases h : a = i
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm h]

theorem mulC_tv_apply (i j : Fin n) (c : S) (x : Fin n → ℕ → S) (a : Fin n) (k : ℕ) :
    mulC (Matrix.transvection i j c) x a k = x a k + if a = i then c * x j k else 0 := by
  unfold mulC
  simp only [Matrix.transvection, Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  by_cases h : a = i
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm h]

theorem mulC_one' (x : Fin n → ℕ → S) : mulC (1 : Matrix (Fin n) (Fin n) S) x = x := by
  funext a k
  simp [mulC, Matrix.one_apply]

theorem det_catM_tv (l : ℕ) (i j : Fin n) (hij : i ≠ j) (c : S) (y : Matrix (Fin n) (Fin n) S) (x : Fin n → ℕ → S) :
    (catM l (Matrix.transvection i j c * y) x).det = (catM l y (mulC (Matrix.transvection i j (-c)) x)).det := by
  have h1 : x = mulC (Matrix.transvection i j c) (mulC (Matrix.transvection i j (-c)) x) := by
    rw [← mulC_mul, Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel, Matrix.transvection_zero,
      mulC_one']
  conv_lhs => rw [h1]
  rw [← mul_catM, Matrix.det_mul, Matrix.det_transvection_of_ne i j hij, one_mul]

def revTail (n h : ℕ) (hh : h ≤ n) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (fun t => if ht : t.val < n - h then t else ⟨2 * n - h - 1 - t.val, by have := t.isLt; omega⟩)
    (by
      intro t
      by_cases ht : t.val < n - h
      · simp only [dif_pos ht]
      · have := t.isLt
        have h2 : ¬ (2 * n - h - 1 - t.val < n - h) := by omega
        simp only [dif_neg ht, dif_neg h2]
        exact Fin.ext (by simp only []; omega))

theorem revTail_apply_lt (n h : ℕ) (hh : h ≤ n) (t : Fin n) (ht : t.val < n - h) : revTail n h hh t = t := by
  change (fun t : Fin n => if ht : t.val < n - h then t else
    (⟨2 * n - h - 1 - t.val, by have := t.isLt; omega⟩ : Fin n)) t = t
  simp only [dif_pos ht]

theorem revTail_apply_ge (n h : ℕ) (hh : h ≤ n) (t : Fin n) (ht : ¬ t.val < n - h) :
    (revTail n h hh t).val = 2 * n - h - 1 - t.val := by
  change ((fun t : Fin n => if ht : t.val < n - h then t else
    (⟨2 * n - h - 1 - t.val, by have := t.isLt; omega⟩ : Fin n)) t).val = _
  simp only [dif_neg ht]

theorem det_catM_rev (h : ℕ) (hh : h ≤ n) (y : Matrix (Fin n) (Fin n) S) (x : Fin n → ℕ → S)
    (hx : ∀ a i, x a i = if i + a.val + 1 = n then 1 else 0) :
    ((Equiv.Perm.sign (revTail n h hh) : ℤ) : S) * (catM h y x).det =
      (Matrix.of fun p q : Fin (n - h) => y (Fin.castLE (Nat.sub_le n h) p) (Fin.castLE (Nat.sub_le n h) q)).det := by
  rw [← Matrix.det_permute', det_unit_cols (Nat.sub_le n h)]
  · congr 1
    refine Matrix.ext fun p q => ?_
    have hq : (Fin.castLE (Nat.sub_le n h) q).val < n - h := by simp
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, revTail_apply_lt n h hh _ hq, catM, hq, if_true]
  · intro a t ht
    have hnt : ¬ t.val < n - h := by omega
    have hv := revTail_apply_ge n h hh t hnt
    have := t.isLt
    have h3 : ¬ (revTail n h hh t).val < n - h := by omega
    simp only [Matrix.submatrix_apply, id, catM, h3, if_false, hx]
    rw [hv]
    by_cases hat : a = t
    · subst hat; rw [if_pos (by omega), if_pos rfl]
    · rw [if_neg (fun h' => hat (Fin.ext (by omega))), if_neg hat]

end MatO

section Odd

variable {R : Type} [CommRing R] {n : ℕ}

def ptO (R : Type) [CommRing R] (n : ℕ) : ℕ × Fin n → R := fun v => if v.1 + v.2.val + 1 = n then 1 else 0

theorem eval_hvO (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ n) :
    (∏ k, ((Equiv.Perm.sign (revTail n (h k) (hh k)) : ℤ) : MvPolynomial (Fin n × Fin n) R)) *
      eval (fun v => algebraMap R (MvPolynomial (Fin n × Fin n) R) (ptO R n v)) (hvO (gX R n) (gY R n) c h) =
      ∏ k, lpF R n (n - h k) := by
  unfold hvO
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_catM, det_catM_rev (h k) (hh k), lpF, dif_pos (Nat.sub_le _ _)]
  · unfold lpMinor
    congr 1
    refine Matrix.ext fun p q => ?_
    simp [gY]
  · intro a i
    simp only [gX, eval_X, ptO]
    split_ifs <;> simp

def psiO (R : Type) [CommRing R] (a b : Fin n) : ℕ × Fin n → MvPolynomial (ℕ × Fin n) (Polynomial R) :=
  fun v => X v + if v.2 = b then (-C Polynomial.X) * X (v.1, a) else 0

theorem catM_odd (a b : Fin n) (hab : a ≠ b) (l : ℕ) :
    map (rowGen R (n := n) a b).toRingHom (catM l (gY R n) (gX R n)).det =
      eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiO R a b v))
        (catM l (gY R n) (gX R n)).det := by
  rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_catM, map_catM]
  set Y' : Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R))) :=
    fun a t => C (Polynomial.C (X (a, t))) with hY'
  set X' : Fin n → ℕ → MvPolynomial (ℕ × Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R)) :=
    fun a i => X (i, a) with hX'
  have e1 : (gY R n).map (map (rowGen R (n := n) a b).toRingHom) = Matrix.transvection b a (C Polynomial.X) * Y' := by
    refine Matrix.ext fun a' t => ?_
    rw [tv_mul_apply]
    simp only [Matrix.map_apply, gY, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowGen_X, hY']
    by_cases h : a' = b
    · subst h; rw [if_pos rfl, if_pos rfl, C_add, C_mul]
    · rw [if_neg h, if_neg h, add_zero, add_zero]
  have e2 : (fun a₁ i => map (rowGen R (n := n) a b).toRingHom (gX R n a₁ i)) = X' := by
    funext a' i
    simp only [gX, map_X, hX']
  have e3 : (gY R n).map (eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp
      Polynomial.C) (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiO R a b v))) =
      Y' := by
    refine Matrix.ext fun a' t => ?_
    simp only [Matrix.map_apply, gY, eval₂Hom_C, RingHom.comp_apply, hY']
  have e4 : (fun a₁ i => eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp
      Polynomial.C) (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiO R a b v))
      (gX R n a₁ i)) = mulC (Matrix.transvection b a (-(C Polynomial.X))) X' := by
    funext a' i
    rw [mulC_tv_apply]
    simp only [gX, eval₂Hom_X', psiO, map_add, map_X, hX']
    by_cases h : a' = b
    · subst h; rw [if_pos rfl, if_pos rfl, map_mul, map_neg, map_C, map_X, Polynomial.coe_mapRingHom, Polynomial.map_X]
    · rw [if_neg h, if_neg h, map_zero]
  rw [e1, e2, e3, e4, det_catM_tv l b a (Ne.symm hab)]

theorem twist_odd (a b : Fin n) (hab : a ≠ b) (c : ℕ) (h : Fin c → ℕ) :
    map (rowGen R (n := n) a b).toRingHom (hvO (gX R n) (gY R n) c h) =
      eval₂ ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiO R a b v))
        (hvO (gX R n) (gY R n) c h) := by
  unfold hvO
  rw [← coe_eval₂Hom, map_prod, map_prod]
  exact Finset.prod_congr rfl fun k _ => catM_odd a b hab (h k)

end Odd

theorem weyl_complement_det_coeff_span : WeylComplementInDetCoeffSpan := by
  intro R _ n μ hμ c hc
  have hκ : Antitone (fun t : Fin n => c - μ t.rev) := fun s t hst => by
    have := hμ (Fin.rev_le_rev.mpr hst)
    simp only
    omega
  refine weyl_le_of _ hκ _ ?_ ?_
  · have hm := eval_mem_span (R := R) (hvO (gX R n) (gY R n) c (fun k => colH μ k.val)) (ptO R n)
    have e := eval_hvO (R := R) c (fun k => colH μ k.val) (fun k => colH_le μ k.val)
    rw [prod_lpF_eq_hw _ c (fun k => n - colH μ k.val) (fun k => Nat.sub_le _ _) (count_odd μ hμ hc)] at e
    rw [← e, ← Int.cast_prod, ← zsmul_eq_mul]
    exact Submodule.smul_of_tower_mem _ _ hm
  · rintro a b hab k _ ⟨m, rfl⟩
    exact coeff_twist_mem (rowGen R (n := n) a b).toRingHom (psiO R a b) _ (twist_odd a b hab c _) m k

end Formalism.L2.PairingIndexBounds.Ent
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem evX_gX {K : Type} [CommRing K] {n : ℕ} (x : ℕ × Fin n → K) (a : Fin n) (i : ℕ) : evX x (gX K n a i) = C (x (i, a)) := by
  unfold evX gX
  rw [coe_eval₂Hom, eval₂_X]

theorem evX_gY {K : Type} [CommRing K] {n : ℕ} (x : ℕ × Fin n → K) : (gY K n).map (evX x) = yV K n := by
  ext a t
  rw [Matrix.map_apply]
  unfold evX gY yV
  rw [coe_eval₂Hom, eval₂_C]
  rfl

theorem evX_HgX (j : ℕ) (b : BX X) (x : ℕ × Fin (NJ X j) → X.G.Kf) :
    evX x (HgX X X.G.Kf j b) = srcN X j b fun a i => x (i, a) := by
  unfold HgX srcN
  split_ifs with ho
  · rw [map_hvO, evX_gY]
    simp only [evX_gX]
  · rw [map_mul, map_pow, RingHom.map_det, map_hvE, evX_gY, map_pow, RingHom.map_det]
    simp only [evX_gX]
    congr 3
    ext a i
    simp [evX_gX]

theorem HgX_map (O K : Type) [CommRing O] [CommRing K] (f : O →+* K) (j : ℕ) (b : BX X) :
    map (map f) (HgX X O j b) = HgX X K j b := by
  have hx : ∀ a i, (map (map f) : GenR O (NJ X j) →+* GenR K (NJ X j)) (gX O (NJ X j) a i) = gX K (NJ X j) a i := by
    intro a i
    unfold gX
    rw [map_X]
  have hy : (gY O (NJ X j)).map (map (map f) : GenR O (NJ X j) →+* GenR K (NJ X j)) = gY K (NJ X j) := by
    ext a t
    rw [Matrix.map_apply]
    unfold gY
    rw [map_C, map_X]
  unfold HgX
  split_ifs with ho
  · rw [map_hvO, hy]
    simp only [hx]
  · rw [map_mul, map_pow, RingHom.map_det, map_hvE, hy]
    simp only [hx]
    congr 3
    ext a i
    simp [hx]

theorem hQX (hS : XShape) (j : ℕ) (b : BX X) :
    (weyl X.G.O (NJ X j) (NJ X j) le_rfl (nuM X j b)).map (toK X.G.O X.G.Kf) ≤
      Submodule.span X.G.O (Set.range fun m => coeff m (HgX X X.G.Kf j b)) := by
  obtain ⟨h1, -, hanti, hle, -, -, -, -, -, -⟩ := hS p X j b
  rw [h1]
  have key : weyl X.G.O (NJ X j) (NJ X j) le_rfl (nuS X j b) ≤
      Submodule.span X.G.O (Set.range fun m => coeff m (HgX X X.G.O j b)) := by
    by_cases ho : IsOddPos b.2
    · have hn : nuS X j b = fun t => cX X j b - muX X j (NJ X j) b t.rev := if_pos ho
      unfold HgX
      rw [if_pos ho, hn]
      exact weyl_complement_det_coeff_span X.G.O (NJ X j) _ (hanti _) _ (hle _)
    · have hn : nuS X j b = fun t => muX X j (NJ X j) b t - eX X j b := if_neg ho
      unfold HgX
      rw [if_neg ho]
      refine weyl_lattice_det_coeff_span X.G.O (NJ X j) (nuS X j b) ?_ _ _ ?_
      · rw [hn]
        exact fun a c hac => Nat.sub_le_sub_right (hanti _ hac) _
      · rw [hn]
        exact fun t => (Nat.sub_le _ _).trans (hle _ t)
  refine (Submodule.map_mono key).trans ?_
  rw [Submodule.map_span, ← Set.range_comp]
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  refine ⟨m, ?_⟩
  show _ = map (algebraMap X.G.O X.G.Kf) (coeff m (HgX X X.G.O j b))
  rw [← HgX_map X X.G.O X.G.Kf (algebraMap X.G.O X.G.Kf) j b]
  exact coeff_map _ _ _

end Formalism.L2.PairingIndexBounds.Ent
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Model

section dual

variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [CharZero K]

lemma toK_eq_map {σ : Type} (f : MvPolynomial σ O) : toK O K f = map (algebraMap O K) f := rfl

lemma polyK_torsionFree {σ : Type} : Module.IsTorsionFree O (MvPolynomial σ K) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun a f h => ?_
  rw [← algebraMap_smul K a f, smul_eq_zero] at h
  rcases h with h | h
  · left; exact (IsFractionRing.injective O K) (by rw [h, map_zero])
  · right; exact h

lemma weylK_fg {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    ((weyl O n n le_rfl ν).map (toK O K)).FG := by
  have hM : ((dualWeyl O n n ν).map (toK O K)).FG := by
    apply Submodule.FG.map
    obtain ⟨b, hb, -⟩ := sSBasis O n n ν
    rw [← hb.2.1]
    have := (sSIdxFinite n n ν).to_subtype
    exact Submodule.fg_span (Set.finite_range b)
  have hle : (weyl O n n le_rfl ν).map (toK O K) ≤ (dualWeyl O n n ν).map (toK O K) :=
    Submodule.map_mono (weylLeDual O n n le_rfl ν hν)
  have := isNoetherian_of_fg_of_noetherian _ hM
  have h := IsNoetherian.noetherian (((weyl O n n le_rfl ν).map (toK O K)).comap
    ((dualWeyl O n n ν).map (toK O K)).subtype)
  have h2 := h.map ((dualWeyl O n n ν).map (toK O K)).subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2

end dual

theorem dual_bases_holds : DualBases := by
  intro O K _ _ _ _ _ _ _ n ν hν
  classical
  set c := fockR (hw K (le_rfl : n ≤ n) ν) (hw K le_rfl ν) with hc
  set D := (weyl O n n le_rfl ν).map (toK O K) with hD
  have : Module.IsTorsionFree O (MvPolynomial (Fin n × Fin n) K) := polyK_torsionFree
  have : Module.Finite O D := Module.Finite.iff_fg.mpr (weylK_fg ν hν)
  obtain ⟨N, bD⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := D)
  set e : Fin N → MvPolynomial (Fin n × Fin n) K := fun i => (bD i : MvPolynomial (Fin n × Fin n) K) with he_def
  have he : ∀ i, e i ∈ D := fun i => (bD i).2
  have hDV : ∀ x ∈ D, x ∈ dualWeyl K n n ν := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    rw [toK_eq_map]
    exact weylLeDual K n n le_rfl ν hν (sw_weyl_map (algebraMap O K) le_rfl ν y hy)
  have hrep : ∀ x (hx : x ∈ D), x = ∑ i, bD.repr ⟨x, hx⟩ i • e i := by
    intro x hx
    have h := congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at h
    simpa [he_def] using h.symm
  have hsm : ∀ (a : O) (f : MvPolynomial (Fin n × Fin n) K), a • f = algebraMap O K a • f :=
    fun a f => (algebraMap_smul K a f).symm
  have hDspan : ∀ x ∈ D, x ∈ Submodule.span K (Set.range e) := by
    intro x hx
    rw [hrep x hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : dualWeyl K n n ν ≤ Submodule.span K (Set.range e) := by
    rw [← sw_weyl_eq K n n le_rfl ν hν]
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    apply hDspan
    refine Submodule.mem_map.mpr ⟨applyWord O w (hw O le_rfl ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩
    rw [toK_eq_map, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
  have hliO : LinearIndependent O e := bD.linearIndependent.map' D.subtype (Submodule.ker_subtype D)
  have hli : LinearIndependent K e := (LinearIndependent.iff_fractionRing O K).mp hliO
  set W := Submodule.span K (Set.range e) with hW
  have hWV : W = dualWeyl K n n ν := by
    refine le_antisymm ?_ hspan
    rw [hW, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hDV _ (he i)
  let bW : Module.Basis (Fin N) K W := Module.Basis.span hli
  have hbW : ∀ i, (bW i : MvPolynomial (Fin n × Fin n) K) = e i := fun i =>
    congrArg Subtype.val (Module.Basis.span_apply hli i)
  let Bf : LinearMap.BilinForm K W := LinearMap.mk₂ K (fun x y : W => fockR (x : MvPolynomial (Fin n × Fin n) K) y)
    (fun x x' y => by simp [fockR_add_left]) (fun a x y => by simp [fockR_smul_left])
    (fun x y y' => by simp [fockR_add_right]) (fun a x y => by simp [fockR_smul_right])
  have hBf : ∀ x y : W, Bf x y = fockR (x : MvPolynomial (Fin n × Fin n) K) y := fun _ _ => rfl
  have hnd : Bf.Nondegenerate := by
    constructor
    · intro x hx
      apply Subtype.ext
      refine Top.nondegK K n n le_rfl ν hν x.1 (hWV ▸ x.2) fun P hP => ?_
      rw [fockR_symm]
      exact hx ⟨P, hWV ▸ hP⟩
    · intro y hy
      apply Subtype.ext
      exact Top.nondegK K n n le_rfl ν hν y.1 (hWV ▸ y.2) fun P hP => hy ⟨P, hWV ▸ hP⟩
  let d := Bf.dualBasis hnd bW
  have hd : ∀ i k, fockR (e i) (d k : MvPolynomial (Fin n × Fin n) K) = if i = k then 1 else 0 := by
    intro i k
    have h := LinearMap.BilinForm.apply_dualBasis_left hnd bW k i
    rw [hBf, hbW, fockR_symm] at h
    exact h
  refine ⟨Fin N, inferInstance, inferInstance, e, fun k => c • (d k : MvPolynomial (Fin n × Fin n) K),
    he, ?_, ?_, hspan⟩
  · intro k
    have hkV : c • (d k : MvPolynomial (Fin n × Fin n) K) ∈ dualWeyl K n n ν :=
      Submodule.smul_mem _ _ (hWV ▸ (d k).2)
    refine Top.dualWeylIn O K n n le_rfl ν hν _ hkV fun P hP => ⟨bD.repr ⟨P, hP⟩ k, ?_⟩
    show fockR P (c • (d k : MvPolynomial (Fin n × Fin n) K)) = _
    conv_lhs => rw [hrep P hP]
    rw [fockR_sum_left]
    simp_rw [hsm, fockR_smul_left, fockR_smul_right, hd]
    simp [hc]
  · intro i k
    rw [fockR_smul_right, hd]
    split_ifs <;> simp

end Formalism.L2.PairingIndexBounds.Ent
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem mF_mul (j : ℕ) (b : BX X) (A B : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    mF X j b A * mF X j b B = mF X j b (A * B) := by
  simp only [mF]
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  ext i k
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]

theorem mF_one (j : ℕ) (b : BX X) : mF X j b 1 = 1 := by
  ext i k
  by_cases h : i = k <;> simp [mF, Matrix.one_apply, h]

theorem mF_inv_mul (j : ℕ) (b : BX X) (g : GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    mF X j b ((g⁻¹ : GL _ _) : Matrix _ _ (X.G.P.Qq b.1)) * mF X j b (g : Matrix _ _ (X.G.P.Qq b.1)) = 1 := by
  rw [mF_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mF_one]

theorem mF_det_ne (j : ℕ) (b : BX X) (g : GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    (mF X j b (g : Matrix _ _ (X.G.P.Qq b.1))).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (mF_inv_mul X j b g)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

variable (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

def PhiX (j : ℕ) (l : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] Kc) (a : Kc) (f : MvPowerSeries (X.ZA j) Kc) :
    (X.Pj j).Xsp →ₗ[X.G.Kf] Kc :=
  ((LinearMap.mulLeft Kc a).restrictScalars X.G.Kf) ∘ₗ (l.restrictScalars X.G.Kf) ∘ₗ ((delF X Kc j).flip f)

theorem PhiX_apply (j : ℕ) (l : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] Kc) (a : Kc) (f : MvPowerSeries (X.ZA j) Kc) (G : (X.Pj j).Xsp) :
    PhiX X Kc j l a f G = a * l (delF X Kc j G f) := rfl

def WT (j : ℕ) : Submodule Kc (XspC (X.Pj (j + 1)) Kc) :=
  Submodule.span Kc {z | ∃ F : BX X → MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) X.G.Kf,
    (∀ b, F b ∈ dualWeyl X.G.Kf (NJ X (j + 1)) (NJ X (j + 1)) (nuT X j b)) ∧
      z = map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b) (F b))}

private theorem prod_rowAct_lemma {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (d : K) :
    rowAct K M (C d : MvPolynomial (Fin n × Fin n) K) = C d := by
  simp [rowAct]

private theorem prod_rowAct_lemma_2 {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (yV K n).map (rowAct K M) = M.map C * yV K n := by
  ext a t
  simp [yV, BidetPairing.rowAct_X', Matrix.mul_apply]

private theorem prod_rowAct_lemma_3 {K : Type} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K)
    (y : Fin n → ℕ → K) : mulC A (mulC B y) = mulC (A * B) y := by
  funext a i
  simp only [mulC, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

private theorem prod_rowAct_lemma_4 {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (y : Fin n → ℕ → K) :
    mulC (M.map (C : K →+* MvPolynomial (Fin n × Fin n) K)) (fun a i => C (y a i)) =
      fun a i => C (mulC M y a i) := by
  funext a i
  simp [mulC, map_sum, map_mul]

private theorem prod_rowAct_lemma_5 {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : M.det ≠ 0) (y : Fin n → ℕ → K) (c : ℕ) (h : Fin c → ℕ) :
    rowAct K M (hvO (fun a i => C (y a i)) (yV K n) c h) =
      C (M.det ^ c) * hvO (fun a i => C (mulC M⁻¹ y a i)) (yV K n) c h := by
  show (rowAct K M).toRingHom _ = _
  rw [map_hvO]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, prod_rowAct_lemma]
  rw [prod_rowAct_lemma_2]
  have hy : (fun a i => (C (y a i) : MvPolynomial (Fin n × Fin n) K)) =
      mulC (M.map (C : K →+* MvPolynomial (Fin n × Fin n) K)) (fun a i => C (mulC M⁻¹ y a i)) := by
    rw [prod_rowAct_lemma_4, prod_rowAct_lemma_3, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM),
      mulC_one']
  rw [hy, hvO_mul]
  congr 1
  rw [map_pow, RingHom.map_det, RingHom.mapMatrix_apply]

private theorem prod_rowAct_lemma_6 {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (y : Fin n → ℕ → K) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k : Fin c, h k ≤ n) :
    rowAct K M (hvE (fun a i => C (y a i)) (yV K n) c h hh) =
      hvE (fun a i => C (mulC M.transpose y a i)) (yV K n) c h hh := by
  show (rowAct K M).toRingHom _ = _
  rw [map_hvE]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, prod_rowAct_lemma]
  rw [prod_rowAct_lemma_2, hvE_mul, ← Matrix.transpose_map, prod_rowAct_lemma_4]

private theorem prod_rowAct_lemma_7 (j : ℕ) (b : BX X) (M : Matrix (Fin (NJ X j)) (Fin (NJ X j)) X.G.Kf)
    (hM : M.det ≠ 0) (y : Fin (NJ X j) → ℕ → X.G.Kf) :
    ∃ (c : X.G.Kf) (y'' : Fin (NJ X j) → ℕ → X.G.Kf),
      rowAct X.G.Kf M (srcN X j b y) = c • srcN X j b y'' := by
  unfold srcN
  split_ifs with hb
  · exact ⟨M.det ^ cX X j b, mulC M⁻¹ y, by rw [prod_rowAct_lemma_5 M hM, MvPolynomial.smul_eq_C_mul]⟩
  · refine ⟨(M.det ^ eX X j b)⁻¹, mulC M.transpose y, ?_⟩
    rw [map_mul, prod_rowAct_lemma, prod_rowAct_lemma_6, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
    congr 2
    have hd : (Matrix.of fun (a i : Fin (NJ X j)) => mulC M.transpose y a ↑i) =
        M.transpose * Matrix.of fun (a i : Fin (NJ X j)) => y a ↑i := by
      ext a i
      simp [mulC, Matrix.mul_apply]
    rw [hd, Matrix.det_mul, Matrix.det_transpose, mul_pow, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hM), one_mul]

theorem prod_rowAct (j : ℕ) (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (x : X.FrI j → X.G.Kf) :
    ∃ (a : X.G.Kf) (x'' : ∀ b : BX X, Fin (NJ X j) → ℕ → X.G.Kf),
      ∏ b, rename (emX X j b) (rowAct X.G.Kf (mF X j b ((g b.1)⁻¹ : GL _ _))
        (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b))) = a • ∏ b, rename (emX X j b) (srcN X j b (x'' b)) := by
  have key : ∀ b : BX X, ∃ (c : X.G.Kf) (y'' : Fin (NJ X j) → ℕ → X.G.Kf),
      rename (emX X j b) (rowAct X.G.Kf (mF X j b ((g b.1)⁻¹ : GL _ _))
        (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b))) =
        c • rename (emX X j b) (srcN X j b y'') := by
    intro b
    rw [evX_HgX]
    obtain ⟨c, y'', hc⟩ := prod_rowAct_lemma_7 X j b _ (mF_det_ne X j b (g b.1)⁻¹) _
    exact ⟨c, y'', by rw [hc, MvPolynomial.smul_eq_C_mul, map_mul, rename_C, MvPolynomial.smul_eq_C_mul]⟩
  choose c y'' hc using key
  refine ⟨∏ b, c b, y'', ?_⟩
  rw [Finset.prod_congr rfl (fun b _ => hc b)]
  simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]

end Formalism.L2.PairingIndexBounds.Ent
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

theorem hinjX : Function.Injective (algebraMap X.G.O X.G.Kf) := IsFractionRing.injective X.G.O X.G.Kf

theorem phi_mem (hS : XShape) (hBrS : XBrS) (hInj : XInj) (j : ℕ) (L : (X.Pj j).Tup)
    (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (hg : ∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v)))
    (M : AddSubgroup Kc) (hM : ∀ (o : X.G.O), ∀ a ∈ M, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) * a ∈ M)
    (Φ : (X.Pj j).Xsp →ₗ[X.G.Kf] Kc) (A : MvPolynomial (X.FrI j) Kc) (hA : ∀ m, coeff m A ∈ M)
    (hnum : ∀ x : X.FrI j → X.G.Kf, Φ (sX X j (fun v => g v) • ∏ b, rename (emX X j b) (rowAct X.G.Kf (mF X j b ((g b.1)⁻¹ : GL _ _))
      (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b)))) = eval (fun t => algebraMap X.G.Kf Kc (x t)) A) :
    ∀ G ∈ (X.Pj j).HtupW L, Φ G ∈ M := by
  have : CharZero X.G.Kf := (algebraMap X.G.Kf Kc).charZero
  let T : Submodule X.G.O (X.Pj j).Xsp :=
    { carrier := {G | Φ G ∈ M}
      add_mem' := fun {a b} ha hb => by
        show Φ (a + b) ∈ M
        rw [map_add]; exact M.add_mem ha hb
      zero_mem' := by show Φ 0 ∈ M; rw [map_zero]; exact M.zero_mem
      smul_mem' := fun o G hG => by
        show Φ (o • G) ∈ M
        rw [← algebraMap_smul X.G.Kf o G, map_smul, Algebra.smul_def]
        exact hM o _ hG }
  refine hBrS p X (hinjX X) j L (fun v => g v) (fun v => (Matrix.isUnit_iff_isUnit_det _).1 (g v).isUnit) hg T ?_
  intro F hF
  let Φ' : (X.Pj j).Xsp →ₗ[X.G.Kf] Kc := Φ ∘ₗ (LinearMap.lsmul X.G.Kf (X.Pj j).Xsp (sX X j fun v => g v))
  exact src_abs (O := X.G.O) (emX X j) (xmX X j) (hInj p X j).2 (nuM X j) (fun b => mF X j b (g b.1))
    (fun b => mF X j b ((g b.1)⁻¹ : GL _ _)) (fun b => mF_inv_mul X j b (g b.1)) M hM (HgX X X.G.Kf j) (hQX X hS j) Φ' A hA hnum
    interpolation_holds coefficient_product_holds F hF

theorem xSpan (hS : XShape) (hBrS : XBrS) (hInj : XInj) (hSp : XSpanN) (j : ℕ) (L : (X.Pj j).Tup)
    (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (hg : ∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v)))
    (f : MvPowerSeries (X.ZA j) Kc) (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).HtupW L) : delF X Kc j G f ∈ WT X Kc j := by
  by_contra hne
  obtain ⟨l, hl1, hl2⟩ := Submodule.exists_le_ker_of_notMem hne
  have h0 := phi_mem X Kc hS hBrS hInj j L g hg ⊥ (fun o a ha => by
    rw [AddSubgroup.mem_bot] at ha ⊢; rw [ha, mul_zero]) (PhiX X Kc j l 1 f) 0 (fun m => by rw [coeff_zero]; exact AddSubgroup.zero_mem _)
    (fun x => by
      obtain ⟨a, x'', hx⟩ := prod_rowAct X j g x
      rw [hx, map_zero, PhiX_apply, one_mul, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
      have h1 : delF X Kc j (∏ b, rename (emX X j b) (srcN X j b (x'' b))) f ∈ WT X Kc j := hSp p X Kc j x'' f
      have h2 : l (delF X Kc j (∏ b, rename (emX X j b) (srcN X j b (x'' b))) f) = 0 := hl2 h1
      rw [← algebraMap_smul Kc (sX X j fun v => g v), ← algebraMap_smul Kc a, map_smul, map_smul, h2, smul_zero, smul_zero]) G hG
  rw [AddSubgroup.mem_bot, PhiX_apply, one_mul] at h0
  exact hl1 h0

end Formalism.L2.PairingIndexBounds.Ent
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

theorem nuT_antitone (hS : XShape) (j : ℕ) (b : BX X) : Antitone (nuT X j b) := by
  obtain ⟨-, -, hanti, -⟩ := hS p X j b
  unfold nuT
  split_ifs
  · exact BidetPairing.kap_antitone (hanti _) _
  · exact hanti _

theorem shape_szT (hS : XShape) (j : ℕ) (b : BX X) : shapeDeg (szT X j b) = nuT X j b := by
  obtain ⟨-, -, hanti, hle, -⟩ := hS p X j b
  by_cases ho : IsOddPos b.2
  · have h1 : szT X j b = fun k => NJ X (j + 1) - colH (muX X j (NJ X (j + 1)) b) k.val := by
      funext k; exact if_pos ho
    rw [h1, show nuT X j b = _ from if_pos ho]
    exact shape_odd_holds _ _ (hanti _) _ (hle _)
  · have h1 : szT X j b = fun k => colH (muX X j (NJ X (j + 1)) b) k.val := by
      funext k; exact if_neg ho
    rw [h1, show nuT X j b = _ from if_neg ho]
    exact shape_even_holds _ _ (hanti _) _ (hle _)

theorem xPair (hS : XShape) (hBrS : XBrS) (hInj : XInj) (hMid : XMid) (hU : XUnit)
    (Oc : Subring Kc) (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc)
    (hO : ∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc)
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (i0 : X.Pl → ℕ) (h3 : ∀ v, i0 v ≤ X.G.P.r)
    (f : MvPowerSeries (X.ZA j) Kc) (gg : ℝ)
    (hf : ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ), geX p Oc (coeff n (applyD (X.PI j I i0) f)) gg)
    (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).HtupW La.2)
    (I : ∀ (b : BX X) (k : Fin (cX X j b)), Fin (szT X j b k) → Fin (NJ X (j + 1))) :
    ∃ a ∈ MG p Oc hval gg,
      fockR ((((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
            ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
              (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) La'.2))⁻¹)) *
            (∏ b : BX X, (mF X (j + 1) b (φ.g' b.1) * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)))⁻¹) •
          delF X Kc j G (linSub (bc Kc φ) f))
        (map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b)
          (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1) * DgX X X.G.Kf j i0 b.1).transpose
            (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b))))) = a * ∏ b, cN Kc (nuT X j b) := by
  classical
  by_cases hI : ∀ b k, Function.Injective (I b k)
  · obtain ⟨Ist, ε, hε, hmid⟩ := hMid p X Kc j La La' φ i0 I hI
    set TI := map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b)
      (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1) * DgX X X.G.Kf j i0 b.1).transpose
        (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b)))) with hTI
    set cc : Kc := ∏ b, cN Kc (nuT X j b) with hcc
    have hcc0 : cc ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => cN_ne Kc _
    set S1 : X.G.Kf := ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
            ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
              (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) La'.2))⁻¹)) with hS1
    set s1 : X.G.Kf := (∏ b : BX X, (mF X (j + 1) b (φ.g' b.1) * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)))⁻¹ with hs1
    have hp0 : (p : Kc) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    have hu := hU p X Kc Oc hO hp0 j La.2 La'.2 φ.g φ.g' φ.hg φ.hg' i0 h3
    rw [← hS1, ← hs1] at hu
    set U0 := numericalIdentityScalar X Kc j (fun v => φ.g v) (fun v => φ.g' v) i0 with hU0
    have hεO : ε ∈ Oc := by
      rcases hε with h | h
      · rw [h]; exact Oc.one_mem
      · rw [h]; exact Oc.neg_mem Oc.one_mem
    have key := phi_mem X Kc hS hBrS hInj j La.2 φ.g φ.hg (MG p Oc hval gg) (fun o a ha => geX_mul (hO o) ha)
      (PhiX X Kc j (fockL TI) (cc⁻¹ * algebraMap X.G.Kf Kc (S1 * s1)) (linSub (bc Kc φ) f))
      (C (ε * (algebraMap X.G.Kf Kc (S1 * sX X j (fun v => φ.g v) * s1) * U0)) * applyD (X.PI j Ist i0) f)
      (fun m => by
        rw [coeff_C_mul]
        exact geX_mul (Oc.mul_mem hεO hu) (hf Ist m))
      (fun x => by
        rw [PhiX_apply, map_smul, LinearMap.smul_apply, ← algebraMap_smul Kc (sX X j fun v => φ.g v), map_smul, smul_eq_mul]
        show _ * (_ * fockR _ TI) = _
        rw [hmid f x]
        simp only [map_mul, eval_C]
        field_simp) G hG
    refine ⟨_, key, ?_⟩
    rw [PhiX_apply, ← algebraMap_smul Kc (S1 * s1), fockR_smul_left]
    show _ = _ * _ * fockR _ TI * cc
    field_simp
  · push Not at hI
    obtain ⟨b0, k0, hk⟩ := hI
    refine ⟨0, AddSubgroup.zero_mem _, ?_⟩
    have hb : bideterminant X.G.Kf (szT X j b0) (szT_le X j b0) (I b0) = 0 := by
      unfold bideterminant
      exact Finset.prod_eq_zero (Finset.mem_univ k0) (minor_zero_holds _ _ _ _ _ _ hk)
    have hz : (∏ b, rename (emX X (j + 1) b)
        (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1) * DgX X X.G.Kf j i0 b.1).transpose
          (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b)))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ b0) (by rw [hb, map_zero, map_zero])
    rw [hz, map_zero, fockR_comm, fockR_zero_left, zero_mul]

end Formalism.L2.PairingIndexBounds.Ent
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

theorem admissible_general_lattice_tuple (hS : XShape) (hBrS : XBrS) (hBrT : XBrT) (hInj : XInj) (hSp : XSpanN) (hMid : XMid) (hU : XUnit) (hE : XEdge)
    (Oc : Subring Kc) (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc)
    (hO : ∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc)
    (j : ℕ) (La : X.Lt j) (c' : X.Lv.comp (j + 1)) (L' L'' : (X.Pj (j + 1)).Tup) (i0 : X.Pl → ℕ)
    (h1 : (X.Pj j).IsLatTup La.2) (h2 : (X.Pj (j + 1)).IsLatTup L') (h3 : ∀ v, i0 v ≤ X.G.P.r)
    (h4 : ∀ v' : Fin (X.Pj (j + 1)).nV, (i0 (X.vB (j + 1) v') = 0 ∧ L'' v' = L' v') ∨
      (1 ≤ i0 (X.vB (j + 1) v') ∧ IsEdge p ((X.Pj (j + 1)).n' v') (i0 (X.vB (j + 1) v')) ⟨L'' v', L' v'⟩)) :
    ∃ φ : Frm X j La (c', L''), ∀ (f : MvPowerSeries (X.ZA j) Kc) (gg : ℝ),
      (∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ), geX p Oc (coeff n (applyD (X.PI j I i0) f)) gg) →
      ∀ G ∈ (X.Pj j).HtupW La.2,
        ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) •
          (((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
            (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) L''))⁻¹) •
              delF X Kc j G (linSub (bc Kc φ) f))) ∈
        AddSubgroup.closure {y' | ∃ a : Kc, geX p Oc a gg ∧ ∃ z ∈ (X.Pj (j + 1)).HtupW L',
          y' = a • map (algebraMap X.G.Kf Kc) z} := by
  classical
  have cz : CharZero X.G.Kf := (algebraMap X.G.Kf Kc).charZero
  obtain ⟨g', h', hg', hh', hmF⟩ := hE p X j L' L'' i0 h2 h4
  obtain ⟨φ0⟩ := exists_frm X j La (c', L') h1 h2
  let φ : Frm X j La (c', L'') := ⟨φ0.g, g', φ0.hg, hg'⟩
  refine ⟨φ, fun f gg hf G hG => ?_⟩
  set ft := linSub (bc Kc φ) f with hft
  set S1 : X.G.Kf := ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
    ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
      (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) L''))⁻¹)) with hS1
  set s' : X.G.Kf := sX X (j + 1) (fun v => h' v) with hs'
  have hs'0 : s' ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => zpow_ne_zero _ (mF_det_ne X (j + 1) b (h' b.1))
  have hs'e : s' = ∏ b : BX X, (mF X (j + 1) b (g' b.1) * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)) :=
    Finset.prod_congr rfl fun b _ => by rw [hmF b]
  have hy1 := tgt_bidet (O := X.G.O) (Kc := Kc) (emX X (j + 1)) (hInj p X (j + 1)).1 (nuT X j) (nuT_antitone X hS j)
    (fun b => mF X (j + 1) b (h' b.1)) (fun b => mF X (j + 1) b ((h' b.1)⁻¹ : GL _ _)) (fun b => mF_inv_mul X (j + 1) b (h' b.1))
    (MG p Oc hval gg) (fun o a ha => geX_mul (hO o) ha) dual_bases_holds fock_product_holds reorder_holds (cX X j) (szT X j)
    (szT_le X j) (shape_szT X hS j) ((S1 * s'⁻¹) • delF X Kc j G ft)
    (by
      rw [← algebraMap_smul Kc (S1 * s'⁻¹)]
      exact Submodule.smul_mem _ _ (xSpan X Kc hS hBrS hInj hSp j La.2 φ0.g φ0.hg ft G hG))
    (fun I => by
      have := xPair X Kc hS hBrS hInj hMid hU Oc hval hO j La (c', L'') φ i0 h3 f gg hf G hG I
      rw [← hS1, ← hs'e] at this
      simp only [hmF]
      exact this)
  have htr : ∀ z ∈ AddSubgroup.closure {z | ∃ a ∈ MG p Oc hval gg,
      ∃ F : BX X → MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) X.G.Kf,
        (∀ b, F b ∈ deltaL X.G.O X.G.Kf (NJ X (j + 1)) (nuT X j b) (mF X (j + 1) b (h' b.1))) ∧
          z = a • map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b) (F b))},
      s' • z ∈ AddSubgroup.closure {y' | ∃ a : Kc, geX p Oc a gg ∧ ∃ z ∈ (X.Pj (j + 1)).HtupW L',
        y' = a • map (algebraMap X.G.Kf Kc) z} := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, F, hF, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨a, ha, s' • ∏ b, rename (emX X (j + 1) b) (F b), ?_, ?_⟩
      · refine hBrT p X (hinjX X) (j + 1) L' (fun v => h' v) (fun v => (Matrix.isUnit_iff_isUnit_det _).1 (h' v).isUnit) hh' F ?_
        intro b
        rw [(hS p X j b).2.1]
        exact hF b
      · rw [smul_comm, smul_eq_C_mul (a := s'), map_mul, map_C, ← smul_eq_C_mul, algebraMap_smul]
    | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
    | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx
  have := htr _ hy1
  rw [smul_smul, mul_comm s', mul_assoc, inv_mul_cancel₀ hs'0, mul_one, hS1, mul_smul] at this
  exact this

end Formalism.L2.PairingIndexBounds.Ent
end
end
