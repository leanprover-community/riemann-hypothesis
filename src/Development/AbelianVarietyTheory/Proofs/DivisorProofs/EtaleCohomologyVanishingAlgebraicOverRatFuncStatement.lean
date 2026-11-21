import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Scalars
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependentStatement
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DimensionSylow
import GroundTheory.TateCohomology.CohTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.COnePropertyFiniteExtension
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFieldEqGaloisCohomologyStatement

section
open IsLocalRing

open CategoryTheory Limits groupCohomology GroundTheory.GroupCoh IntermediateField

namespace GlobalTheory

theorem c_one_h2_units_subsingleton : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L], (∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0) → Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) := by
  intro K L _ _ _ _ _ hC
  classical
  let A := Rep.ofAlgebraAutOnUnits K L
  have h0 : ∀ (S : Subgroup (L ≃ₐ[K] L)) [Fintype S],
      IsZero (tateCohomology (Rep.res S.subtype A) 0) := by
    intro S _
    refine isZero_tateCohomology_zero_of_forall _ fun m hm => ?_
    let u : Lˣ := Additive.toMul m
    have hu : (u : L) ∈ fixedField S := fun s => congrArg Units.val (hm s)
    have hCF := GlobalTheory.T.c_one_property_finite_extension K (fixedField S) hC
    have hne : (⟨(u : L), hu⟩ : fixedField S) ≠ 0 := fun h => u.ne_zero (congrArg Subtype.val h)
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass (fixedField S) L hCF _ hne
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hx
      exact hne hx.symm
    let y : Rep.res S.subtype A := Additive.ofMul (Units.mk0 x hx0)
    refine ⟨y, ?_⟩
    have e1 : (Rep.res S.subtype A).ρ.norm y = ∑ s : S, (Rep.res S.subtype A).ρ s y := by
      first
        | rw [Representation.norm, LinearMap.coeFn_sum, Finset.sum_apply]
        | simp [Representation.norm]
    have e2 : (Additive.ofMul (∏ s : S, (s : L ≃ₐ[K] L) • Units.mk0 x hx0) : Additive Lˣ) =
        ∑ s : S, (Rep.res S.subtype A).ρ s y := ofMul_prod _ _
    rw [e1, ← e2]
    change Additive.ofMul _ = Additive.ofMul u
    congr 1
    apply Units.ext
    rw [Units.coe_prod]
    have h := Algebra.norm_eq_prod_automorphisms (fixedField S) x
    rw [hx] at h
    refine Eq.trans ?_ h.symm
    exact Fintype.prod_equiv (subgroupEquivAlgEquiv S).toEquiv _ _ (fun s => rfl)
  have h1 : ∀ (S : Subgroup (L ≃ₐ[K] L)) [Fintype S],
      IsZero (tateCohomology (Rep.res S.subtype A) (0 + 1)) := by
    intro S _
    have hz : ∀ z : groupCohomology (Rep.res S.subtype A) 1, z = 0 := fun z =>
      H1_induction_on z fun f => by
        rw [H1π_eq_zero_iff]
        have hf := (mem_cocycles₁_iff (A := Rep.res S.subtype A) f).1 f.2
        let e := subgroupEquivAlgEquiv S
        let g : Gal(L/fixedField S) → Lˣ := fun σ => Additive.toMul (f (e.symm σ))
        have hg : IsMulCocycle₁ g := by
          intro σ τ
          obtain ⟨s, rfl⟩ := e.surjective σ
          obtain ⟨t, rfl⟩ := e.surjective τ
          have h := congrArg (Additive.toMul (α := Lˣ)) (hf s t)
          simp only [g, ← map_mul, MulEquiv.symm_apply_apply]
          exact h
        obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units g hg
        refine ⟨Additive.ofMul β, funext fun s => ?_⟩
        have h := congrArg (Additive.ofMul (α := Lˣ)) (hβ (e s))
        rw [show g (e s) = Additive.toMul (f s) by simp only [g, MulEquiv.symm_apply_apply]; rfl] at h
        exact h
    have hs : Subsingleton (groupCohomology (Rep.res S.subtype A) 1) :=
      ⟨fun a b => by rw [hz a, hz b]⟩
    have e : (0 + 1 : ℤ) = ((1 : ℕ) : ℤ) := by norm_num
    rw [e]
    exact (ModuleCat.isZero_of_subsingleton (groupCohomology (Rep.res S.subtype A) 1)).of_iso ((TateCohomology.isoGroupCohomology 1).app _)
  have hCT : CohTrivial A := cohTrivial_of_forall_subgroup A 0 fun S _ => ⟨h0 S, h1 S⟩
  have h2 : IsZero (tateCohomology A ((2 : ℕ) : ℤ)) :=
    isZero_tateCohomology_of_index A _ fun p hp _ =>
      ⟨⊤, by simpa [Subgroup.index_top] using hp.one_lt.ne', fun {_} => hCT ⊤ _⟩
  have h2' : IsZero (groupCohomology A 2) :=
    h2.of_iso ((TateCohomology.isoGroupCohomology 2).app A).symm
  exact (ModuleCat.isZero_iff_subsingleton).1 h2'

end GlobalTheory
end

section
open IsLocalRing

namespace GlobalTheory

theorem span_range_X_eq_ker_constantCoeff (k : Type) [Field k] (n : ℕ) :
    Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))
      = RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have key : ∀ q : MvPolynomial (Fin n) k, q - MvPolynomial.C (MvPolynomial.constantCoeff q) ∈
        Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k))) := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq =>
        have := Ideal.add_mem _ hp hq
        convert this using 1
        simp only [map_add]; ring
      | mul_X p i _ =>
        simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    simpa [hp] using key p

theorem le_height_span_range_X_mvPolynomial : ∀ (k : Type) [Field k] (n : ℕ), ((n : ℕ∞)) ≤ (Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))).height := by
  intro k _ n
  rw [span_range_X_eq_ker_constantCoeff]
  haveI : (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨MvPolynomial.C a, by simp⟩)
  have h := ReciprocityTheory.CA.height_maximal_mvPolynomial_field k n (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k))
  exact h.2.ge

end GlobalTheory
end

section
section
open IsLocalRing

namespace GlobalTheory

theorem exists_ne_zero_common_zero_of_isHomogeneous :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (f : Fin r → MvPolynomial (Fin n) k),
      (∀ i, ∃ d, 0 < d ∧ (f i).IsHomogeneous d) → r < n →
        ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  intro k _ _ n r f hf hrn
  by_contra hcon
  push Not at hcon
  set I : Ideal (MvPolynomial (Fin n) k) := Ideal.span (Set.range f) with hIdef
  set M : Ideal (MvPolynomial (Fin n) k) :=
    MvPolynomial.vanishingIdeal k ({(0 : Fin n → k)} : Set (Fin n → k)) with hMdef
  have hMmax : M.IsMaximal := inferInstance

  have hf0 : ∀ i, MvPolynomial.eval (0 : Fin n → k) (f i) = 0 := by
    intro i
    obtain ⟨d, hd, hh⟩ := hf i
    rw [MvPolynomial.eval_zero]
    rw [MvPolynomial.constantCoeff_eq]
    apply hh.coeff_eq_zero
    simp
    omega
  have hIM : I ≤ M := by
    rw [hIdef, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, hMdef, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hf0 i

  have hZ : MvPolynomial.zeroLocus k I ⊆ ({(0 : Fin n → k)} : Set (Fin n → k)) := by
    intro x hx
    by_contra hx0
    obtain ⟨i, hi⟩ := hcon x hx0
    apply hi
    have := hx (f i) (Ideal.subset_span ⟨i, rfl⟩)
    exact this
  have hMrad : M ≤ I.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I]
    exact MvPolynomial.vanishingIdeal_anti_mono hZ
  have hXM : Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))
      ≤ M := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, hMdef, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  have hItop : I ≠ ⊤ := fun h => hMmax.ne_top (top_le_iff.mp (h ▸ hIM))
  have hrad : I.radical.height = I.height := by
    rw [Ideal.height_eq_inf_minimalPrimes, Ideal.height_eq_inf_minimalPrimes,
      Ideal.radical_minimalPrimes]
  have hfin : (I.spanFinrank : ℕ∞) ≤ r := by
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := MvPolynomial (Fin n) k)
      (Set.finite_range f)
    have h2 : (Set.range f).ncard ≤ r := by
      rw [← Set.image_univ]
      refine (Set.ncard_image_le Set.finite_univ).trans ?_
      simp [Set.ncard_univ]
    exact_mod_cast h1.trans h2
  have key : (n : ℕ∞) ≤ r :=
    (GlobalTheory.le_height_span_range_X_mvPolynomial k n).trans <| (Ideal.height_mono hXM).trans <| (Ideal.height_mono hMrad).trans <|
      hrad.le.trans <| (Ideal.height_le_spanFinrank I hItop).trans hfin
  have : n ≤ r := by exact_mod_cast key
  omega

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_common_zero_of_isHomogeneous' : ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (f : Fin r → MvPolynomial (Fin n) k), (∀ i, ∃ d, 0 < d ∧ (f i).IsHomogeneous d) → r < n → ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  atlas_forward_decl GlobalTheory.exists_ne_zero_common_zero_of_isHomogeneous
end

section
open IsLocalRing

namespace GlobalTheory
namespace TsenCount

open Polynomial

variable {σ k : Type} [CommRing k]

def CoeffHom (e : ℕ) (p : (MvPolynomial σ k)[X]) : Prop := ∀ j, (p.coeff j).IsHomogeneous e

theorem CoeffHom.mul {a b : ℕ} {p q : (MvPolynomial σ k)[X]} (hp : CoeffHom a p)
    (hq : CoeffHom b q) : CoeffHom (a + b) (p * q) := fun j => by
  rw [coeff_mul]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun c _ => (hp _).mul (hq _)

theorem coeffHom_map (g : k[X]) :
    CoeffHom 0 (g.map (MvPolynomial.C : k →+* MvPolynomial σ k)) := fun j => by
  rw [coeff_map]
  exact MvPolynomial.isHomogeneous_C _ _

theorem coeffHom_one : CoeffHom 0 (1 : (MvPolynomial σ k)[X]) := by
  simpa using coeffHom_map (σ := σ) (1 : k[X])

theorem CoeffHom.pow {p : (MvPolynomial σ k)[X]} (hp : CoeffHom 1 p) (m : ℕ) :
    CoeffHom m (p ^ m) := by
  induction m with
  | zero => simpa using coeffHom_one
  | succ m ih => rw [pow_succ]; exact ih.mul hp

theorem CoeffHom.prod {ι : Type} (s : Finset ι) (e : ι → ℕ) (p : ι → (MvPolynomial σ k)[X])
    (h : ∀ i, CoeffHom (e i) (p i)) : CoeffHom (∑ i ∈ s, e i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coeffHom_one
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha]; exact (h a).mul ih

theorem CoeffHom.sum {ι : Type} (s : Finset ι) (e : ℕ) (p : ι → (MvPolynomial σ k)[X])
    (h : ∀ i ∈ s, CoeffHom e (p i)) : CoeffHom e (∑ i ∈ s, p i) := fun j => by
  rw [finsetSum_coeff]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => h i hi j

theorem sum_eq_of_mem_support {n d : ℕ} {R : Type} [CommRing R] {f : MvPolynomial (Fin n) R}
    (hf : f.IsHomogeneous d) {s : Fin n →₀ ℕ} (hs : s ∈ f.support) : ∑ i, s i = d := by
  have h := hf (MvPolynomial.mem_support_iff.1 hs)
  rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp

theorem coeffHom_eval₂ {n d : ℕ} {f : MvPolynomial (Fin n) k[X]} (hf : f.IsHomogeneous d)
    (y : Fin n → (MvPolynomial σ k)[X]) (hy : ∀ i, CoeffHom 1 (y i)) :
    CoeffHom d (MvPolynomial.eval₂ (mapRingHom (MvPolynomial.C : k →+* MvPolynomial σ k)) y f) := by
  rw [MvPolynomial.eval₂_eq']
  refine CoeffHom.sum _ _ _ fun s hs => ?_
  have h := (coeffHom_map (σ := σ) (MvPolynomial.coeff s f)).mul
    (CoeffHom.prod Finset.univ (fun i => s i) (fun i => y i ^ s i) fun i => (hy i).pow _)
  rwa [zero_add, sum_eq_of_mem_support hf hs] at h

theorem natDegree_eval_le {n d N D : ℕ} {f : MvPolynomial (Fin n) k[X]} (hf : f.IsHomogeneous d)
    (hD : ∀ s ∈ f.support, (MvPolynomial.coeff s f).natDegree ≤ D)
    (x : Fin n → k[X]) (hx : ∀ i, (x i).natDegree ≤ N) :
    (MvPolynomial.eval x f).natDegree ≤ D + d * N := by
  rw [MvPolynomial.eval_eq']
  refine natDegree_sum_le_of_forall_le _ _ fun s hs => natDegree_mul_le.trans ?_
  refine add_le_add (hD s hs) ((natDegree_prod_le _ _).trans ?_)
  rw [← sum_eq_of_mem_support hf hs, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hx i))

end TsenCount

open Polynomial TsenCount in

theorem exists_nonzero_zero_polynomial_of_isAlgClosed (k : Type) [Field k] [IsAlgClosed k] (n d : ℕ)
    (f : MvPolynomial (Fin n) (Polynomial k)) (hf : f.IsHomogeneous d) (hd : 0 < d) (hn : d < n) :
    ∃ x : Fin n → Polynomial k, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  classical
  obtain ⟨D, hD⟩ : ∃ D, ∀ s ∈ f.support, (MvPolynomial.coeff s f).natDegree ≤ D :=
    ⟨f.support.sup fun s => (MvPolynomial.coeff s f).natDegree, fun s hs =>
      Finset.le_sup (f := fun s => (MvPolynomial.coeff s f).natDegree) hs⟩
  let y : Fin n → (MvPolynomial (Fin (n * (D + 1))) k)[X] := fun i =>
    ∑ m : Fin (D + 1), monomial (m : ℕ) (MvPolynomial.X (finProdFinEquiv (i, m)))
  have hy : ∀ i, CoeffHom 1 (y i) := fun i => CoeffHom.sum _ _ _ fun m _ j => by
    rw [coeff_monomial]
    split_ifs
    · exact MvPolynomial.isHomogeneous_X _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  have hP := coeffHom_eval₂ hf y hy
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.exists_ne_zero_common_zero_of_isHomogeneous' k (n * (D + 1)) (D + d * D + 1)
    (fun j => (MvPolynomial.eval₂ (mapRingHom MvPolynomial.C) y f).coeff j)
    (fun j => ⟨d, hd, hP j⟩) (by nlinarith)
  let x : Fin n → k[X] := fun i => (y i).map (MvPolynomial.eval c)
  have hx : ∀ i, x i = ∑ m : Fin (D + 1), monomial (m : ℕ) (c (finProdFinEquiv (i, m))) := fun i => by
    simp [x, y, Polynomial.map_sum]
  have hdeg : ∀ i, (x i).natDegree ≤ D := fun i => by
    rw [hx]
    exact natDegree_sum_le_of_forall_le _ _ fun m _ =>
      (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 m.2)
  have hev : MvPolynomial.eval x f =
      (MvPolynomial.eval₂ (mapRingHom MvPolynomial.C) y f).map (MvPolynomial.eval c) := by
    rw [← coe_mapRingHom, MvPolynomial.eval₂_comp_left, mapRingHom_comp]
    have : (MvPolynomial.eval c).comp (MvPolynomial.C : k →+* MvPolynomial (Fin (n * (D + 1))) k)
        = RingHom.id k := by ext; simp
    rw [this, mapRingHom_id]
    rfl
  refine ⟨x, fun h0 => hc0 ?_, ?_⟩
  · funext a
    obtain ⟨⟨i, m⟩, rfl⟩ := finProdFinEquiv.surjective a
    have h1 : (x i).coeff m = 0 := by rw [h0]; simp
    rw [hx, finsetSum_coeff, Finset.sum_eq_single m] at h1
    · simpa using h1
    · intro b _ hb
      rw [coeff_monomial, if_neg fun h => hb (Fin.ext h)]
    · simp
  · ext j
    rw [coeff_zero]
    by_cases hj : j < D + d * D + 1
    · rw [hev, coeff_map]
      exact hc ⟨j, hj⟩
    · exact coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_eval_le hf hD x hdeg) (by omega))

end GlobalTheory
end

section
open Polynomial

namespace GlobalTheory

open Polynomial in
private theorem isHomogeneous_of_map_of_injective {R S : Type} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) {n d : ℕ} {p : MvPolynomial (Fin n) R}
    (hp : (MvPolynomial.map φ p).IsHomogeneous d) : p.IsHomogeneous d := by
  intro ν hν
  apply hp
  rw [MvPolynomial.coeff_map]
  intro h
  exact hν (hφ (h.trans (map_zero φ).symm))

open Polynomial in
private theorem mvPolynomial_eval_map_comp {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (x : Fin n → R) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.eval (φ ∘ x) (MvPolynomial.map φ p) = φ (MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

open Polynomial in
private theorem exists_ne_zero_homogeneous_zero_of_forall_subfield {F K : Type} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K]
    (hF : ∀ (n d : ℕ) (f : MvPolynomial (Fin n) F), f.IsHomogeneous d → 0 < d → d < n →
      ∃ x : Fin n → F, x ≠ 0 ∧ MvPolynomial.eval x f = 0)
    (n d : ℕ) (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) (hd : 0 < d) (hdn : d < n) :
    ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  classical
  set E := IntermediateField.adjoin F (f.coeffs : Set K) with hE
  haveI : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  obtain ⟨fE, hfE⟩ : f ∈ Set.range (MvPolynomial.map (algebraMap E K)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    exact ⟨⟨a, IntermediateField.subset_adjoin F _ ha⟩, rfl⟩
  have hfEh : fE.IsHomogeneous d :=
    isHomogeneous_of_map_of_injective (algebraMap E K).injective (hfE ▸ hf)
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.c_one_of_finite_extension F E hF n d fE hfEh hd hdn
  refine ⟨algebraMap E K ∘ x, ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    exact (algebraMap E K).injective (by simpa using congrFun h i)
  · rw [← hfE, mvPolynomial_eval_map_comp, hx, map_zero]

open Polynomial in
variable {σ k : Type} [CommRing k] in
private theorem coeffHom_sum {ι : Type} (s : Finset ι) {e : ℕ} (p : ι → (MvPolynomial σ k)[X])
    (hp : ∀ i ∈ s, _root_.GlobalTheory.TsenCount.CoeffHom e (p i)) :
    _root_.GlobalTheory.TsenCount.CoeffHom e (∑ i ∈ s, p i) := fun j => by
  rw [Polynomial.finset_sum_coeff]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => hp i hi j

open Polynomial in
variable {σ k : Type} [CommRing k] in
private theorem coeffHom_mul {e e' : ℕ} {p q : (MvPolynomial σ k)[X]}
    (hp : _root_.GlobalTheory.TsenCount.CoeffHom e p) (hq : _root_.GlobalTheory.TsenCount.CoeffHom e' q) :
    _root_.GlobalTheory.TsenCount.CoeffHom (e + e') (p * q) := fun j => by
  rw [Polynomial.coeff_mul]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun x _ => (hp x.1).mul (hq x.2)

open Polynomial in
variable {σ k : Type} [CommRing k] in
private theorem coeffHom_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (e : ι → ℕ)
    (p : ι → (MvPolynomial σ k)[X]) (hp : ∀ i ∈ s, _root_.GlobalTheory.TsenCount.CoeffHom (e i) (p i)) :
    _root_.GlobalTheory.TsenCount.CoeffHom (∑ i ∈ s, e i) (∏ i ∈ s, p i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro j
    rw [Finset.prod_empty, Finset.sum_empty, Polynomial.coeff_one]
    split_ifs
    · exact MvPolynomial.isHomogeneous_one _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact coeffHom_mul (hp a (Finset.mem_insert_self a s))
      (ih fun i hi => hp i (Finset.mem_insert_of_mem hi))

open Polynomial in
variable {σ k : Type} [CommRing k] in
private theorem coeffHom_pow {e : ℕ} {p : (MvPolynomial σ k)[X]}
    (hp : _root_.GlobalTheory.TsenCount.CoeffHom e p) (m : ℕ) :
    _root_.GlobalTheory.TsenCount.CoeffHom (m * e) (p ^ m) := by
  have := coeffHom_prod (Finset.range m) (fun _ => e) (fun _ => p) (fun _ _ => hp)
  simpa using this

private theorem exists_ne_zero_common_zero_of_lt {k : Type} [Field k] [IsAlgClosed k] {m r : ℕ}
    (g : Fin r → MvPolynomial (Fin m) k) (hg : ∀ i, MvPolynomial.eval 0 (g i) = 0) (hr : r < m) :
    ∃ x : Fin m → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (g i) = 0 := by
  classical
  have hM0 : (MvPolynomial.vanishingIdeal k {(0 : Fin m → k)}).IsMaximal :=
    MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.2 ⟨0, rfl⟩
  have hIM : Ideal.span (Set.range g) ≤ MvPolynomial.vanishingIdeal k {(0 : Fin m → k)} := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_eq_eval]
    exact hg i
  obtain ⟨Q, hQmin, hQM⟩ := Ideal.exists_minimalPrimes_le hIM
  have hQprime : Q.IsPrime := hQmin.1.1
  have hht : Q.height ≤ r := by
    refine (Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ Q hQmin).trans ?_
    have h1 := Submodule.spanRank_span_le_card (R := MvPolynomial (Fin m) k) (Set.range g)
    have h2 : Cardinal.mk (Set.range g) ≤ r := by
      simpa using Cardinal.mk_range_le (f := g)
    calc Cardinal.toENat (Submodule.spanRank (Ideal.span (Set.range g)))
        ≤ Cardinal.toENat (r : Cardinal) := Cardinal.toENat.monotone' (h1.trans h2)
      _ = r := by simp
  have hQne : Q ≠ MvPolynomial.vanishingIdeal k {(0 : Fin m → k)} := by
    intro hQ
    have hm := (_root_.ReciprocityTheory.CA.height_maximal_mvPolynomial_field k m (MvPolynomial.vanishingIdeal k {(0 : Fin m → k)})).2
    have hm' : Q.height = m := hQ ▸ hm
    rw [hm'] at hht
    have : m ≤ r := by exact_mod_cast hht
    omega
  have hex : ∃ J : Ideal (MvPolynomial (Fin m) k), J.IsMaximal ∧ Q ≤ J ∧
      J ≠ MvPolynomial.vanishingIdeal k {(0 : Fin m → k)} := by
    by_contra hcon
    push_neg at hcon
    have hjac : Q.jacobson = Q := isJacobsonRing_iff_prime_eq.1 inferInstance Q hQprime
    have hle : MvPolynomial.vanishingIdeal k {(0 : Fin m → k)} ≤ Q.jacobson := by
      rw [Ideal.jacobson]
      refine le_sInf ?_
      rintro J ⟨hQJ, hJ⟩
      rw [hcon J hJ hQJ]
    exact hQne (le_antisymm hQM (hjac ▸ hle))
  obtain ⟨J, hJ, hQJ, hJne⟩ := hex
  obtain ⟨x, rfl⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hJ
  refine ⟨x, ?_, fun i => ?_⟩
  · rintro rfl
    exact hJne rfl
  · have hx : g i ∈ MvPolynomial.vanishingIdeal k {x} :=
      hQJ (hQmin.1.2 (Ideal.subset_span ⟨i, rfl⟩))
    rwa [MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_eq_eval] at hx

open Polynomial in
private theorem exists_ne_zero_polynomial_zero_of_homogeneous {k : Type} [Field k] [IsAlgClosed k] {n d : ℕ}
    (F : MvPolynomial (Fin n) k[X]) (hF : F.IsHomogeneous d) (hd : 0 < d) (hdn : d < n) :
    ∃ x : Fin n → k[X], x ≠ 0 ∧ MvPolynomial.eval x F = 0 := by
  classical
  set D := F.support.sup fun ν => (F.coeff ν).natDegree with hD
  have hDle : ∀ ν, (F.coeff ν).natDegree ≤ D := by
    intro ν
    by_cases hν : ν ∈ F.support
    · exact Finset.le_sup (f := fun ν => (F.coeff ν).natDegree) hν
    · rw [MvPolynomial.notMem_support_iff.1 hν]
      simp
  set s := D
  set m := n * (s + 1)
  set e : Fin n × Fin (s + 1) ≃ Fin m := finProdFinEquiv
  let y : Fin n → (MvPolynomial (Fin m) k)[X] := fun i =>
    ∑ j : Fin (s + 1), Polynomial.C (MvPolynomial.X (e (i, j))) * Polynomial.X ^ (j : ℕ)
  let Φ : (MvPolynomial (Fin m) k)[X] :=
    MvPolynomial.eval₂ (Polynomial.mapRingHom (MvPolynomial.C)) y F
  have hy : ∀ i, _root_.GlobalTheory.TsenCount.CoeffHom 1 (y i) := by
    intro i
    refine coeffHom_sum _ _ fun j _ => ?_
    intro l
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs
    · exact MvPolynomial.isHomogeneous_X _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  have hyd : ∀ i, (y i).natDegree ≤ s := by
    intro i
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 j.2)
  have hΦ : _root_.GlobalTheory.TsenCount.CoeffHom d Φ := by
    simp only [Φ, MvPolynomial.eval₂_eq']
    refine coeffHom_sum _ _ fun ν hν => ?_
    have hdeg : ∑ i, ν i = d := by
      have := hF (MvPolynomial.mem_support_iff.1 hν)
      rw [← this]
      simp [Finsupp.weight_apply, Finsupp.sum_fintype]
    have h1 : _root_.GlobalTheory.TsenCount.CoeffHom 0
        ((Polynomial.mapRingHom (MvPolynomial.C (σ := Fin m))) (F.coeff ν)) := by
      intro l
      rw [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
      exact MvPolynomial.isHomogeneous_C _ _
    have h2 := coeffHom_prod Finset.univ (fun i => ν i * 1) (fun i => y i ^ ν i)
      (fun i _ => coeffHom_pow (hy i) (ν i))
    have h3 := coeffHom_mul h1 h2
    simpa [hdeg] using h3
  have hΦdeg : Φ.natDegree ≤ D + d * s := by
    simp only [Φ, MvPolynomial.eval₂_eq']
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun ν hν => ?_
    have hdeg : ∑ i, ν i = d := by
      have := hF (MvPolynomial.mem_support_iff.1 hν)
      rw [← this]
      simp [Finsupp.weight_apply, Finsupp.sum_fintype]
    refine (Polynomial.natDegree_mul_le).trans (add_le_add ?_ ?_)
    · exact (Polynomial.natDegree_map_le).trans (hDle ν)
    · refine (Polynomial.natDegree_prod_le _ _).trans ?_
      calc ∑ i, (y i ^ ν i).natDegree ≤ ∑ i, ν i * s :=
            Finset.sum_le_sum fun i _ => (Polynomial.natDegree_pow_le).trans
              (Nat.mul_le_mul_left _ (hyd i))
        _ = d * s := by rw [← Finset.sum_mul, hdeg]
  set r := D + d * s + 1
  have hrm : r < m := by
    simp only [r, m, s]
    nlinarith
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_common_zero_of_lt (k := k) (m := m) (r := r)
    (fun j => Φ.coeff j) (fun j => by
      rw [MvPolynomial.eval_zero]
      exact (hΦ j).coeff_eq_zero (by simp; omega)) hrm
  let x : Fin n → k[X] := fun i =>
    ∑ j : Fin (s + 1), Polynomial.C (a (e (i, j))) * Polynomial.X ^ (j : ℕ)
  have hmapΦ : Polynomial.map (MvPolynomial.eval a) Φ = 0 := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hj : j < r
    · exact ha ⟨j, hj⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  have hΦx : Polynomial.map (MvPolynomial.eval a) Φ = MvPolynomial.eval x F := by
    have h1 := MvPolynomial.eval₂_comp_left (Polynomial.mapRingHom (MvPolynomial.eval a))
      (Polynomial.mapRingHom (MvPolynomial.C (σ := Fin m))) y F
    rw [Polynomial.coe_mapRingHom] at h1
    simp only [Φ]
    rw [h1]
    have h2 : (Polynomial.mapRingHom (MvPolynomial.eval a)).comp
        (Polynomial.mapRingHom (MvPolynomial.C (σ := Fin m))) = RingHom.id k[X] := by
      refine RingHom.ext fun p => ?_
      have hc : (MvPolynomial.eval a).comp (MvPolynomial.C (σ := Fin m)) = RingHom.id k := by
        ext c
        simp
      rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_mapRingHom, Polynomial.map_map, hc,
        Polynomial.map_id, RingHom.id_apply]
    have h3 : Polynomial.map (MvPolynomial.eval a) ∘ y = x := by
      funext i
      simp [y, x, Polynomial.map_sum]
    rw [h2, h3]
    rfl
  refine ⟨x, ?_, hΦx ▸ hmapΦ⟩
  obtain ⟨t, ht⟩ : ∃ t, a t ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact ha0 (funext hcon)
  obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective t
  intro hx
  have hxi : (x i).coeff j = 0 := by
    rw [congrFun hx i]
    simp
  have hc : (x i).coeff j = a (e (i, j)) := by
    simp only [x, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext h.symm)
    · simp
  exact ht (hc.symm.trans hxi)

open Polynomial in
private theorem exists_ne_zero_ratFunc_homogeneous_zero {k : Type} [Field k] [IsAlgClosed k] (n d : ℕ)
    (f : MvPolynomial (Fin n) (RatFunc k)) (hf : f.IsHomogeneous d) (hd : 0 < d) (hdn : d < n) :
    ∃ x : Fin n → RatFunc k, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors k[X]) f.coeffs
  have hc0 : algebraMap k[X] (RatFunc k) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  obtain ⟨F, hF⟩ : MvPolynomial.C (algebraMap k[X] (RatFunc k) b) * f ∈
      Set.range (MvPolynomial.map (algebraMap k[X] (RatFunc k))) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨ν, hν, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 ha
    rw [MvPolynomial.coeff_C_mul]
    have hν' : f.coeff ν ∈ f.coeffs := by
      refine MvPolynomial.coeff_mem_coeffs ν ?_
      intro h
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, h, mul_zero] at hν
      exact hν rfl
    obtain ⟨p, hp⟩ := hb _ hν'
    exact ⟨p, hp.trans (Algebra.smul_def _ _)⟩
  have hFh : F.IsHomogeneous d := by
    refine isHomogeneous_of_map_of_injective (IsFractionRing.injective k[X] (RatFunc k)) ?_
    rw [hF]
    simpa using (MvPolynomial.isHomogeneous_C (Fin n) (algebraMap k[X] (RatFunc k) b)).mul hf
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_polynomial_zero_of_homogeneous F hFh hd hdn
  refine ⟨algebraMap k[X] (RatFunc k) ∘ x, ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    exact IsFractionRing.injective k[X] (RatFunc k) (by simpa using congrFun h i)
  · have key := mvPolynomial_eval_map_comp (algebraMap k[X] (RatFunc k)) x F
    rw [hF, hx, map_zero] at key
    simp only [map_mul, MvPolynomial.eval_C] at key
    exact (mul_eq_zero.1 key).resolve_left hc0

open Polynomial in

theorem _root_.GlobalTheory.tsen_algebraic_extension_ratFunc :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K]
      [Algebra.IsAlgebraic (RatFunc k) K] (n d : ℕ) (f : MvPolynomial (Fin n) K),
      f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  intro k K _ _ _ _ _ n d f hf hd hdn
  exact exists_ne_zero_homogeneous_zero_of_forall_subfield (F := RatFunc k)
    (fun n d f hf hd hdn => exists_ne_zero_ratFunc_homogeneous_zero (k := k) n d f hf hd hdn) n d f hf hd hdn

end GlobalTheory
end

section
set_option maxSynthPendingDepth 1

open CategoryTheory IntermediateField GroundTheory.ProfCoh

namespace GlobalTheory.TsenCD

theorem subsingleton_brauer (k E Ω : Type) [Field k] [IsAlgClosed k] [Field E] [Algebra (RatFunc k) E]
    [Algebra.IsAlgebraic (RatFunc k) E] [Field Ω] [Algebra E Ω] [IsGalois E Ω] :
    Subsingleton (cohomology (galUnits.{0} E Ω) 2) := by
  suffices h : ∀ x : cohomology (galUnits.{0} E Ω) 2, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨F, z, rfl⟩ := exists_unitsInflation_eq 2 x
  have hC := GlobalTheory.tsen_algebraic_extension_ratFunc k E
  have h1 : Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits E F.toIntermediateField) 2) :=
    GlobalTheory.c_one_h2_units_subsingleton E F.toIntermediateField hC
  have h2 : Subsingleton (groupCohomology (galUnitsZ E F.toIntermediateField) 2) := h1
  have h3 : Subsingleton (groupCohomology (galUnits.{0} E F.toIntermediateField) 2) :=
    (h2GalUnitsAddEquiv E F.toIntermediateField).injective.subsingleton
  rw [Subsingleton.elim z 0, map_zero]

theorem cdp_le_one_of_ne_char (k K Ω : Type) [Field k] [IsAlgClosed k] [Field K]
    [Algebra (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (p : ℕ) (hp : p.Prime) (hpK : (p : K) ≠ 0) :
    cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity K Ω hp hpK
  have h := cdp_le_of_forall_openSubgroup hp (galRootsOfUnity.{0} K Ω p) e 1 (fun U => by
    let E := fixedField (U : Subgroup (Ω ≃ₐ[K] Ω))
    letI : Algebra (RatFunc k) E := ((algebraMap K E).comp (algebraMap (RatFunc k) K)).toAlgebra
    haveI : IsScalarTower (RatFunc k) K E := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.IsAlgebraic K E := inferInstance
    haveI : Algebra.IsAlgebraic (RatFunc k) E := Algebra.IsAlgebraic.trans (RatFunc k) K E
    haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    have hB : Subsingleton (cohomology (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype
        (galUnits.{0} K Ω)) 2) := by
      have := subsingleton_brauer k E Ω
      exact (openCohomologyIso U 2).toLinearEquiv.toEquiv.subsingleton
    have h1 : Subsingleton (cohomology (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype
        (galUnits.{0} K Ω)) 1) := ModuleCat.subsingleton_of_isZero (isZero_H1_open K Ω U)
    have hS := kummerSequenceRes_shortExact (Ksep := Ω) p (U : Subgroup (Ω ≃ₐ[K] Ω)) hpK
    haveI : Subsingleton (cohomology (kummerSequenceRes (K := K) (Ksep := Ω) p
        (U : Subgroup (Ω ≃ₐ[K] Ω))).X₂ (1 + 1)) := hB
    exact (cohomologyMap_f_injective_of_subsingleton hS 1 h1).subsingleton)
  exact_mod_cast h

section ArtinSchreier

attribute [local instance 2000] Rep.hV2

open Polynomial

theorem exists_zmod_cast_eq_of_pow_sub_self {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [CharP Ω p]
    (y : Ω) (hy : y ^ p - y = 0) : ∃ a : ZMod p, ZMod.castHom (dvd_refl p) Ω a = y := by
  classical
  by_contra hne
  push_neg at hne
  set f := ZMod.castHom (dvd_refl p) Ω
  set P : Polynomial Ω := X ^ p - X
  have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero Ω hp.out.one_lt
  have hroot : ∀ z : Ω, z ^ p - z = 0 → z ∈ P.roots.toFinset := fun z hz => by
    rw [Multiset.mem_toFinset, mem_roots hP]
    simp [P, hz]
  have hT : insert y (Finset.univ.image f) ⊆ P.roots.toFinset := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hroot _ hy
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hz
      apply hroot
      rw [← map_pow, ZMod.pow_card, sub_self]
  have hy' : y ∉ Finset.univ.image f := fun h => by
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
    exact hne a ha
  have hcard : (insert y (Finset.univ.image f)).card = p + 1 := by
    rw [Finset.card_insert_of_notMem hy', Finset.card_image_of_injective _ f.injective,
      Finset.card_univ, ZMod.card]
  have h1 := Finset.card_le_card hT
  have h2 : P.roots.toFinset.card ≤ p :=
    (Multiset.toFinset_card_le _).trans ((card_roots' P).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq Ω hp.out.one_lt).le)
  omega

theorem exists_pow_sub_self_eq {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [CharP Ω p]
    [IsSepClosed Ω] (a : Ω) : ∃ x : Ω, x ^ p - x = a := by
  have hd : derivative (X ^ p - X - C a : Polynomial Ω) = -1 := by
    simp [derivative_X_pow, CharP.cast_eq_zero]
  have hsep : (X ^ p - X - C a : Polynomial Ω).Separable := by
    rw [separable_def, hd]
    exact isCoprime_one_right.neg_right
  have hdeg : (X ^ p - X - C a : Polynomial Ω).degree ≠ 0 := fun h => by
    have h' := congrArg derivative (eq_C_of_degree_eq_zero h)
    rw [hd, derivative_C] at h'
    exact one_ne_zero (neg_eq_zero.1 h')
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root _ hdeg hsep
  refine ⟨x, ?_⟩
  have := hx.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at this
  exact sub_eq_zero.1 this

end ArtinSchreier

section Sequence

attribute [local instance 2000] Rep.hV2

variable (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] [IsGalois E Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p]

noncomputable def primeFieldToGalAdd :
    Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p)) ⟶ galAddInt.{0} E Ω :=
  Rep.ofHom ⟨uliftIntLinearMap ((ZMod.castHom (dvd_refl p) Ω).toAddMonoidHom.comp
      (AddEquiv.ulift : ULift.{0} (ZMod p) ≃+ ZMod p).toAddMonoidHom), fun σ =>
    LinearMap.ext fun x => by
      change ZMod.castHom (dvd_refl p) Ω x.down = σ (ZMod.castHom (dvd_refl p) Ω x.down)
      exact (congrArg (fun φ : ZMod p →+* Ω => φ x.down)
        (RingHom.ext_zmod ((σ : Ω →+* Ω).comp (ZMod.castHom (dvd_refl p) Ω))
          (ZMod.castHom (dvd_refl p) Ω))).symm⟩

noncomputable def artinSchreierMap : galAddInt.{0} E Ω ⟶ galAddInt.{0} E Ω :=
  Rep.ofHom ⟨uliftIntLinearMap ((frobenius Ω p).toAddMonoidHom - AddMonoidHom.id Ω), fun σ =>
    LinearMap.ext fun x => by
      change σ x ^ p - σ x = σ (x ^ p - x)
      rw [map_sub, map_pow]⟩

noncomputable def artinSchreierSequence : ShortComplex (Rep (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω)) :=
  ShortComplex.mk (primeFieldToGalAdd E Ω p) (artinSchreierMap E Ω p) (by
    ext x
    change (ZMod.castHom (dvd_refl p) Ω x.down) ^ p - ZMod.castHom (dvd_refl p) Ω x.down = 0
    rw [← map_pow, ZMod.pow_card, sub_self])

theorem artinSchreierSequence_shortExact [IsSepClosed Ω] :
    (artinSchreierSequence E Ω p).ShortExact where
  exact := shortComplex_exact_of_forall_exists _ fun y hy => by
    obtain ⟨a, ha⟩ := exists_zmod_cast_eq_of_pow_sub_self (p := p) (Ω := Ω) y hy
    exact ⟨ULift.up a, ha⟩
  mono_f := (Rep.mono_iff_injective _).2 fun x y h =>
    ULift.ext _ _ ((ZMod.castHom (dvd_refl p) Ω).injective h)
  epi_g := (Rep.epi_iff_surjective _).2 fun a => by
    obtain ⟨x, hx⟩ := exists_pow_sub_self_eq (p := p) (Ω := Ω) a
    exact ⟨x, hx⟩

instance isDiscreteRep_artinSchreierSequence_X₁ :
    IsDiscreteRep (artinSchreierSequence E Ω p).X₁ :=
  inferInstanceAs (IsDiscreteRep (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p))))

instance isDiscreteRep_artinSchreierSequence_X₂ :
    IsDiscreteRep (artinSchreierSequence E Ω p).X₂ :=
  inferInstanceAs (IsDiscreteRep (galAddInt.{0} E Ω))

instance isDiscreteRep_artinSchreierSequence_X₃ :
    IsDiscreteRep (artinSchreierSequence E Ω p).X₃ :=
  inferInstanceAs (IsDiscreteRep (galAddInt.{0} E Ω))

omit [Fact p.Prime] [CharP Ω p] in

theorem subsingleton_cohomology_galAddInt {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (cohomology (galAddInt.{0} E Ω) n) := by
  have := subsingleton_cohomology_galAdd (K := E) (L := Ω) hn
  exact (cohomologyAddEquivOfEquiv (A := galAddInt.{0} E Ω) (A' := galAdd E Ω) (AddEquiv.refl Ω)
    (fun _ _ => rfl) n).injective.subsingleton

theorem subsingleton_cohomology_two_trivial_zmod [IsSepClosed Ω] :
    Subsingleton (cohomology (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p))) 2) := by
  have hS := artinSchreierSequence_shortExact E Ω p
  have h1 : Subsingleton (cohomology (artinSchreierSequence E Ω p).X₃ 1) :=
    subsingleton_cohomology_galAddInt E Ω one_ne_zero
  haveI : Subsingleton (cohomology (artinSchreierSequence E Ω p).X₂ (1 + 1)) :=
    subsingleton_cohomology_galAddInt E Ω (n := 2) two_ne_zero
  exact (cohomologyMap_f_injective_of_subsingleton hS 1 h1).subsingleton

end Sequence

theorem cdp_le_one_of_char_eq (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (p : ℕ) (hp : p.Prime) (hpK : (p : K) = 0) : cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp).2 hpK
  haveI : CharP Ω p := charP_of_injective_algebraMap (algebraMap K Ω).injective p
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  have h := cdp_le_of_forall_openSubgroup hp
    (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[K] Ω) (ULift.{0} (ZMod p))) AddEquiv.ulift.symm 1 (fun U => by
      let E := fixedField (U : Subgroup (Ω ≃ₐ[K] Ω))
      haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
      have h2 := subsingleton_cohomology_two_trivial_zmod E Ω p
      haveI : IsDiscreteRep (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype
          (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[K] Ω) (ULift.{0} (ZMod p)))) :=
        isDiscreteRep_res_subtype _ _
      let f : Rep.res (galFixedFieldEquivOpen U).toMonoidHom
          (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype
            (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[K] Ω) (ULift.{0} (ZMod p)))) ⟶
          Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p)) :=
        Rep.ofHom ⟨LinearMap.id, fun σ => LinearMap.ext fun x => rfl⟩
      haveI := isIso_cohomologyMapAlong_of_mulEquiv (galFixedFieldEquivOpen U)
        (continuous_galFixedFieldEquivOpen U) (continuous_galFixedFieldEquivOpen_symm U) f
        Function.bijective_id 2
      exact (asIso (cohomologyMapAlong (galFixedFieldEquivOpen U).toMonoidHom
        (continuous_galFixedFieldEquivOpen U) f 2)).toLinearEquiv.toEquiv.subsingleton)
  exact_mod_cast h

theorem cdp_galois_le_one_of_algebraic_ratFunc : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [Field K]
    [Algebra (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (p : ℕ), p.Prime → GroundTheory.ProfCoh.cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  intro k K Ω _ _ _ _ _ _ _ _ p hp
  by_cases hpK : (p : K) = 0
  · exact cdp_le_one_of_char_eq K Ω p hp hpK
  · exact cdp_le_one_of_ne_char k K Ω p hp hpK

end GlobalTheory.TsenCD
end

section
open GroundTheory.ProfCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cdp_galois_le_one_of_isAlgebraic_ratFunc : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (p : ℕ), p.Prime → GroundTheory.ProfCoh.cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  first | (exact @GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc) | (exact GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc) | (intros; apply GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CdOne

open GroundTheory.ProfCoh

theorem subsingleton_cohomology_trivial_zmod (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (q : ℕ) [NeZero q]
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q → cdp ℓ G ≤ 1) (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (cohomology (Rep.trivial (ZMod q) G (ZMod q)) n) := by
  let A : Rep.{0} (ULift.{0} ℤ) G := Rep.trivial (ULift.{0} ℤ) G (ULift.{0} (ZMod q))
  have hq0 : q ≠ 0 := NeZero.ne q
  have hA : ∀ a : A, q • a = 0 := fun a => by
    change (q • a : ULift.{0} (ZMod q)) = 0
    ext
    simp
  have htors : IsAddTorsion A := fun a =>
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q, Nat.pos_of_ne_zero hq0, hA a⟩
  have hsub : Subsingleton (cohomology A n) := by
    suffices h' : ∀ x : cohomology A n, x = 0 from ⟨fun x y => (h' x).trans (h' y).symm⟩
    intro x
    refine eq_zero_of_primaryComponent_eq_bot q hq0 (fun ℓ hℓ hℓq => ?_) x
      (nsmul_cohomology_eq_zero A hA n x)
    refine primaryComponent_cohomology_eq_bot_of_cdp_lt (p := ℓ) A htors ?_
    calc cdp ℓ G ≤ 1 := h ℓ hℓ hℓq
      _ < n := by exact_mod_cast (show 1 < n by omega)
  let e : A ≃+ (Rep.trivial (ZMod q) G (ZMod q) : Rep (ZMod q) G) := AddEquiv.ulift
  exact (cohomologyAddEquivOfEquiv (A := A) (A' := Rep.trivial (ZMod q) G (ZMod q)) e
    (fun _ _ => rfl) n).symm.injective.subsingleton

end GlobalTheory.EtC.CdOne

namespace GlobalTheory.EtC

theorem gaugeSplitting_holds : C1 := by
  intro q _ k K _ _ _ _ _ hq n i hn
  let f : k →+* K := (algebraMap (RatFunc k) K).comp (algebraMap k (RatFunc k))
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqk : (q : k) ≠ 0 := by
    intro h0
    have : (q : K) = 0 := by rw [← map_natCast f q, h0, map_zero]
    exact hq.ne_zero this
  haveI : NeZero (q : k) := ⟨hqk⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (Polynomial.degree_cyclotomic_pos q k hq0).ne'
  have hζk : IsPrimitiveRoot ζ q := (Polynomial.isRoot_cyclotomic_iff).1 hζ
  have hζK : IsPrimitiveRoot (f ζ) q := hζk.map_of_injective f.injective
  have hroot : ∃ z : K, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 := by
    refine ⟨f ζ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζK.isRoot_cyclotomic hq0
  obtain ⟨u⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q K hq hroot n i 0
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n by omega)
  have hm : 2 ≤ m := by omega
  let Ω := SeparableClosure K
  have hζΩ : IsPrimitiveRoot (algebraMap K Ω (f ζ)) q :=
    hζK.map_of_injective (algebraMap K Ω).injective
  obtain ⟨e⟩ := GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology q K Ω hq 0 (Rep.trivial (ZMod q) (Ω ≃ₐ[K] Ω) (ZMod q)) _ hζΩ
    (Module.Basis.singleton Unit (ZMod q)) (fun σ a _ => by simp) m
  have hsub := GlobalTheory.EtC.CdOne.subsingleton_cohomology_trivial_zmod (Ω ≃ₐ[K] Ω) q
    (fun ℓ hℓ _ => GlobalTheory.T.cdp_galois_le_one_of_isAlgebraic_ratFunc k K Ω ℓ hℓ) m hm
  exact (u.trans e).injective.subsingleton

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc : GlobalTheory.EtC.C1 := by
  first | (exact @GlobalTheory.EtC.gaugeSplitting_holds) | (exact GlobalTheory.EtC.gaugeSplitting_holds) | (intros; apply GlobalTheory.EtC.gaugeSplitting_holds  <;> assumption)
end
