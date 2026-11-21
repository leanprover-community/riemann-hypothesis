import Mathlib
import Formalism.PeriodIntegrals.LocBasisPlace

section
open Submodule

namespace LocBasisPlaceWork

theorem span_clear {R A V : Type*} [CommRing R] [CommRing A] [Algebra R A] (M : Submonoid R)
    [IsLocalization M A] [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
    (S : Set V) : ∀ y ∈ span A S, ∃ s ∈ M, s • y ∈ span R S := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, M.one_mem, by rw [one_smul]; exact subset_span hx⟩
  | zero => exact ⟨1, M.one_mem, by rw [smul_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, M.mul_mem hs ht, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact smul_mem _ _ hsx
    · rw [mul_smul]; exact smul_mem _ _ hty
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj M a
    refine ⟨(t : R) * s, M.mul_mem t.2 hs, ?_⟩
    have key : (t : R) • (a • x) = r • x := by
      rw [← algebraMap_smul A (t : R) (a • x), smul_smul, mul_comm (algebraMap R A _), e,
        algebraMap_smul]
    rw [mul_comm, mul_smul, key, smul_comm]
    exact smul_mem _ _ hsx

theorem core {R A K : Type*} [CommRing R] [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [Field K] [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
    [IsFractionRing A K] (M : Submonoid R) [IsLocalization M A] (N : ℕ)
    (L : Submodule R (Fin N → K)) (hL : L.FG)
    (hsp : Submodule.span K (L : Set (Fin N → K)) = ⊤) :
    ∃ P : Matrix (Fin N) (Fin N) K, P.det ≠ 0 ∧ (∀ a, ∃ s ∈ M, s • P.transpose a ∈ L) ∧
      ∀ x ∈ L, ∃ s ∈ M, ∃ c : Fin N → R, s • x = ∑ a, c a • P.transpose a := by
  obtain ⟨S, rfl⟩ := hL
  set LA : Submodule A (Fin N → K) := span A (S : Set (Fin N → K)) with hLA
  have : Module.Finite A LA := Module.Finite.iff_fg.mpr (Submodule.fg_span S.finite_toSet)
  have : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).mpr (IsFractionRing.injective A K)
  have : Module.IsTorsionFree A LA := inferInstance
  let b := Module.Free.chooseBasis A LA
  let v : Module.Free.ChooseBasisIndex A LA → (Fin N → K) := fun i => (b i : Fin N → K)
  have hliA : LinearIndependent A v := b.linearIndependent.map' LA.subtype (ker_subtype _)
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing A K).mp hliA
  have hsum : ∀ (y : Fin N → K) (hy : y ∈ LA), y = ∑ i, (b.repr ⟨y, hy⟩ i) • v i := by
    intro y hy
    have h2 := congrArg (fun z : LA => (z : Fin N → K)) (b.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have hLAle : ∀ y ∈ LA, y ∈ span K (Set.range v) := by
    intro y hy
    rw [hsum y hy]
    refine sum_mem fun i _ => ?_
    rw [← algebraMap_smul K (b.repr ⟨y, hy⟩ i) (v i)]
    exact smul_mem _ _ (subset_span ⟨i, rfl⟩)
  have hspan : (⊤ : Submodule K (Fin N → K)) ≤ span K (Set.range v) := by
    rw [← hsp, Submodule.span_span_of_tower R K, Submodule.span_le]
    intro x hx
    exact hLAle x (subset_span hx)
  let bK := Module.Basis.mk hli hspan
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A LA) = N := by
    have := Module.finrank_eq_card_basis bK
    simpa using this.symm
  let e := Fintype.equivFinOfCardEq hcard
  set P : Matrix (Fin N) (Fin N) K := (Matrix.of fun a i => v (e.symm a) i).transpose with hP
  have hcol : ∀ a, P.transpose a = v (e.symm a) := fun a => by ext i; simp [hP]
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hP, Matrix.det_transpose]
    have hrows : LinearIndependent K (fun a => (Matrix.of fun a i => v (e.symm a) i) a) :=
      hli.comp e.symm e.symm.injective
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero
  · intro a
    obtain ⟨s, hs, h⟩ := span_clear M (S : Set (Fin N → K)) (v (e.symm a)) (b (e.symm a)).2
    exact ⟨s, hs, by rw [hcol]; exact h⟩
  · intro x hx
    have hxA : x ∈ LA := Submodule.span_le_restrictScalars R A _ hx
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples M Finset.univ
      (fun i => b.repr ⟨x, hxA⟩ i)
    choose c hc using fun i => hs i (Finset.mem_univ i)
    refine ⟨(s : R), s.2, fun a => c (e.symm a), ?_⟩
    have hR : (∑ a, c (e.symm a) • P.transpose a) = ∑ i, c i • v i := by
      simp_rw [hcol]
      exact Equiv.sum_comp e.symm (fun i => c i • v i)
    rw [hR]
    conv_lhs => rw [hsum x hxA, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_assoc, ← hc i, algebraMap_smul]

end LocBasisPlaceWork
end

section
open NumberField

namespace LocBasisPlaceWork

variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (ρ : E →+* ℂ_[p])

theorem norm_le_one (a : 𝓞 E) : ‖ρ (a : E)‖ ≤ 1 := by
  have hv := Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))
  have h2 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer (ρ (a : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) ρ (RingHom.ext_int _ _)
      (RingOfIntegers.isIntegral_coe a)
  have h3 := hv.mem_of_integral h2
  have h4 : ‖ρ (a : E)‖₊ ≤ 1 := h3
  exact_mod_cast h4

def plc : Ideal (𝓞 E) where
  carrier := {a | ‖ρ (a : E)‖ < 1}
  add_mem' {a b} ha hb := by
    show ‖ρ (algebraMap (𝓞 E) E (a + b))‖ < 1
    rw [map_add, map_add]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by
    show ‖ρ ((0 : 𝓞 E) : E)‖ < 1
    simp
  smul_mem' c a ha := by
    show ‖ρ (algebraMap (𝓞 E) E (c * a))‖ < 1
    rw [map_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one ρ c)) ha

theorem mem_plc (a : 𝓞 E) : a ∈ plc ρ ↔ ‖ρ (a : E)‖ < 1 := Iff.rfl

instance plc_isPrime : (plc ρ).IsPrime where
  ne_top' h := by
    have h1 : (1 : 𝓞 E) ∈ plc ρ := h ▸ Submodule.mem_top
    rw [mem_plc] at h1
    simp at h1
  mem_or_mem' {a b} hab := by
    rw [mem_plc, mem_plc]
    have hab' : ‖ρ (algebraMap (𝓞 E) E (a * b))‖ < 1 := hab
    rw [map_mul, map_mul, norm_mul] at hab'
    by_contra h
    push Not at h
    have := mul_le_mul h.1 h.2 zero_le_one (le_trans zero_le_one h.1)
    change ‖ρ (algebraMap (𝓞 E) E a)‖ * ‖ρ (algebraMap (𝓞 E) E b)‖ < 1 at hab'
    linarith

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h1 := PadicComplex.norm_extends' p (p : ℚ_[p])
  simp only [map_natCast, Padic.norm_p] at h1
  have h2 : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    convert h1 using 2
    first
    | rfl
    | exact (map_natCast _ p).symm
    | norm_cast
  rw [h2]
  exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)

theorem plc_ne_bot : plc ρ ≠ ⊥ := by
  intro h
  have hp : (p : 𝓞 E) ∈ plc ρ := by
    rw [mem_plc]
    simpa [map_natCast] using norm_p_lt_one (p := p)
  rw [h, Ideal.mem_bot] at hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp

theorem mem_primeCompl_iff (s : 𝓞 E) : s ∈ (plc ρ).primeCompl ↔ ‖ρ (s : E)‖ = 1 := by
  rw [Ideal.mem_primeCompl_iff, mem_plc, not_lt]
  exact ⟨fun h => le_antisymm (norm_le_one ρ s) h, fun h => h.ge⟩

end LocBasisPlaceWork
end

section
open NumberField

namespace LocBasisPlaceWork

theorem main : PI.LocBasisPlace := by
  intro E _ _ p _ ρ N L hL hsp
  let A := Localization.AtPrime (plc ρ)
  have hle : (plc ρ).primeCompl ≤ nonZeroDivisors (𝓞 E) :=
    Ideal.primeCompl_le_nonZeroDivisors (plc ρ)
  letI : Algebra A E :=
    IsLocalization.localizationAlgebraOfSubmonoidLe A E (plc ρ).primeCompl
      (nonZeroDivisors (𝓞 E)) hle
  have : IsScalarTower (𝓞 E) A E :=
    IsLocalization.localization_isScalarTower_of_submonoid_le A E (plc ρ).primeCompl
      (nonZeroDivisors (𝓞 E)) hle
  have : IsDomain A := IsLocalization.isDomain_localization hle
  have : IsFractionRing A E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (plc ρ).primeCompl A E
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) (plc_ne_bot ρ) A
  obtain ⟨P, hdet, hcol, hx⟩ := core (A := A) (plc ρ).primeCompl N L hL hsp
  refine ⟨P, hdet, fun a => ?_, fun x hxL => ?_⟩
  · obtain ⟨s, hs, h⟩ := hcol a
    exact ⟨s, (mem_primeCompl_iff ρ s).mp hs, h⟩
  · obtain ⟨s, hs, c, h⟩ := hx x hxL
    exact ⟨s, (mem_primeCompl_iff ρ s).mp hs, c, h⟩

end LocBasisPlaceWork
end
