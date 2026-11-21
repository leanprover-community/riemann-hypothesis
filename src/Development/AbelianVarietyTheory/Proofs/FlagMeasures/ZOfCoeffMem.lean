import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLawsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraSeriesCentralIdempotentNeZero
import BuildAid.ForwardExisting

section
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem trace_mem_adjoin_of_pow_eq_one (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (N : ℕ) (hN : 0 < N) (hf : f ^ N = 1) :
    LinearMap.trace ℂ V f ∈
      IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  refine multiset_sum_mem _ ?_
  intro μ hμ
  have hroot : f.charpoly.IsRoot μ := (Polynomial.mem_roots'.mp hμ).2
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hroot).exists_hasEigenvector
  have h1 := hv.pow_apply N
  rw [hf] at h1
  have h2 : μ ^ N = 1 := by
    have h3 : (μ ^ N - 1) • v = 0 := by
      rw [sub_smul, ← h1]; simp
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv.2
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp N hN.ne').eq_pow_of_pow_eq_one h2
  rw [← hi]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ _) i

theorem isChar_mem_adjoin_exp :
    ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ) (N : ℕ), 0 < N → Nat.card G ∣ N → IsChar χ →
      ∀ x, χ x ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  intro G _ _ χ N hN hd hχ x
  obtain ⟨V, hV⟩ := hχ
  rw [← hV x]
  refine trace_mem_adjoin_of_pow_eq_one V (V.ρ x) N hN ?_
  obtain ⟨k, rfl⟩ := hd
  rw [← map_pow, pow_mul, pow_card_eq_one', one_pow, map_one]

end GlobalTheory.GLm
end

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOfFDRep_mem_cyclotomic_adjoin : ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ) (N : ℕ), 0 < N → Nat.card G ∣ N → IsChar χ → ∀ x, χ x ∈ IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  atlas_forward_decl GlobalTheory.GLm.isChar_mem_adjoin_exp
end

section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem zOf_coeff_mem {G : Type} [Group G] [Fintype G] (K : IntermediateField ℚ ℂ) (χ : G → ℂ)
    (h : ∀ x, χ x ∈ K) (y : G) : (zOf χ).coeff y ∈ K := by
  unfold zOf
  refine Finset.sum_induction _ (fun a : MonoidAlgebra ℂ G => a.coeff y ∈ K) ?_ ?_ ?_
  · intro a b ha hb
    have := K.add_mem ha hb
    simpa using this
  · simp
  · intro x _
    have h1 : χ 1 / (Fintype.card G : ℂ) * χ x⁻¹ ∈ K :=
      K.mul_mem (K.div_mem (h 1) (natCast_mem K _)) (h _)
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact h1
    · exact K.zero_mem

theorem isSer_eSerC (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (hg : 5 ≤ g) (hG : Green) (r N : ℕ) (hN : 0 < N)
    (hd : Nat.card (GL (Fin r) (ZMod g)) ∣ N) : GlobalTheory.MemN.IsSer r g N (eSerC L r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L hg hG r
  refine ⟨h1, h2, h3, ?_, h5, ?_⟩
  · intro f
    refine ⟨fun h0 hf => GlobalTheory.T.harishChandraSeriesCentralIdempotent_ne_zero g L hG r f hf.1 hf.2.1 hf.2.2 h0, h4 f⟩
  · intro f x
    unfold eSerC
    refine finsum_mem_induction (fun a : MonoidAlgebra ℂ (Gn g r) => a.coeff x ∈
      IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))}) ?_ ?_ ?_
    · simp
    · intro a b ha hb
      have := add_mem ha hb
      simpa using this
    · intro χ hχ
      obtain ⟨⟨V, _, hV⟩, _⟩ := hχ
      exact zOf_coeff_mem _ χ (GlobalTheory.T.isCharacterOfFDRep_mem_cyclotomic_adjoin (Gn g r) χ N hN hd ⟨V, hV⟩) x

end GlobalTheory.GLm
end
