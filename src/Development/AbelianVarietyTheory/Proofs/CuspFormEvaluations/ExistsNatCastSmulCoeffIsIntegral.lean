import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

section
namespace GlobalTheory.NatMultipleIntegralCoefficients

theorem exists_nat_smul_coeff_isIntegral {σ K : Type} [Field K] [CharZero K]
    [FiniteDimensional ℚ K] (P : MvPolynomial σ K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : σ →₀ ℕ, IsIntegral ℤ (MvPolynomial.coeff m ((N : K) • P)) := by
  classical
  have halg : ∀ x : K, IsAlgebraic ℤ x := fun x =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  have hx : ∀ x : K, ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : K) * x) := by
    intro x
    obtain ⟨y, hy, h⟩ := (halg x).exists_integral_multiple
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with e | e
    · rw [e] at h
      simpa using h
    · rw [e] at h
      have h2 := h.neg
      simpa using h2
  choose n hn hi using hx
  refine ⟨∏ m ∈ P.support, n (P.coeff m), Finset.prod_pos fun m _ => hn _, fun m => ?_⟩
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ P.support
  · rw [← Finset.prod_erase_mul _ _ hm, Nat.cast_mul, mul_assoc]
    refine IsIntegral.mul ?_ (hi _)
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K)
      (x := ((∏ k ∈ P.support.erase m, n (P.coeff k) : ℕ) : ℤ)))
  · rw [MvPolynomial.notMem_support_iff.1 hm, mul_zero]
    exact isIntegral_zero

end GlobalTheory.NatMultipleIntegralCoefficients
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_natCast_smul_coeff_isIntegral {σ K : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    (P : MvPolynomial σ K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m, IsIntegral ℤ (((N : K) • P).coeff m) := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral
  | exact _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral
  | (apply _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral ..)

theorem smul_mem_HHa {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (t : k) (hP : P ∈ HHa r n k cc isX a) :
    t • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ t hP.1,
    fun σ i i' h s => by rw [map_smul, hP.2.1 σ i i' h s],
    fun m hm => hP.2.2 m (MvPolynomial.support_smul hm)⟩

theorem exists_natCast_smul_mem_harmA :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∃ N : ℕ, 0 < N ∧ (N : c.F) • P ∈ harmA c a n ∧ ((N : c.F) • P).support = P.support := by
  intro E _ _ _ H Dw l c a n P hP
  haveI := c.fin
  obtain ⟨N, hN, h⟩ := exists_natCast_smul_coeff_isIntegral (K := c.F) P
  refine ⟨N, hN, ⟨smul_mem_HHa _ hP, fun m => h m⟩, ?_⟩
  have hN' : (N : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  ext m
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul, hN']

end GlobalTheory
end
