module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GaloisValuations.GlobalB
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

open ReciprocityTheory.Gal Pointwise NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_frob_at_place_over_prime : ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω),
    A.valuation (p : Ω) < 1 → ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∃ q : ℕ, q ≠ 1 ∧
      ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 := by
  intro F Ω _ _ _ _ _ p hp A hpA
  set f : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F) with hf
  have fA : ∀ r : 𝓞 F, f r ∈ A := fun r =>
    mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe r).map (algebraMap F Ω).toIntAlgHom)
  let I : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal A).comap (f.codRestrict A fA)
  have memI : ∀ r, r ∈ I ↔ A.valuation (algebraMap F Ω (r : F)) < 1 := fun r => by
    simp only [I, Ideal.mem_comap]; exact A.valuation_lt_one_iff _
  have hIp : I.IsPrime := Ideal.comap_isPrime _ _
  have hpI : (p : 𝓞 F) ∈ I := by
    rw [memI]; simpa using hpA
  have hIne : I ≠ ⊥ := fun h => by
    have h' := hpI
    rw [h, Ideal.mem_bot] at h'
    exact hp.out.ne_zero (by exact_mod_cast h')
  let v : HeightOneSpectrum (𝓞 F) := ⟨I, hIp, hIne⟩
  obtain ⟨σ, hσA, hσ⟩ := exists_frob_over (F := F) (A := A) (v := v) (fun x => (memI x).symm)
  refine ⟨σ, hσA, Nat.card (𝓞 F ⧸ v.asIdeal), fun h1 => ?_, hσ⟩
  have hss : Subsingleton (𝓞 F ⧸ v.asIdeal) := by
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [h1]; exact one_ne_zero)
    exact Finite.card_le_one_iff_subsingleton.mp h1.le
  have : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]; exact Subsingleton.elim _ _
  exact hIp.ne_top ((Ideal.eq_top_iff_one _).2 this)

end GlobalTheory
