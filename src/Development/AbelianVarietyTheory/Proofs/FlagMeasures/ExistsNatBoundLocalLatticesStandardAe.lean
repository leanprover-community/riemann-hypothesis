module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanSingleIff
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

theorem exists_uniform_bound {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (n : ℕ)
    (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep))
    (hfin : {p | Λ p ≠ Submodule.span (A.L p).O
      (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite)
    (hm : ∀ p, ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) →
      (m : (A.loc p).Ep) • v ∈ Λ p) ∧ ∀ v ∈ Λ p, ∀ i, (m : (A.loc p).Ep) * v i ∈ (A.L p).O) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ p, (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) →
      (N : (A.loc p).Ep) • v ∈ Λ p) ∧ ∀ v ∈ Λ p, ∀ i, (N : (A.loc p).Ep) * v i ∈ (A.L p).O := by
  choose m hm0 hm1 hm2 using hm
  refine ⟨∏ q ∈ hfin.toFinset, m q, Finset.prod_ne_zero_iff.mpr fun q _ => hm0 q, fun p => ?_⟩
  by_cases hp : p ∈ hfin.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hp
    rw [hk]
    refine ⟨fun v hv => ?_, fun v hv i => ?_⟩
    · have h1 := hm1 p v hv
      have h2 : ((m p * k : ℕ) : (A.loc p).Ep) • v = k • ((m p : (A.loc p).Ep) • v) := by
        rw [← Nat.cast_smul_eq_nsmul (A.loc p).Ep, smul_smul]
        push_cast
        ring_nf
      rw [h2]
      exact nsmul_mem h1 k
    · have h1 := hm2 p v hv i
      have h2 : ((m p * k : ℕ) : (A.loc p).Ep) * v i = (k : (A.loc p).Ep) * ((m p : (A.loc p).Ep) * v i) := by
        push_cast; ring
      rw [h2]
      exact (A.L p).O.mul_mem (natCast_mem (A.L p).O k) h1
  · have hΛ : Λ p = Submodule.span (A.L p).O
        (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep)) := by
      by_contra h
      exact hp (hfin.mem_toFinset.mpr h)
    refine ⟨fun v hv => ?_, fun v hv i => ?_⟩
    · rw [hΛ, mem_span_single_iff]
      intro i
      have := (A.L p).O.mul_mem (natCast_mem (A.L p).O (∏ q ∈ hfin.toFinset, m q)) (hv i)
      simpa only [Pi.smul_apply, smul_eq_mul] using this
    · rw [hΛ, mem_span_single_iff] at hv
      exact (A.L p).O.mul_mem (natCast_mem (A.L p).O _) (hv i)

end GlobalTheory.HL.Glue
