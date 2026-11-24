module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIdeleGenerator
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewLatticeMoverWithDeterminant

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.SkewMove

variable {D : D7}

theorem coprime_span_of_inert (𝔪 : Ideal (𝓞 D.host.E)) (hcop : IsCoprime 𝔪 (D.host.conj • 𝔪)) {q : ℕ}
    (hq : q.Prime) (hi : InertQ D q) : IsCoprime 𝔪 (Ideal.span {(q : 𝓞 D.host.E)}) := by
  rw [Ideal.isCoprime_iff_sup_eq] at hcop ⊢
  by_contra h
  obtain ⟨P, hPm, hle⟩ := Ideal.exists_le_maximal _ h
  have hqP : (q : 𝓞 D.host.E) ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at hqP
    exact hq.ne_zero (by exact_mod_cast hqP)
  have hPP := hi P hPm.isPrime hP0 hqP
  have h𝔪 : 𝔪 ≤ P := le_trans le_sup_left hle
  have h𝔪' : D.host.conj • 𝔪 ≤ P := by
    intro x hx
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hx
    rw [← hPP, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact h𝔪 hx
  exact hPm.ne_top (top_le_iff.1 (hcop ▸ sup_le h𝔪 h𝔪'))

open Classical in
theorem exists_split_nat (𝔪 : Ideal (𝓞 D.host.E)) (h𝔪 : 𝔪 ≠ ⊥) (hcop : IsCoprime 𝔪 (D.host.conj • 𝔪)) :
    ∃ ns ni : ℕ, 0 < ns ∧ ((ns * ni : ℕ) : 𝓞 D.host.E) ∈ 𝔪 ∧ (∀ q : ℕ, q.Prime → InertQ D q → Nat.Coprime ns q) ∧
      ∃ b ∈ 𝔪, ∃ r : 𝓞 D.host.E, b + (ni : 𝓞 D.host.E) * r = 1 := by
  set n := Ideal.absNorm 𝔪 with hn
  have hn0 : n ≠ 0 := by simpa [hn, Ideal.absNorm_eq_zero_iff] using h𝔪
  set S := n.primeFactors with hS
  refine ⟨∏ p ∈ S.filter (fun p => ¬ InertQ D p), p ^ n.factorization p,
    ∏ p ∈ S.filter (fun p => InertQ D p), p ^ n.factorization p, ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun p hp => pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_filter.1 hp).1) _
  · have : (∏ p ∈ S.filter (fun p => ¬ InertQ D p), p ^ n.factorization p) *
        (∏ p ∈ S.filter (fun p => InertQ D p), p ^ n.factorization p) = n := by
      rw [mul_comm, Finset.prod_filter_mul_prod_filter_not]
      exact Nat.prod_factorization_pow_eq_self hn0
    rw [this, hn]
    exact Ideal.absNorm_mem 𝔪
  · intro q hq hi
    refine Nat.Coprime.symm (Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow_right _ ?_)
    have hp := Finset.mem_filter.1 hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    refine (Nat.coprime_primes hq hpp).2 ?_
    rintro rfl
    exact hp.2 hi
  · have hc : IsCoprime 𝔪 (Ideal.span {((∏ p ∈ S.filter (fun p => InertQ D p), p ^ n.factorization p : ℕ) :
        𝓞 D.host.E)}) := by
      rw [Nat.cast_prod, ← Ideal.prod_span_singleton]
      refine IsCoprime.prod_right fun p hp => ?_
      have hp := Finset.mem_filter.1 hp
      rw [Nat.cast_pow, ← Ideal.span_singleton_pow]
      exact IsCoprime.pow_right (coprime_span_of_inert 𝔪 hcop (Nat.prime_of_mem_primeFactors hp.1) hp.2)
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Submodule.mem_sup] at hc
    obtain ⟨b, hb, c, hc, e⟩ := hc
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hc
    exact ⟨b, hb, r, by rw [← e, mul_comm]⟩

theorem exists_gen_idem (𝔪 : Ideal (𝓞 D.host.E)) (h𝔪 : 𝔪 ≠ ⊥) (hcop : IsCoprime 𝔪 (D.host.conj • 𝔪)) :
    ∃ (y : (AE D)ˣ) (f : AE D),
      (∀ b ∈ 𝔪, ((y⁻¹ : (AE D)ˣ) : AE D) * inc D (b : D.host.E) ∈ OhE D) ∧
      (∃ (k : ℕ) (b : Fin k → 𝓞 D.host.E) (w : Fin k → AE D), (∀ i, b i ∈ 𝔪) ∧ (∀ i, w i ∈ OhE D) ∧
        (y : AE D) = ∑ i, inc D (b i : D.host.E) * w i) ∧
      f ∈ OhE D ∧ f * f = f ∧ f * ((y⁻¹ : (AE D)ˣ) : AE D) ∈ OhE D ∧
      ∀ q : ℕ, q.Prime → InertQ D q → ∀ k : ℕ, ∃ w ∈ OhE D, 1 - f = (q : AE D) ^ k * w := by
  obtain ⟨y, y1, hy⟩ := GlobalTheory.IdealIdele.exists_idele_generator D 𝔪 h𝔪
  obtain ⟨ns, ni, hns, hn𝔪, hcq, b, hb, r, e⟩ := exists_split_nat 𝔪 h𝔪 hcop
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := GlobalTheory.IdealIdele.exists_idem (OhE D) hsep hcpl ns hns
  refine ⟨y, f, y1, hy, hf, hff, ?_, fun q hq hi k => ?_⟩
  · have h1 : inc D (b : D.host.E) + (ni : AE D) * inc D (r : D.host.E) = 1 := by
      have := congrArg (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) e
      simpa using this
    have h2 := y1 _ hn𝔪
    have h3 : inc D (((ns * ni : ℕ) : 𝓞 D.host.E) : D.host.E) = (ns : AE D) * ni := by simp
    rw [h3] at h2
    have hb' := y1 b hb
    have : f * ((y⁻¹ : (AE D)ˣ) : AE D) = f * (((y⁻¹ : (AE D)ˣ) : AE D) * inc D (b : D.host.E)) +
        inc D (r : D.host.E) * w * (((y⁻¹ : (AE D)ˣ) : AE D) * ((ns : AE D) * ni)) := by
      rw [hfw]; linear_combination (-((ns : AE D) * w * ((y⁻¹ : (AE D)ˣ) : AE D))) * h1
    rw [this]
    exact add_mem (mul_mem hf hb') (mul_mem (mul_mem (VacMove.inc_int D r) hw) h2)
  · obtain ⟨w', hw', e'⟩ := h3 (q ^ k) (pow_pos hq.pos k) (Nat.Coprime.pow_right _ (hcq q hq hi))
    exact ⟨w', hw', by rw [e']; push_cast; ring⟩

theorem mem_of_gen {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {y : (AE D)ˣ} {k : ℕ} {b : Fin k → 𝓞 D.host.E}
    {w : Fin k → AE D} (hb : ∀ i, b i ∈ 𝔪) (hw : ∀ i, w i ∈ OhE D) (hy : (y : AE D) = ∑ i, inc D (b i : D.host.E) * w i)
    {z : D.host.E} (hz : ((y⁻¹ : (AE D)ˣ) : AE D) * inc D z ∈ OhE D) :
    z ∈ ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) := by
  have h0 : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  rw [← inv_inv ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)), FractionalIdeal.mem_inv_iff (inv_ne_zero h0)]
  intro β hβ
  rw [FractionalIdeal.mem_inv_iff h0] at hβ
  have hint : ∀ i, inc D ((b i : D.host.E) * β) ∈ OhE D := fun i => by
    have h := hβ _ (FractionalIdeal.mem_coeIdeal_of_mem _ (hb i))
    rw [mul_comm] at h
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h
    rw [← hr]; exact VacMove.inc_int D r
  have e : inc D (z * β) = (((y⁻¹ : (AE D)ˣ) : AE D) * inc D z) * ∑ i, inc D ((b i : D.host.E) * β) * w i := by
    have : ∑ i, inc D ((b i : D.host.E) * β) * w i = (y : AE D) * inc D β := by
      rw [hy, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring
    rw [this, map_mul]
    linear_combination (-(inc D z * inc D β)) * y.inv_mul
  have hm : inc D (z * β) ∈ OhE D := e ▸ mul_mem hz (sum_mem fun i _ => mul_mem (hint i) (hw i))
  rw [GlobalTheory.HeckeVal.inc_mem_iff] at hm
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨⟨_, hm⟩, rfl⟩

theorem conj_smul_ne_bot {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) : D.host.conj • 𝔪 ≠ ⊥ := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪
  intro h
  have := Ideal.smul_mem_pointwise_smul D.host.conj b 𝔪 hb
  rw [h, Ideal.mem_bot, smul_eq_zero_iff_eq] at this
  exact hb0 this

theorem mem_skew_iff {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {y : (AE D)ˣ}
    (y1 : ∀ b ∈ 𝔪, ((y⁻¹ : (AE D)ˣ) : AE D) * inc D (b : D.host.E) ∈ OhE D) {k : ℕ} {b : Fin k → 𝓞 D.host.E}
    {w : Fin k → AE D} (hb : ∀ i, b i ∈ 𝔪) (hw : ∀ i, w i ∈ OhE D) (hy : (y : AE D) = ∑ i, inc D (b i : D.host.E) * w i)
    (x : D.host.E) :
    x ∈ ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ↔
      sgA D (y : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D) * inc D x ∈ OhE D := by
  have hJ0 : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact conj_smul_ne_bot h𝔪
  rw [FractionalIdeal.mem_div_iff_of_ne_zero hJ0]
  constructor
  · intro h
    have hmem : ∀ i, ((y⁻¹ : (AE D)ˣ) : AE D) * inc D (x * D.host.conj (b i : D.host.E)) ∈ OhE D := fun i => by
      have h1 := h _ (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.smul_mem_pointwise_smul D.host.conj (b i) 𝔪 (hb i)))
      obtain ⟨b', hb', e⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
      have e' : x * D.host.conj (b i : D.host.E) = (b' : D.host.E) := by
        change _ = algebraMap (𝓞 D.host.E) D.host.E b'
        rw [e]; rfl
      rw [e']; exact y1 b' hb'
    have e : sgA D (y : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D) * inc D x =
        ∑ i, sgA D (w i) * (((y⁻¹ : (AE D)ˣ) : AE D) * inc D (x * D.host.conj (b i : D.host.E))) := by

      rw [hy, map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, GlobalTheory.NormSum.PtsMem.sgA_inc, map_mul]; ring
    rw [e]
    exact sum_mem fun i _ => mul_mem (VacMove.sgA_mem D (hw i)) (hmem i)
  · intro hs c hc
    obtain ⟨c', hc', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hc
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hc'
    have hcc : D.host.conj (((D.host.conj⁻¹ • c' : 𝓞 D.host.E)) : D.host.E) = (c' : D.host.E) := by
      change D.host.conj (D.host.conj⁻¹ (c' : D.host.E)) = c'
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    have hinv : sgA D ((y⁻¹ : (AE D)ˣ) : AE D) * sgA D (y : AE D) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    refine mem_of_gen h𝔪 hb hw hy ?_
    have e : ((y⁻¹ : (AE D)ˣ) : AE D) * inc D (x * algebraMap (𝓞 D.host.E) D.host.E c') =
        (sgA D (y : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D) * inc D x) *
          sgA D (((y⁻¹ : (AE D)ˣ) : AE D) * inc D ((D.host.conj⁻¹ • c' : 𝓞 D.host.E) : D.host.E)) := by
      rw [map_mul (sgA D), GlobalTheory.NormSum.PtsMem.sgA_inc, hcc, map_mul]
      change _ * (_ * inc D (c' : D.host.E)) = _
      linear_combination (-(((y⁻¹ : (AE D)ˣ) : AE D) * inc D x * inc D (c' : D.host.E))) * hinv
    rw [e]
    exact mul_mem hs (VacMove.sgA_mem D (y1 _ hc'))

theorem move_iff {R : Type*} [CommRing R] (S : Subring R) {e y yi Y Yi T : R} (heS : e ∈ S) (he : e * e = e)
    (hyy : y * yi = 1) (hY : Y * Yi = 1) (hA : e * Y * yi ∈ S) (hB : e * y * Yi ∈ S) :
    ((1 - e) * yi + e) * ((1 - e) * Y + e) * T ∈ S ↔ Y * yi * T ∈ S := by
  have e1 : ((1 - e) * yi + e) * ((1 - e) * Y + e) * T = (1 - e) * (Y * yi * T) + e * T := by
    linear_combination (yi * Y - yi - Y + 1) * T * he
  have e2 : e * T = (e * y * Yi) * (Y * yi * T) := by
    linear_combination (-(e * T * Y * Yi)) * hyy - e * T * hY
  have h1e : 1 - e ∈ S := sub_mem (one_mem _) heS
  rw [e1]
  constructor
  · intro h
    have e3 : Y * yi * T = (1 - e) * ((1 - e) * (Y * yi * T) + e * T) +
        (e * Y * yi) * ((1 - e) * (Y * yi * T) + e * T) := by
      linear_combination (T + Y * yi * (Y * yi * T) - 2 * (Y * yi * T)) * he
    rw [e3]
    exact add_mem (mul_mem h1e h) (mul_mem hA h)
  · intro h
    rw [e2]
    exact add_mem (mul_mem h1e h) (mul_mem hB h)

theorem zeroAt_zero' (D : D7) (q : ℕ) : ZeroAt D q 0 :=
  fun _ => ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩



theorem exists_skew_move : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ d : ℕ, ∃ (g' : GA D d) (x' : (AE D)ˣ), SuppSplit D (g' : GL (Fin d) (AE D)) ∧ Moves D (g' : GL (Fin d) (AE D)) (skewLat D 𝔪 d) ∧ (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x' : AE D) - 1)) ∧ x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin d) (AE D)) * sgU D x' := by
  intro D 𝔪 h𝔪 hcop d
  obtain ⟨g', x', h1, h2, h3, h4, -⟩ := GlobalTheory.SkewCentral.exists_central_skew_move D 𝔪 h𝔪 hcop d
  exact ⟨g', x', h1, h2, h3, h4⟩

end GlobalTheory.SkewMove
