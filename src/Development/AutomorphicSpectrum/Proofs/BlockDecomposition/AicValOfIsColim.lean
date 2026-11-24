module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Monic

@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Colim

theorem iota_tr {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    {f : ∀ n, G n →ₐ[A] G (n + 1)} {L : Type} [CommRing L] [Algebra A L] {ι : ∀ n, G n →ₐ[A] L}
    (hc : IsColim f ι) (n : ℕ) : ∀ (k : ℕ) (x : G n), ι (n + k) (tr f n k x) = ι n x
  | 0, _ => rfl
  | k + 1, x => by
    show ι (n + k + 1) (f (n + k) (tr f n k x)) = ι n x
    rw [hc.comm, iota_tr hc n k x]

theorem aic_of_isColim {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    {f : ∀ n, G n →ₐ[A] G (n + 1)} {L : Type} [CommRing L] [Algebra A L] {ι : ∀ n, G n →ₐ[A] L}
    (hc : IsColim f ι) (hA : ∀ n, AICm (f n : G n →+* G (n + 1))) : AIC L := by
  intro P hP hd
  obtain ⟨n, y, hy⟩ := hc.surj P.natDegree (fun i => P.coeff i)
  set Q : Polynomial (G n) := Polynomial.X ^ P.natDegree + ∑ i : Fin P.natDegree, Polynomial.C (y i) * Polynomial.X ^ (i : ℕ) with hQ
  have hQm : Q.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt y)
  have hmap : Q.map (ι n : G n →+* L) = P := by

    rw [hQ, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, RingHom.coe_coe, hy]
    conv_rhs => rw [hP.as_sum]
    rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (P.coeff i) * Polynomial.X ^ i) P.natDegree]
  have hQd : 0 < Q.natDegree := by
    have := Polynomial.natDegree_map_le (f := (ι n : G n →+* L)) (p := Q)
    rw [hmap] at this; omega
  obtain ⟨x, hx⟩ := hA n Q hQm hQd
  refine ⟨ι (n + 1) x, ?_⟩
  have h2 : (Q.map (f n : G n →+* G (n + 1))).map (ι (n + 1) : G (n + 1) →+* L) = P := by
    rw [Polynomial.map_map, ← hmap]; congr 1; ext z; simp [hc.comm]
  rw [← h2]
  exact Polynomial.IsRoot.map (ι (n + 1) : G (n + 1) →+* L) hx

theorem val_of_isColim {A : Type} [CommRing A] (π : A) {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    {f : ∀ n, G n →ₐ[A] G (n + 1)} {L : Type} [CommRing L] [Algebra A L] {ι : ∀ n, G n →ₐ[A] L}
    (hc : IsColim f ι) (hV : ∀ n, VALm (algebraMap A (G n) π) (f n : G n →+* G (n + 1))) :
    VAL (algebraMap A L π) := by
  intro u v ⟨N, hN⟩
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hN
  obtain ⟨n, y, hy⟩ := hc.surj 4 ![a, b, u, v]
  have h0 := hy 0; have h1 := hy 1; have h2 := hy 2; have h3 := hy 3
  simp only [Matrix.cons_val] at h0 h1 h2 h3
  obtain ⟨k, hk⟩ := hc.ker n 1 (fun _ => y 0 * y 2 + y 1 * y 3 - algebraMap A (G n) π ^ N)
    (fun _ => by simp [h0, h1, h2, h3, hab])
  have hk0 := hk 0
  set m := n + k
  set t := tr f n k
  have hspan : algebraMap A (G m) π ^ N ∈ Ideal.span {t (y 2), t (y 3)} := by
    refine Ideal.mem_span_pair.mpr ⟨t (y 0), t (y 1), ?_⟩
    have := hk0
    simp only [map_sub, map_add (f := _), map_mul, map_pow, AlgHom.commutes] at this
    exact (sub_eq_zero.mp this)
  obtain ⟨e, he, he1, he2⟩ := hV m (t (y 2)) (t (y 3)) ⟨N, hspan⟩
  have hu : ι (m + 1) (f m (t (y 2))) = u := by rw [hc.comm, iota_tr hc n k, h2]
  have hv : ι (m + 1) (f m (t (y 3))) = v := by rw [hc.comm, iota_tr hc n k, h3]
  refine ⟨ι (m + 1) e, he.map (ι (m + 1)), ?_, ?_⟩
  · rw [Ideal.mem_span_singleton] at he1 ⊢
    have := map_dvd (ι (m + 1)) he1
    simpa [map_mul, hu, hv] using this
  · rw [Ideal.mem_span_singleton] at he2 ⊢
    have := map_dvd (ι (m + 1)) he2
    simpa [map_mul, map_sub, hu, hv] using this

theorem aic_val_of_isColim : ∀ (A : Type) [CommRing A] (π : A) (G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → (∀ n, AICm (f n : G n →+* G (n + 1))) → (∀ n, VALm (algebraMap A (G n) π) (f n : G n →+* G (n + 1))) → AIC L ∧ VAL (algebraMap A L π) :=
  fun _ _ π _ _ _ _ _ _ _ _ hc hA hV => ⟨aic_of_isColim hc hA, val_of_isColim π hc hV⟩
end GlobalTheory.CompanionTheory.Colim
