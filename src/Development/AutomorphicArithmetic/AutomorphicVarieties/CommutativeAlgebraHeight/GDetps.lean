module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GDetrad
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GHomprime
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing

private theorem UpperTheory.V.CA.detps_height {A : Type} [CommRing A] [IsNoetherianRing A] (n : ℕ)
    (M : Fin (n + 1) → Fin (n + 1) → A) (v : Fin (n + 1) → A) (I : Ideal A)
    (hI : I = Ideal.span (Set.range (fun a => ∑ b, M a b * v b) ∪ {Matrix.det (Matrix.of M)}))
    (hp : I.radical.IsPrime) (hv : v 0 ∉ I.radical) : I.radical.height ≤ (n + 1 : ℕ) := by
  classical
  have hJI : Ideal.span (Set.range (fun a => ∑ b, M a b * v b)) ≤ I := by
    rw [hI]
    exact Ideal.span_mono Set.subset_union_left
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (hJI.trans I.le_radical)
  have hQprime : Q.IsPrime := hQ.1.1
  have key : Matrix.mulVec (Matrix.adjugate (Matrix.of M)) (Matrix.mulVec (Matrix.of M) v) 0
      = Matrix.det (Matrix.of M) * v 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp
  have hdv : Matrix.det (Matrix.of M) * v 0 ∈ Q := by
    rw [← key]
    apply hQ.1.2
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, rfl⟩)
  have hdet : Matrix.det (Matrix.of M) ∈ Q := by
    rcases hQprime.mem_or_mem hdv with h | h
    · exact h
    · exact absurd (hQP h) hv
  have hIQ : I ≤ Q := by
    rw [hI, Ideal.span_le]
    rintro x (⟨a, rfl⟩ | hx)
    · exact hQ.1.2 (Ideal.subset_span ⟨a, rfl⟩)
    · rw [Set.mem_singleton_iff.mp hx]
      exact hdet
  have hPQ : I.radical = Q :=
    le_antisymm (by rw [← hQprime.radical]; exact Ideal.radical_mono hIQ) hQP
  rw [hPQ]
  have hQ' : Q ∈ (Ideal.span ((Finset.univ.image fun a => ∑ b, M a b * v b : Finset A) :
      Set A)).minimalPrimes := by
    simpa using hQ
  refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hQ').trans ?_
  exact_mod_cast Finset.card_image_le.trans (by simp)

theorem UpperTheory.V.CA.g_detps :
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (n : ℕ),
      let A := MvPowerSeries ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R
      let I : Ideal A := Ideal.span (Set.range (fun a : Fin (n + 1) => ∑ b : Fin (n + 1), (MvPowerSeries.X (Sum.inl (a, b)) * MvPowerSeries.X (Sum.inr b) : A)) ∪ {Matrix.det (Matrix.of fun a b : Fin (n + 1) => (MvPowerSeries.X (Sum.inl (a, b)) : A))})
      I.radical.IsPrime ∧ I.radical.height ≤ (n + 1 : ℕ)) := by
  intro R _ _ _ n A I
  classical
  have hd := UpperTheory.V.CA.g_detrad R n
  simp only at hd
  obtain ⟨hP, hX0, -, hhom⟩ := hd
  set Ip : Ideal (MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R) :=
    Ideal.span (Set.range (fun a : Fin (n + 1) => ∑ b : Fin (n + 1),
      MvPolynomial.X (Sum.inl (a, b)) * MvPolynomial.X (Sum.inr b)) ∪
      {Matrix.det (Matrix.of fun a b : Fin (n + 1) => MvPolynomial.X (Sum.inl (a, b)))}) with hIp
  set φ := (MvPolynomial.coeToMvPowerSeries.ringHom :
    MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R →+* A) with hφ
  have hmap : Ideal.map φ Ip = I := by
    rw [hIp, Ideal.map_span, Set.image_union, Set.image_singleton, ← Set.range_comp]
    congr 3
    · funext a

      simp [φ, map_sum]
    · rw [RingHom.map_det]
      congr 1
      ext a b
      simp [φ]
  obtain ⟨hmp, hcomap⟩ := UpperTheory.V.CA.g_homprime R _ Ip.radical hP hhom
  have hrad : I.radical = Ideal.map φ Ip.radical := by
    apply le_antisymm
    · rw [← hmp.radical]
      apply Ideal.radical_mono
      rw [← hmap]
      exact Ideal.map_mono Ip.le_radical
    · rw [← hmap]
      exact Ideal.map_radical_le φ
  have hIprime : I.radical.IsPrime := by
    rw [hrad]
    exact hmp
  refine ⟨hIprime, ?_⟩
  refine UpperTheory.V.CA.detps_height n (fun a b => (MvPowerSeries.X (Sum.inl (a, b)) : A))
    (fun b => (MvPowerSeries.X (Sum.inr b) : A)) I rfl hIprime ?_
  rw [hrad]
  intro h
  apply hX0
  rw [← hcomap, Ideal.mem_comap]
  simpa [φ] using h
