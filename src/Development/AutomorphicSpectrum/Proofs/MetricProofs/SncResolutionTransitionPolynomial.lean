module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCoverAndCone
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

theorem coord_image (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) :
    coord P p '' src P p = {t | ∀ h ∈ ideal P p, eval t h = 0} := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact renPt_zero (chartIdeal P p) (affCoord p (rep x))
      ((mem_conePts_iff_chartIdeal hP p (rep x) hx).1 (rep_mem x))
  · intro ht
    obtain ⟨w, hwd⟩ : ∃ w, w = t ∘ Fintype.equivFin (Σ k, ι k) := ⟨_, rfl⟩
    have hren : renPt w = t := by
      subst hwd
      funext l
      simp [renPt]
    have hw : ∀ h ∈ chartIdeal P p, eval w h = 0 := by
      intro h hh
      rw [← eval_renC w h, hren]
      exact ht _ (Ideal.mem_map_of_mem _ hh)
    obtain ⟨hc, h1, ha⟩ := conePts_of_chartIdeal hP p w hw
    let x : Pts P := ⟨proj w, w, hc, rfl⟩
    have ho : SameOrbit (rep x) w := sameOrbit_of_proj_eq (rep_mem x).1 hc.1 (proj_rep x)
    refine ⟨x, fun k => ?_, ?_⟩
    · obtain ⟨c, hcn, hcz⟩ := ho
      have hk : rep x ⟨k, p k⟩ = c k * w ⟨k, p k⟩ := congrFun hcz ⟨k, p k⟩
      rw [hk, h1 k, mul_one]
      exact hcn k
    · show renPt (affCoord p (rep x)) = t
      rw [affCoord_eq_of_sameOrbit p ho, ha, hren]

theorem coord_trans (p p' : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p ∩ src P p') :
    ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
      (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ),
      eval (coord P p x) q ≠ 0 ∧ ∀ y ∈ src P p ∩ src P p', eval (coord P p y) q ≠ 0 →
        ∀ l, coord P p' y l * eval (coord P p y) q = eval (coord P p y) (F l) := by
  classical
  obtain ⟨e, he⟩ : ∃ e, e = Fintype.equivFin (Σ k, ι k) := ⟨_, rfl⟩
  have hev : ∀ (y : Pts P) (q : Σ k, ι k), eval (coord P p y) (X (e q)) = affCoord p (rep y) q := by
    intro y q
    subst he
    simp [coord, renPt]
  have hev' : ∀ (y : Pts P) (q : Σ k, ι k), coord P p' y (e q) = affCoord p' (rep y) q := by
    intro y q
    subst he
    simp [coord, renPt]
  refine ⟨∏ k, X (e ⟨k, p' k⟩),
    fun l => X l * ∏ k ∈ Finset.univ.erase (e.symm l).1, X (e ⟨k, p' k⟩), ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    rw [hev]
    exact div_ne_zero (hx.2 k) (hx.1 k)
  · intro y hy _ l
    obtain ⟨r, rfl⟩ := e.surjective l
    have hprod := Finset.mul_prod_erase Finset.univ
      (fun k => affCoord p (rep y) ⟨k, p' k⟩) (Finset.mem_univ r.1)
    have hA : affCoord p' (rep y) r * affCoord p (rep y) ⟨r.1, p' r.1⟩ = affCoord p (rep y) r := by
      have h1 := hy.1 r.1
      have h2 := hy.2 r.1
      simp only [affCoord]
      field_simp
    simp only [map_prod, map_mul, hev, hev', Equiv.symm_apply_apply]
    rw [← hprod, ← mul_assoc, hA]

theorem chart_image_and_trans (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    (∀ p : (k : K) → ι k, coord P p '' src P p = {t | ∀ h ∈ ideal P p, eval t h = 0}) ∧
    ∀ p p' : (k : K) → ι k, ∀ x ∈ src P p ∩ src P p',
      ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
        (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ),
        eval (coord P p x) q ≠ 0 ∧ ∀ y ∈ src P p ∩ src P p', eval (coord P p y) q ≠ 0 →
          ∀ l, coord P p' y l * eval (coord P p y) q = eval (coord P p y) (F l) :=
  ⟨coord_image hP, fun p p' x hx => coord_trans p p' x hx⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
