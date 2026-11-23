module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem rho_not_real {tr nm : ℤ} {r : ℂ} (hd : tr ^ 2 - 4 * nm < 0)
    (hr : r ^ 2 - (tr : ℂ) * r + (nm : ℂ) = 0) : (starRingEnd ℂ) r ≠ r := by
  intro hc
  have him : r.im = 0 := Complex.conj_eq_iff_im.mp hc
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, r = (x : ℂ) := ⟨r.re, by apply Complex.ext <;> simp [him]⟩
  have h1 : x ^ 2 - (tr : ℝ) * x + (nm : ℝ) = 0 := by exact_mod_cast hr
  have h2 : ((tr : ℝ)) ^ 2 - 4 * (nm : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [sq_nonneg (2 * x - (tr : ℝ))]

theorem UpperTheory.Gal.W2.placeT_of :
    UpperTheory.Gal.W2.PlaceT := by
  intro p _ D G L ha v hv t₀ ht
  have i₀ : Fin D.a := ⟨0, by omega⟩
  have hsub : ∀ i j : Fin D.a, i = j := fun i j => by
    apply Fin.ext; have := i.2; have := j.2; omega
  have hρ : t₀ (D.ω : D.F) = D.ρc := by rw [← ht i₀]; exact D.tau_ω i₀
  have hne : (starRingEnd ℂ) D.ρc ≠ D.ρc := rho_not_real D.disc_neg D.ρc_root
  obtain ⟨i, hi⟩ := (L.sig v).1 hv
  have hφ : ∀ x, (G.iotaC.comp (L.s i)) (L.e x) = t₀ x := fun x => by
    rw [← ht i]; exact L.s_C i x
  refine ⟨fun v' hv' => ?_, hρ, hne, ?_⟩
  · obtain ⟨j, hj⟩ := (L.sig v').1 hv'
    rw [hi, hj, hsub i j]
  · have hemb := InfinitePlace.embedding_mk_eq (G.iotaC.comp (L.s i))
    rw [← hi] at hemb
    rcases hemb with h | h
    · left
      have hx : ∀ x, v.embedding (L.e x) = t₀ x := fun x => by rw [h]; exact hφ x
      refine ⟨?_, hx⟩
      unfold sgnV
      rw [if_pos (by rw [hx, hρ])]
    · right
      have hx : ∀ x, v.embedding (L.e x) = (starRingEnd ℂ) (t₀ x) := fun x => by
        rw [h, ComplexEmbedding.conjugate_coe_eq, hφ]
      have hω : v.embedding (L.e (D.ω : D.F)) ≠ D.ρc := by rw [hx, hρ]; exact hne
      refine ⟨?_, fun hall => hω (by rw [hall, hρ]), fun x => by rw [hx, Complex.conj_conj]⟩
      unfold sgnV
      rw [if_neg hω]
