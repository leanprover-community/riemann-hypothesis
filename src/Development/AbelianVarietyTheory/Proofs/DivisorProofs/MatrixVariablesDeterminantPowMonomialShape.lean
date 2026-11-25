module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffProdLeadingMinors
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DetPowShape

noncomputable def detZ (i : ℕ) : MvPolynomial (Σ _ : Fin i, Fin i) ℤ :=
  Matrix.det (Matrix.of fun a b : Fin i =>
    (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) ℤ))

theorem detPow_eq_map (C : Type) [Field C] (i c : ℕ) :
    detPow C i c = MvPolynomial.map (Int.castRingHom C) (detZ i ^ c) := by
  rw [map_pow, detZ, RingHom.map_det]
  unfold detPow
  congr 2
  ext a b
  simp [RingHom.mapMatrix_apply]

theorem weight_eq_sum {i : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    Finsupp.weight w α = ∑ x, α x * w x := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [smul_eq_mul]

theorem det_wh {R : Type} [CommRing R] {i : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ)
    (hw : ∀ σ : Equiv.Perm (Fin i), ∑ j, w ⟨j, σ j⟩ = 1) :
    MvPolynomial.IsWeightedHomogeneous w (Matrix.det (Matrix.of fun a b : Fin i =>
      (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) R))) 1 := by
  rw [Matrix.det_apply']
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp := MvPolynomial.IsWeightedHomogeneous.prod (R := R) (w := w) Finset.univ
    (fun j => (MvPolynomial.X ⟨j, σ j⟩ : MvPolynomial (Σ _ : Fin i, Fin i) R))
    (fun j => w ⟨j, σ j⟩) (fun j _ => MvPolynomial.isWeightedHomogeneous_X R w _)
  rw [hw σ] at hp
  have hc : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Σ _ : Fin i, Fin i) R) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
  simp only [Matrix.of_apply]
  rw [hc]
  simpa using hp.C_mul ((Equiv.Perm.sign σ : ℤ) : R)

theorem sum_of_mem_support {C : Type} [Field C] {i c : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ)
    (hw : ∀ σ : Equiv.Perm (Fin i), ∑ j, w ⟨j, σ j⟩ = 1) (α) (hα : α ∈ (detPow C i c).support) :
    ∑ x, α x * w x = c := by
  have h := (det_wh (R := C) w hw).pow c
  rw [← weight_eq_sum]
  have := h (MvPolynomial.mem_support_iff.1 hα)
  simpa using this

theorem detPow_shape : ∀ (C : Type) [Field C] [CharZero C] (i c : ℕ),
    (detPow C i c).IsHomogeneous (i * c) ∧ (∀ α, ∃ n : ℤ, (detPow C i c).coeff α = n) ∧
    (detPow C i c).coeff (∑ a : Fin i, Finsupp.single ⟨a, a⟩ c) = 1 ∧
    ∀ α ∈ (detPow C i c).support, (∀ a : Fin i, ∑ b : Fin i, α ⟨b, a⟩ = c) ∧
      (∀ b : Fin i, ∑ a : Fin i, α ⟨b, a⟩ = c) := by
  intro C _ _ i c
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (GlobalTheory.LeadingMinors.isHomogeneous_det_X (k := C)
      (fun a b : Fin i => (⟨b, a⟩ : Σ _ : Fin i, Fin i))).pow c
    simpa [Fintype.card_fin, detPow] using this
  · intro α
    exact ⟨(detZ i ^ c).coeff α, by rw [detPow_eq_map, MvPolynomial.coeff_map]; simp⟩
  · let f : Fin i → (Σ _ : Fin i, Fin i) := fun a => ⟨a, a⟩
    have hf : Function.Injective f := fun x y h => congrArg Sigma.fst h
    have h1 : (∑ a : Fin i, Finsupp.single (⟨a, a⟩ : Σ _ : Fin i, Fin i) c) =
        Finsupp.mapDomain f (∑ a : Fin i, Finsupp.single a c) := by
      change _ = Finsupp.mapDomain.addMonoidHom f _

      simp [map_sum, f]
    have h2 : MvPolynomial.killCompl hf (detPow C i c) =
        MvPolynomial.monomial (∑ a : Fin i, Finsupp.single a c) 1 := by
      unfold detPow
      rw [map_pow, GlobalTheory.LeadingMinors.killCompl_det_X (k := C) hf
        (fun a b : Fin i => (⟨b, a⟩ : Σ _ : Fin i, Fin i)) id (fun a => rfl),
        MvPolynomial.monomial_pow, one_pow]
      · congr 1
        rw [Finset.smul_sum]
        simp
      · rintro a b hab ⟨x, hx⟩
        obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 hx
        exact hab ((eq_of_heq h2).symm.trans h1)
    rw [h1, ← MvPolynomial.coeff_killCompl hf, h2, MvPolynomial.coeff_monomial, ite_eq_left rfl]
  · intro α hα
    constructor
    · intro a
      have h := sum_of_mem_support (C := C) (c := c)
        (fun x => if x.2 = a then 1 else 0) (fun σ => by
          rw [← Equiv.sum_comp σ.symm]
          simp) α hα
      rw [Fintype.sum_sigma] at h
      simpa using h
    · intro b
      have h := sum_of_mem_support (C := C) (c := c)
        (fun x => if x.1 = b then 1 else 0) (fun σ => by simp) α hα
      rw [Fintype.sum_sigma] at h
      simpa using h

end GlobalTheory.DetPowShape
