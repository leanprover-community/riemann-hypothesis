module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne

@[expose] public section

set_option autoImplicit false

noncomputable section

open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped TensorProduct Classical

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem sigma_finsum {α : Type} {δ : α → Type} (F : (Σ a, δ a) → ℂ) (S : Finset (Σ a, δ a))
    (hS : ∀ z, F z ≠ 0 → z ∈ S) : ∑ᶠ a, ∑ᶠ d, F ⟨a, d⟩ = ∑ z ∈ S, F z := by
  have hinj : ∀ a, Set.InjOn (Sigma.mk a : δ a → Σ a, δ a) (Sigma.mk a ⁻¹' (S : Set (Σ a, δ a))) :=
    fun a => sigma_mk_injective.injOn
  let U : ∀ a, Finset (δ a) := fun a => S.preimage (Sigma.mk a) (hinj a)
  have h1 : ∀ a, ∑ᶠ d, F ⟨a, d⟩ = ∑ d ∈ U a, F ⟨a, d⟩ := fun a =>
    finsum_eq_sum_of_support_subset _ (fun d hd => by
      simpa [U] using hS _ hd)
  have hT : Function.support (fun a => ∑ᶠ d, F ⟨a, d⟩) ⊆ ((S.image Sigma.fst : Finset α) : Set α) := by
    intro a ha
    have ha' : ∑ d ∈ U a, F ⟨a, d⟩ ≠ 0 := by
      rw [← h1 a]; exact ha
    obtain ⟨d, hd, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha'
    have hd' : (⟨a, d⟩ : Σ a, δ a) ∈ S := by simpa [U] using hd
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, hd', rfl⟩)
  rw [finsum_eq_sum_of_support_subset _ hT]
  simp_rw [h1]
  rw [← Finset.sum_sigma (S.image Sigma.fst) U F]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ⟨a, d⟩
  simp only [Finset.mem_sigma, Finset.mem_image, U, Finset.mem_preimage]
  exact ⟨fun h => h.2, fun h => ⟨⟨_, h, rfl⟩, h⟩⟩

private theorem flat_finsum {α : Type} {β γ : α → Type} (n : ∀ a, β a → ℂ) (t : ∀ a, β a → γ a → ℂ)
    (S : Finset (Σ a, β a × γ a)) (hS : ∀ z, t z.1 z.2.1 z.2.2 ≠ 0 → z ∈ S) :
    ∑ᶠ a, ∑ᶠ b, n a b * ∑ᶠ y, t a b y = ∑ z ∈ S, n z.1 z.2.1 * t z.1 z.2.1 z.2.2 := by
  rw [← sigma_finsum (fun z : Σ a, β a × γ a => n z.1 z.2.1 * t z.1 z.2.1 z.2.2) S
    (fun z hz => hS z (right_ne_zero_of_mul hz))]
  refine finsum_congr fun a => ?_
  have hfin : (Function.support fun d : β a × γ a => n a d.1 * t a d.1 d.2).Finite := by
    have hinj : Set.InjOn (fun d : β a × γ a => (⟨a, d⟩ : Σ a, β a × γ a))
        ((fun d : β a × γ a => (⟨a, d⟩ : Σ a, β a × γ a)) ⁻¹' (S : Set (Σ a, β a × γ a))) := by
      intro d _ d' _ h
      simpa using h
    refine (S.finite_toSet.preimage hinj).subset ?_
    intro d hd
    exact hS ⟨a, d⟩ (right_ne_zero_of_mul hd)
  rw [finsum_curry _ hfin]
  refine finsum_congr fun b => ?_
  exact mul_finsum _ _

theorem cxFlat_of : CxFlat := by
  intro p _ G v c K f S hS
  unfold cxTotalM cxSumM cxSumAtM
  refine flat_finsum (α := FCls G) (β := fun q => PtsOf G v K q) (γ := fun q => grp G (Quot.out q).β)
    (fun q a => ((Nat.card (Stab G v (Quot.out q).β (Quot.out q).trivAf.choose
      (Quot.out q).trivAf.choose_spec.choose (Quot.out q).trivAf.choose_spec.choose_spec K (Kp G)
      (Quot.out a)) : ℕ) : ℂ)⁻¹)
    (fun q a y => if FixL G v (Quot.out q).β y (Quot.out a).2.1 then
      f ((Quot.out a).1.1⁻¹ * toAfF G (Quot.out q).β (Quot.out q).trivAf.choose
          (Quot.out q).trivAf.choose_spec.choose (Quot.out q).trivAf.choose_spec.choose_spec y *
          (Quot.out a).1.1) *
        oneP G ((Quot.out a).1.2⁻¹ * toP1 G (Quot.out q).β y * (Quot.out a).1.2) *
        c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (eigL G v (Quot.out q).β y (Quot.out a).2.1)
      else 0) S ?_
  intro z hz
  refine hS z ?_
  beta_reduce at hz
  split_ifs at hz with hfix
  · have h12 := left_ne_zero_of_mul hz
    exact ⟨hfix, left_ne_zero_of_mul h12, right_ne_zero_of_mul h12⟩
  · exact (hz rfl).elim

end UpperTheory.Gal.LocalSmoothExtension
