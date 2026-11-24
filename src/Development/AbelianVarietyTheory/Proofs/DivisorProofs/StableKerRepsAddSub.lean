module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelEquivConjugatePointsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mulStable_intCast_add {L : PeriodPair} {w : ℂ} (a : ℤ) (h : MulStable L w) :
    MulStable L ((a : ℂ) + w) := by
  intro ω hω
  rw [add_mul]
  refine add_mem ?_ (h ω hω)
  have : ((a : ℂ) * ω) = a • ω := by rw [zsmul_eq_mul]
  rw [this]
  exact zsmul_mem hω a

theorem mulStable_intCast_sub {L : PeriodPair} {w : ℂ} (a : ℤ) (h : MulStable L w) :
    MulStable L ((a : ℂ) - w) := by
  intro ω hω
  rw [sub_mul]
  refine sub_mem ?_ (h ω hω)
  have : ((a : ℂ) * ω) = a • ω := by rw [zsmul_eq_mul]
  rw [this]
  exact zsmul_mem hω a

theorem ringEquiv_sqrtNegNat (σ : ℂ ≃+* ℂ) (p : ℕ) :
    σ (sqrtNegNat p) = sqrtNegNat p ∨ σ (sqrtNegNat p) = -sqrtNegNat p := by
  have h : σ (sqrtNegNat p) ^ 2 = sqrtNegNat p ^ 2 := by
    rw [← map_pow, sqrtNegNat_sq, map_neg, map_natCast]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

theorem stable_kerReps_add_sub : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (a : ℤ) (S S' : Finset ℂ), L.g₂ ∈ F → L.g₃ ∈ F → MulStable L (sqrtNegNat p) → IsKerReps L (a + sqrtNegNat p) S → IsKerReps L (a - sqrtNegNat p) S' → Stable L F (Sum.elim (fun t : S => (t : ℂ)) (fun t : S' => (t : ℂ))) := by
  intro p F L a S S' h2 h3 hm hS hS' σ hσ
  have e2 : L.g₂ = σ L.g₂ := (hσ _ h2).symm
  have e3 : L.g₃ = σ L.g₃ := (hσ _ h3).symm
  have mp := mulStable_intCast_add a hm
  have mm := mulStable_intCast_sub a hm
  have hσa : σ (a : ℂ) = a := map_intCast σ a
  rcases ringEquiv_sqrtNegNat σ p with hs | hs
  · have hp : σ ((a : ℂ) + sqrtNegNat p) = (a : ℂ) + sqrtNegNat p := by rw [map_add (f := _), hσa, hs]
    have hm' : σ ((a : ℂ) - sqrtNegNat p) = (a : ℂ) - sqrtNegNat p := by rw [map_sub, hσa, hs]
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_kernel_equiv_conjugate_points L σ _ S S e2 e3 mp hS (by rw [hp]; exact hS)
    obtain ⟨e', he'⟩ := GlobalTheory.T.exists_kernel_equiv_conjugate_points L σ _ S' S' e2 e3 mm hS' (by rw [hm']; exact hS')
    refine ⟨Equiv.sumCongr e e', ?_⟩
    rintro (t | t)
    · exact he t
    · exact he' t
  · have hp : σ ((a : ℂ) + sqrtNegNat p) = (a : ℂ) - sqrtNegNat p := by
      rw [map_add (f := _), hσa, hs, sub_eq_add_neg]
    have hm' : σ ((a : ℂ) - sqrtNegNat p) = (a : ℂ) + sqrtNegNat p := by
      rw [map_sub, hσa, hs, sub_neg_eq_add]
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_kernel_equiv_conjugate_points L σ _ S S' e2 e3 mp hS (by rw [hp]; exact hS')
    obtain ⟨e', he'⟩ := GlobalTheory.T.exists_kernel_equiv_conjugate_points L σ _ S' S e2 e3 mm hS' (by rw [hm']; exact hS)
    refine ⟨(Equiv.sumCongr e e').trans (Equiv.sumComm _ _), ?_⟩
    rintro (t | t)
    · exact he t
    · exact he' t

end GlobalTheory.CMModel
