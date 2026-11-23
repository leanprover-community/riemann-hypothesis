module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_sq_eq_neg_of_discr_eq_neg : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := by
  classical
  intro K _ _ d h2 hd
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  haveI : IsGalois ℚ K := inferInstance
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨σ, hσ, huniq⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[ℚ] K)).1 hcard
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, σ} := by
    ext y
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hy : y = 1
    · exact Or.inl hy
    · exact Or.inr (huniq y hy)
  have htr : ∀ x : K, algebraMap ℚ K (Algebra.trace ℚ K x) = x + σ x := by
    intro x
    rw [_root_.trace_eq_sum_automorphisms, huniv, Finset.sum_pair (Ne.symm hσ)]
    rfl
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 :=
    Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis (integralBasis K), h2])
  let b : Fin 2 → K := fun i => integralBasis K (e.symm i)
  have hb : ⇑(integralBasis K) ∘ ⇑e.symm = b := rfl
  have key : algebraMap ℚ K (discr K : ℚ) = (b 0 * σ (b 1) - b 1 * σ (b 0)) ^ 2 := by
    rw [coe_discr, ← Algebra.discr_reindex ℚ (integralBasis K) e, hb, Algebra.discr_def,
      Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, map_sub, map_mul, htr]
    ring
  refine ⟨b 0 * σ (b 1) - b 1 * σ (b 0), ?_⟩
  rw [← key, hd]
  push_cast
  simp

end GlobalTheory
