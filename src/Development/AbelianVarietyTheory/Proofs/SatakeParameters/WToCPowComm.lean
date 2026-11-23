module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

theorem wToC_pow_comm {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p])
    (hσ : ∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x)) :
    ∀ (k : ℕ) (x : FormalGroupSystem.WW p), (σ ^ k) (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p ((sigW p)^[k] x) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih, hσ, Function.iterate_succ_apply']

theorem dualOm_wToC : ∀ (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]), (∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x)) → ∀ (n' : ℕ), Even n' → ∀ B : OmBasis p n', GlobalTheory.ThBe0.DualOm σ n' (fun r => Formalism.L2.G.Pend.wToC p (B.om r)) (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) := by
  intro p _ σ hσ n' hn B
  have hk := wToC_pow_comm σ hσ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_fin]
    exact Nat.two_mul_div_two_of_even hn
  · intro r
    exact ⟨Formalism.L2.G.Pend.wToC_mem_Wp p _, Formalism.L2.G.Pend.wToC_mem_Wp p _⟩
  · intro r
    refine ⟨?_, ?_⟩
    · rw [hk, B.fix r]
    · rw [hk, B.fixS r]
  · intro r r'
    have h := congrArg (Formalism.L2.G.Pend.wToC p) (B.dual r r')

    rw [map_sum] at h
    rw [← Fin.sum_univ_eq_sum_range (fun i => (σ ^ (2 * i)) (Formalism.L2.G.Pend.wToC p (B.om r) * Formalism.L2.G.Pend.wToC p (B.omS r')))]
    simp only [← map_mul, hk]
    rw [h]
    split_ifs <;> simp

end GlobalTheory.TwU
