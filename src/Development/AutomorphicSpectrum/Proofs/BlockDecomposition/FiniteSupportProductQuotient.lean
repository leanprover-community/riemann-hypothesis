module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Coset.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Basic.Finite.Prod

@[expose] public section

namespace GlobalTheory.CompanionTheory.ProdQuotient

theorem support_mul_out_finite (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁)
    (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ)
    (h₁ : (Function.support fun q : G₁ ⧸ K₁ => f₁ q.out).Finite)
    (h₂ : (Function.support fun q : G₂ ⧸ K₂ => f₂ q.out).Finite)
    (i₁ : ∀ k ∈ K₁, ∀ g, f₁ (g * k) = f₁ g) (i₂ : ∀ k ∈ K₂, ∀ g, f₂ (g * k) = f₂ g) :
    (Function.support fun q : (G₁ × G₂) ⧸ K₁.prod K₂ => f₁ q.out.1 * f₂ q.out.2).Finite := by
  let φ : (G₁ × G₂) ⧸ K₁.prod K₂ → (G₁ ⧸ K₁) × (G₂ ⧸ K₂) :=
    fun q => ((q.out.1 : G₁ ⧸ K₁), (q.out.2 : G₂ ⧸ K₂))
  have hinj : Function.Injective φ := by
    intro a b hab
    have e₁ : ((a.out.1 : G₁ ⧸ K₁)) = (b.out.1 : G₁ ⧸ K₁) := congrArg Prod.fst hab
    have e₂ : ((a.out.2 : G₂ ⧸ K₂)) = (b.out.2 : G₂ ⧸ K₂) := congrArg Prod.snd hab
    rw [QuotientGroup.eq] at e₁ e₂
    have key : ((a.out : G₁ × G₂) : (G₁ × G₂) ⧸ K₁.prod K₂) = (b.out : G₁ × G₂) := by
      rw [QuotientGroup.eq]
      exact Subgroup.mem_prod.mpr ⟨e₁, e₂⟩
    simpa using key
  have inv₁ : ∀ g : G₁, f₁ (g : G₁ ⧸ K₁).out = f₁ g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₁ g
    rw [hk]
    exact i₁ k k.2 g
  have inv₂ : ∀ g : G₂, f₂ (g : G₂ ⧸ K₂).out = f₂ g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₂ g
    rw [hk]
    exact i₂ k k.2 g
  refine ((h₁.prod h₂).preimage hinj.injOn).subset ?_
  intro q hq
  have hq' : f₁ q.out.1 * f₂ q.out.2 ≠ 0 := hq
  refine ⟨?_, ?_⟩
  · change f₁ (q.out.1 : G₁ ⧸ K₁).out ≠ 0
    rw [inv₁]
    exact left_ne_zero_of_mul hq'
  · change f₂ (q.out.2 : G₂ ⧸ K₂).out ≠ 0
    rw [inv₂]
    exact right_ne_zero_of_mul hq'

end GlobalTheory.CompanionTheory.ProdQuotient
