module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
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

@[expose] public section

namespace GlobalTheory.BijectiveIntertwining

theorem bijective_of_intertwining {G V V' : Type} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (h : Representation.IsIrreducible ρ) (h' : Representation.IsIrreducible ρ')
    (F : V →ₗ[ℂ] V') (hF : ∀ (g : G) (v : V), F (ρ g v) = ρ' g (F v)) (h0 : F ≠ 0) :
    Function.Bijective F := by
  let K : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker F
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hF, hv, map_zero] }
  let R : Subrepresentation ρ' :=
    { toSubmodule := LinearMap.range F
      apply_mem_toSubmodule := by
        rintro g _ ⟨v, rfl⟩
        exact ⟨ρ g v, hF g v⟩ }
  constructor
  · rcases h.eq_bot_or_eq_top K with hK | hK
    · rw [← LinearMap.ker_eq_bot]
      exact congrArg Subrepresentation.toSubmodule hK
    · exact absurd (LinearMap.ker_eq_top.mp (congrArg Subrepresentation.toSubmodule hK)) h0
  · rcases h'.eq_bot_or_eq_top R with hR | hR
    · exact absurd (LinearMap.range_eq_bot.mp (congrArg Subrepresentation.toSubmodule hR)) h0
    · rw [← LinearMap.range_eq_top]
      exact congrArg Subrepresentation.toSubmodule hR

end GlobalTheory.BijectiveIntertwining
