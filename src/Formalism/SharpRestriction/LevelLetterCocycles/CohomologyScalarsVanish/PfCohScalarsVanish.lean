module

public import Formalism.SharpRestriction.LevelLetterCocycles.CohomologyScalarsVanish.CohScalarsVanish
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.CohomologyScalarsVanish

open ReciprocityTheory.Gal

theorem cohScalarsVanish : CohScalarsVanish := by
  intro n k _ G _ _ M _ _ _ _ _ _ _ rho rho' hrr hyp
  obtain ⟨h0, h1, h2⟩ := hyp
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_bot_iff] at h0 ⊢
    intro m hm
    have hm' : m ∈ H0 rho' := by
      show m ∈ rho'.invariants
      rw [Representation.mem_invariants]
      intro g
      rw [hrr]
      exact (Representation.mem_invariants _ _).1 hm g
    exact h0 hm'
  · rw [Submodule.Quotient.subsingleton_iff] at h1 ⊢
    rw [eq_top_iff] at h1 ⊢
    rintro ⟨f, hf⟩ -
    have hf' : f ∈ Z1 rho' := ⟨hf.1, fun g h => by rw [hrr]; exact hf.2 g h⟩
    obtain ⟨m, hm⟩ := h1 (Submodule.mem_top (x := (⟨f, hf'⟩ : Z1 rho')))
    refine ⟨m, ?_⟩
    funext g
    have h3 := congrFun hm g
    simp only [d0, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at h3 ⊢
    rw [← hrr]
    exact h3
  · rw [Submodule.Quotient.subsingleton_iff] at h2 ⊢
    rw [eq_top_iff] at h2 ⊢
    rintro ⟨f, hf⟩ -
    have hf' : f ∈ Z2 rho' := ⟨hf.1, fun g h l => by rw [hrr]; exact hf.2 g h l⟩
    obtain ⟨c, hc, hcf⟩ := h2 (Submodule.mem_top (x := (⟨f, hf'⟩ : Z2 rho')))
    refine ⟨c, hc, ?_⟩
    funext p
    have h3 := congrFun hcf p
    simp only [d1, LinearMap.coe_mk, AddHom.coe_mk] at h3 ⊢
    rw [← hrr]
    exact h3

end Formalism.MainNotions.N.CohomologyScalarsVanish
