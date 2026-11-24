module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.cardStep :
    ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : B →+ C)
      (a c : ℕ), Function.Exact f g → CardLe A a → CardLe C c → CardLe B (a * c) := by
  intro A B C _ _ _ f g a c hex hA hC
  obtain ⟨hAf, ha⟩ := hA
  obtain ⟨hCf, hc⟩ := hC
  have hker : g.ker = f.range := AddMonoidHom.exact_iff.mp hex
  have h1 : Nat.card g.ker ≤ Nat.card A := by
    rw [hker]
    exact Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h2 : g.ker.index ≤ Nat.card C := by
    rw [AddSubgroup.index_ker]
    exact Finite.card_subtype_le _
  haveI hfin1 : Finite g.ker := by
    rw [hker]
    exact Finite.of_surjective _ f.rangeRestrict_surjective
  have hpos1 : 0 < Nat.card g.ker := Nat.card_pos
  have hpos2 : 0 < g.ker.index := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos
  have hcard := AddSubgroup.card_mul_index g.ker
  refine ⟨Nat.finite_of_card_ne_zero (by rw [← hcard]; positivity), ?_⟩
  rw [← hcard]
  exact Nat.mul_le_mul (h1.trans ha) (h2.trans hc)
