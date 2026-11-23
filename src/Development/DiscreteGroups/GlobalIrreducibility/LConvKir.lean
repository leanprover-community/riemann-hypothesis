module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.DiscreteGroups.GlobalIrreducibility.InHCorner
public import Development.DiscreteGroups.GlobalIrreducibility.LConvKirStep
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

noncomputable section
open GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

open DiscreteGroups.sglob.LConvKir in
theorem kirBump : KirBump := by
  intro k _ _ _ _ ψ hψc hψ m V _ _ ρ hsm v₀
  have key : ∀ j, j ≤ m → ∃ v : V, ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l →
      l v = l v₀ ∧ (l v₀ = 0 → ∀ g, InH j g → l (ρ g v) = 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨v₀, fun l _ => ⟨rfl, fun h0 g hg => by rw [InH_zero g hg, map_one, Module.End.one_apply]; exact h0⟩⟩
    | succ j ih =>
      intro hj
      obtain ⟨v, hv⟩ := ih (by omega)
      obtain ⟨v', hv'⟩ := step ψ hψc hψ ρ hsm j (by omega) v
      exact ⟨v', fun l hl => ⟨(hv' l hl).1.trans (hv l hl).1,
        fun h0 g hg => (hv' l hl).2 ((hv l hl).2 h0) g hg⟩⟩
  obtain ⟨v, hv⟩ := key m le_rfl
  exact ⟨v, fun l hl => ⟨(hv l hl).1, fun h0 g => (hv l hl).2 h0 _ (InH_corner g)⟩⟩

end DiscreteGroups.sglob.LConv
