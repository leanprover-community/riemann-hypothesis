module

public import Mathlib.LinearAlgebra.Dimension.Finrank
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
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem card_lines_le_submodule (F V : Type) [Field F] [AddCommGroup V] [Module F V] [Finite V]
    (K : Submodule F V) :
    Nat.card {l : Submodule F V // Module.finrank F l = 1 ∧ l ≤ K} * (Nat.card F - 1) + 1
      = Nat.card K := by
  classical
  have e : {l : Submodule F V // Module.finrank F l = 1 ∧ l ≤ K}
      ≃ {H : Submodule F K // Module.finrank F H = 1} :=
    { toFun := fun l => ⟨l.1.comap K.subtype, by
        rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
          inf_eq_right.mpr l.2.2]
        exact l.2.1⟩
      invFun := fun H => ⟨H.1.map K.subtype,
        by rw [Submodule.finrank_map_subtype_eq]; exact H.2,
        Submodule.map_subtype_le K H.1⟩
      left_inv := fun l => by
        apply Subtype.ext
        simp only [Submodule.map_comap_subtype]
        exact inf_eq_right.mpr l.2.2
      right_inv := fun H => by
        apply Subtype.ext
        exact Submodule.comap_map_eq_of_injective K.injective_subtype H.1 }
  rw [Nat.card_congr e, ← Nat.card_congr (Projectivization.equivSubmodule F K)]
  exact (Projectivization.card' F K).symm

end GlobalTheory.SW
