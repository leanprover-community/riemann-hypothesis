module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.RatDiscrete

theorem subgroup_countable_discrete : ∀ (I : AutInst), (∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset) ∧ I.GFset.Countable ∧ ∀ C : Set I.GA, IsCompact C → (I.GFset ∩ C).Finite :=
  fun I => ⟨⟨ratSub I, rfl⟩, countable_GFset I,
    fun _ hC => Set.inter_comm _ _ ▸ finite_inter I hC⟩

end GlobalTheory.RatDiscrete
