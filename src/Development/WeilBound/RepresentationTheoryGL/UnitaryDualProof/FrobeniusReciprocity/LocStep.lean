module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.AdjointSemisimple.AdjunctionCharZero
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocalContinuity.LocalDescentHolds
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpB
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.MemBzOfAdjoin
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.DescFinal
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

namespace PositivityTheory.RgUd.T.Final

open PositivityTheory.RgUd.T

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dich [CharZero k] : Dich (k := k) := PositivityTheory.RgUd.T.Alg.dich k
theorem adjP [CharZero k] : Adj (k := k) := adjunction_char_zero k
theorem locStep : LocStep (k := k) := LocStepPf.local_descent_holds
theorem descA [CharZero k] : DescA (k := k) := PositivityTheory.RgUd.T.Desc.Final.descA k
theorem nilpB [CharZero k] : NilpB (k := k) := PositivityTheory.RgUd.T.Nil.Final.nilpB k

theorem van_all [CharZero k] : ∀ (m n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)),
    Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) = m → CR Z → Van Z := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n Z hm hZ
    refine nilpB k n Z hZ fun ξ hs hi => locStep k n Z hZ ξ hs hi fun y => ?_
    rcases dich k n Z hZ y with h | ⟨s, hs, hsZ, hss, hy⟩
    · exact Or.inl h
    · obtain ⟨hC, hlt⟩ := adjP k n Z hZ s hs hsZ hss
      exact Or.inr fun ξ' h1 h2 => descA k n Z hZ s hs hsZ hss (ih _ (hm ▸ hlt) n _ rfl hC) y hy ξ' h1 h2

theorem thmT [CharZero k] : PositivityTheory.RgUd.ThmT k := by
  intro n Z hcomm hred ξ hsupp hinv f hf
  exact van_all k _ n Z rfl ⟨hcomm, hred⟩ ξ (fun g hg h0 => hsupp g hg fun p hp => h0 p ⟨hp, Set.mem_univ _⟩)
    (fun g hg f hf => hinv g hg f hf) f hf

end PositivityTheory.RgUd.T.Final
