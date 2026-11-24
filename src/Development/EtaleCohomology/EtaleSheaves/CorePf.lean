module

public import Mathlib.Topology.Sets.Opens
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
import Development.EtaleCohomology.EtaleSheaves.ChowGraphCut
import Development.EtaleCohomology.EtaleSheaves.ChowLCut
import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut LateralTheory.E.ChowGraphCut

namespace LateralTheory.E.CorePf

theorem inf_nonempty {X : Type} [TopologicalSpace X] [PreirreducibleSpace X] {n : ℕ}
    (U : Fin n → TopologicalSpace.Opens X) (hU : ∀ j, (U j : Set X).Nonempty) :
    ∀ s : Finset (Fin n), s.Nonempty → ((s.inf U : TopologicalSpace.Opens X) : Set X).Nonempty := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hU a
  | cons a s ha hs ih =>
    rw [Finset.inf_cons, TopologicalSpace.Opens.coe_inf]
    exact nonempty_preirreducible_inter (U a).2 (s.inf U).2 (hU a) ih

end LateralTheory.E.CorePf

end
