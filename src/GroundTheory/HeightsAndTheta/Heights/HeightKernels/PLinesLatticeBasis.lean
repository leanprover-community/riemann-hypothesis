module

public import Mathlib.Algebra.Module.Lattice.Full
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LinesLatticeBasis.proof (V : Type) [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (ι : Type) [Fintype ι]
    (hcard : Fintype.card ι = Module.finrank ℚ V) (M : Submodule ℤ V)
    (hM : Submodule.IsFullLattice ℚ M) :
    ∃ b : Module.Basis ι ℚ V, M = Submodule.span ℤ (Set.range b) := by
  have : Module.Free ℤ M := Submodule.IsLattice.free ℚ M
  have : Module.Finite ℤ M := Submodule.IsLattice.finite ℚ M
  let b0 := Module.finBasis ℤ M
  let B := b0.extendOfIsFullLattice ℚ
  have hc : Fintype.card (Fin (Module.finrank ℤ M)) = Fintype.card ι := by
    rw [hcard, Module.finrank_eq_card_basis B]
  let e := Fintype.equivOfCardEq hc
  refine ⟨B.reindex e, ?_⟩
  rw [Module.Basis.range_reindex]
  have hB : Set.range B = M.subtype '' Set.range b0 := by
    rw [← Set.range_comp']
    exact congrArg Set.range (funext (b0.extendOfIsFullLattice_apply ℚ))
  rw [hB, ← Submodule.map_span, b0.span_eq, Submodule.map_top, Submodule.range_subtype]

end GroundTheory.Heights₂.Heights
