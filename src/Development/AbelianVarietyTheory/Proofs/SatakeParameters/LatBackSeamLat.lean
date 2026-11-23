module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

namespace GlobalTheory.LatticeBackSeam

theorem latBack_seam_lat : ∀ {D : Formalism.BasicNotions.D7} {X : Formalism.L2.Col.Fields} (s : Formalism.L2.Ker.Seam D X) {n : ℕ}
    (N : Submodule (NumberField.RingOfIntegers (Formalism.L2.Col.Fields.E X)) (Formalism.L2.Col.Sp (Formalism.L2.Col.Fields.E X) n)),
    GlobalTheory.TwU.latBack s (Formalism.L2.Ker.Seam.lat s N) = N := by
  intro D X s n N
  ext y
  rw [GlobalTheory.TwU.mem_latBack]
  constructor
  · intro hy
    have key : ∀ v ∈ Formalism.L2.Ker.Seam.lat s N, ∃ x ∈ N, (fun l => s.iE (x l)) = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨x, hx, rfl⟩ := hv
        exact ⟨x, hx, rfl⟩
      | zero => exact ⟨0, N.zero_mem, by funext l; simp⟩
      | add v w _ _ hv hw =>
        obtain ⟨x, hx, rfl⟩ := hv
        obtain ⟨x', hx', rfl⟩ := hw
        exact ⟨x + x', N.add_mem hx hx', by funext l; simp⟩
      | smul r v _ hv =>
        obtain ⟨x, hx, rfl⟩ := hv
        refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r • x, N.smul_mem _ hx, ?_⟩
        funext l
        simp [Algebra.smul_def, RingOfIntegers.mapRingEquiv_symm_apply]
    obtain ⟨x, hx, hxy⟩ := key _ hy
    have hxe : x = y := funext fun l => s.iE.injective (congrFun hxy l)
    rw [← hxe]
    exact hx
  · intro hy
    exact Submodule.subset_span ⟨y, hy, rfl⟩

end GlobalTheory.LatticeBackSeam
