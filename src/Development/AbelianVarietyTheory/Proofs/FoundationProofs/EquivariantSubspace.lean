module

public import Formalism.FormalDegreeBessel.StatementIO
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

open Formalism.QuantumDeterminants

namespace GlobalTheory.EquivariantSubspace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smoothOnH_zero (H : Matrix (Fin n) (Fin n) ℂ) :
    SmoothOnH H (0 : Matrix (Fin n) (Fin n) ℂ → E) :=
  fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem smoothOnH_add {H : Matrix (Fin n) (Fin n) ℂ} {f f' : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnH H f) (hf' : SmoothOnH H f') : SmoothOnH H (f + f') := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), ?_⟩
  intro g hg hH
  rw [Pi.add_apply, hfF g hg.1 hH, hfF' g hg.2 hH]

theorem smoothOnH_smul {H : Matrix (Fin n) (Fin n) ℂ} {f : Matrix (Fin n) (Fin n) ℂ → E} (a : ℂ)
    (hf : SmoothOnH H f) : SmoothOnH H (a • f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun g => a • F g, hU, hgU, hF.const_smul a, ?_⟩
  intro g hg hH
  rw [Pi.smul_apply, hfF g hg hH]

end GlobalTheory.EquivariantSubspace
