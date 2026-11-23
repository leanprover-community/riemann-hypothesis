module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HermPartIsHermitian
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem isCMFam_host (R : Ranks) (H : Host R) (I : Type) (e : I ≃ R.Psi) :
    IsCMFam (fun i => H.emb (e i).1) := by
  refine ⟨fun i j h => ?_, fun w => ?_⟩
  · rcases NumberField.InfinitePlace.mk_eq_iff.1 h with h1 | h1
    · exact e.injective (GlobalTheory.CuspAlgComparison.tau_injective H h1)
    · exact absurd h1.symm (GlobalTheory.CuspAlgComparison.tau_ne_conj H (e j) (e i))
  · obtain ⟨τ, h | h⟩ := GlobalTheory.CuspAlgComparison.emb_cases H w.embedding
    · refine ⟨e.symm τ, ?_⟩
      rw [← NumberField.InfinitePlace.mk_embedding w, h]
      simp only [Equiv.apply_symm_apply]
      rfl
    · refine ⟨e.symm τ, ?_⟩
      rw [← NumberField.InfinitePlace.mk_embedding w, h]
      simp only [Equiv.apply_symm_apply]
      exact (NumberField.InfinitePlace.mk_conjugate_eq _).symm

end GlobalTheory.Mem.Vol
