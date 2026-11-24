module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
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

namespace GlobalTheory

theorem symplectic_zmod_lift : ∀ (h k : ℕ) (M : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) (ZMod k)),
    M ∈ Matrix.symplecticGroup (Fin h) (ZMod k) → ∃ N : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) ℤ,
      N ∈ Matrix.symplecticGroup (Fin h) ℤ ∧ N.map (Int.cast : ℤ → ZMod k) = M := by
  intro h k M hM
  obtain ⟨N, hN⟩ := symplecticGroupMap_zmod_surjective (Fin h) k ⟨M, hM⟩
  refine ⟨N.1, N.2, ?_⟩
  have := congrArg Subtype.val hN
  rw [coe_symplecticGroupMap] at this
  simpa using this

end GlobalTheory
