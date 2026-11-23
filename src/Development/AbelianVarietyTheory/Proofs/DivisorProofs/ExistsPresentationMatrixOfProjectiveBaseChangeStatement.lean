module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationMatrixOfProjectiveBaseChange
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

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.exists_presentation_matrix_of_projective_baseChange : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    Module.Projective B (B ⊗[R] M) →
    ∃ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) ∧
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) := by
  first | (exact @GlobalTheory.projective_baseChange_presentation_matrix) | (exact GlobalTheory.projective_baseChange_presentation_matrix) | (intros; apply GlobalTheory.projective_baseChange_presentation_matrix <;> assumption)
