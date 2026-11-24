module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAlgHomAdjoin
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

theorem adjoin_hom_extend_of_denominator (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω]
    [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S) (hψ : ψ h ≠ 0) (T : Set F)
    (hT : ∀ x ∈ T, (h : F) * x ∈ S) : Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  first
  | exact @_root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin
  | exact _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin
  | (apply _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin ..)

end GlobalTheory
