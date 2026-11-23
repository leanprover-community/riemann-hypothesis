module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatricesIntertwiningOfSemilinear
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

open Matrix

theorem _root_.GlobalTheory.T.exists_matrices_intertwining_of_semilinear_alt : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l) (I M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∃ (n : ℕ) (σ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O) (e : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] V), (∀ p, σ p = 0 → ∀ x : M, p • x = 0) ∧ Function.Injective e ∧ (∀ c, e c ∈ Submodule.span (PadicAlgCl l) (Set.range j)) ∧ ∀ i c, Tq i (e c) = e ((σ (MvPolynomial.X i)).map emb *ᵥ c) := by
  first | exact @GlobalTheory.exists_matrices_intertwining_of_semilinear | exact GlobalTheory.exists_matrices_intertwining_of_semilinear | (intros; apply GlobalTheory.exists_matrices_intertwining_of_semilinear <;> assumption)
