module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHeckeEigensystemDeligneSerre
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.exists_integral_hecke_eigensystem_deligne_serre : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l), Function.Injective emb → (∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ Set.range emb = {x | x ∈ L ∧ ‖x‖ ≤ 1}) → ∀ (I : Type) (M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∀ (m : Ideal (MvPolynomial I O)), m.IsMaximal → (∀ p : MvPolynomial I O, (∀ x : M, p • x = 0) → p ∈ m) → ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ emb θ p‖ < 1) ∧ ∃ v ∈ Submodule.span (PadicAlgCl l) (Set.range j), v ≠ 0 ∧ ∀ i, Tq i v = θ i • v := by
  first | exact @GlobalTheory.DeligneSerre.exists_integral_eigensystem | exact GlobalTheory.DeligneSerre.exists_integral_eigensystem | (intros; apply GlobalTheory.DeligneSerre.exists_integral_eigensystem <;> assumption)
