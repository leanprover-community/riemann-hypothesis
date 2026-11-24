module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitHermitianGeneratorsExist
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

open NumberField GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.split_hermitian_generators_exist : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d r : ℕ) (D : ConjData C p (𝓞 E) d) (χ : 𝓞 E →+* K), (∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits) → (∀ i, ∃ x : Fin r → (Fin d → K) × (Fin d → K), LinearIndependent K (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => D.ρH (RingOfIntegers.basis E q.2) (x q.1)) ∧ ∀ y, y ∈ D.H i ↔ ∃ c : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → K, (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • D.ρH (RingOfIntegers.basis E q.2) (x q.1)) → deg C (quot C D.H (⨆ a : 𝓞 E, LinearMap.range (D.ρH a - χ a • LinearMap.id))) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.deg_quot_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.deg_quot_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.deg_quot_eq_zero <;> assumption)
