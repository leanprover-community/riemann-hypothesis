module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.DualLattices.CotangentSurjective
public import ReciprocityTheory.DualLattices.DiscriminantColengthStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LatticeInequalityValuationIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lattice_inequality_valuation_integers : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → (∃ c : C, 0 < v c ∧ v c < 1) → ∀ (n s h : ℕ) (a : Fin n → O), Function.Injective a → ∀ (M : Submodule O (Fin n × Fin s → O)), M.FG → (∀ f ∈ M, (fun y : Fin n × Fin s => a y.1 * f y) ∈ M) → (∀ (τ : Fin n) (z : Fin s → O), ∃ f ∈ M, ∀ i, f (τ, i) = z i) → ∀ (φ : Fin h → Fin n × Fin s → O), (∀ l, φ l ∈ M) → ∀ c : NNReal, c ≠ 0 → HasLen v O (M ⧸ (Submodule.span O (Set.range fun q : Fin n × Fin h => fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y)).comap M.subtype) c → ∃ x : Fin n → NNReal, (∀ τ, HasLen v O ((Fin s → O) ⧸ Submodule.span O (Set.range fun l => fun i => φ l (τ, i))) (x τ)) ∧ c ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ h ≤ (∏ τ, x τ) ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ s := by
  first | exact @GlobalTheory.ChF.lattice_ineq_integers | exact GlobalTheory.ChF.lattice_ineq_integers | (intros; apply GlobalTheory.ChF.lattice_ineq_integers <;> assumption)
