module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCoordinatesCellChangeBirational
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_flagCoordinates_cellChange_birational : ∀ (κ T : Type) [Field κ] [Infinite κ] [Finite T] (r : T → ℕ) (G : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ) (σ : ∀ τ, Equiv.Perm (Fin (r τ))), (∀ τ, IsUnit (G τ).det) → ∃ (e : FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ) ≃ₐ[κ] FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ)) (b : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) (FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ))), (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) ∧ ∀ τ, (G τ).map (algebraMap κ _) * lowM (fun v => algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v)) τ = (lowM (fun v => e (algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v))) τ).submatrix (σ τ).symm id * b τ := by
  first | exact @GlobalTheory.Reg.cell_change_birational | exact GlobalTheory.Reg.cell_change_birational | (intros; apply GlobalTheory.Reg.cell_change_birational <;> assumption)
