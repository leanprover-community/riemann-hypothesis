module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorWedgeDetChange
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.tensor_wedge_det_change : ∀ (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] (V : Ψ → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)] (n : ℕ) (e e' : ∀ τ, Fin n → V τ) (T : ∀ τ, Matrix (Fin n) (Fin n) Ω) (a a' : Ω), (∀ τ, LinearIndependent Ω (e τ)) → (∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤) → (∀ τ q, e' τ q = ∑ p, T τ p q • e τ p) → a • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e τ) : PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) = a' • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e' τ) : PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) → a = a' * ∏ τ, (T τ).det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TopWedge.eq_mul_prod_det | exact GlobalTheory.CompanionTheory.Ar.TopWedge.eq_mul_prod_det | (intros; apply GlobalTheory.CompanionTheory.Ar.TopWedge.eq_mul_prod_det <;> assumption)
