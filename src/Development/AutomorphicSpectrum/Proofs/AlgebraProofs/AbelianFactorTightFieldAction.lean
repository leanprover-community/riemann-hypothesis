module

public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagComparisonTheoremStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractElementaryStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractRestrictionStatement
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

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem flagConcl_directFactor_of_subquotient :
    SubquotientStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, (∀ x : N, p • x = 0) → IsAbFactor p AA.carrier → IsTight v p AA.carrier → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (Nw : Type) [AddCommGroup Nw] [Module F Nw] [Fintype Nw] [DecidableEq Nw] (i : Nw →+ N) (π : N →+ Nw), (∀ y, π (i y) = y) → (∀ h ∈ AA.carrier, (fun x => h (i (π x))) ∈ AA.carrier) → FStable F (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) → ∀ (n : ℕ) (b : Module.Basis (Fin n) F Nw) (σ : MulChar F R), IsFund p σ → FlagConcl v p (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) b σ := by
  intro hS p _ C _ _ _ v R _ _ hInt hp hcomp N _ _ _ AA hpN hab htight F _ _ _ _ Nw _ _ _ _ i π hπi
    hstab hFS n b σ hσ
  obtain ⟨⟨A', hA'⟩, -, hgen⟩ := GlobalTheory.T.hopf_order_retract_restriction p C v R hInt hp N AA Nw i π hπi hstab
  have ht' := GlobalTheory.T.hopf_order_retract_elementary p C v R hInt hp N hpN AA Nw i π hπi hstab htight
  rw [← hA'] at hFS ht' ⊢
  refine GlobalTheory.T.flag_comparison_theorem p C v R hInt hp F Nw A' hFS ht' n b ?_ σ hσ
  intro k
  rw [hA']
  exact hgen _ (hS p C v R hInt hp hcomp N AA.carrier hab _)

end GlobalTheory.CompanionTheory.Ar.GR
