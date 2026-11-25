module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.TensorSpan
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ReProd
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace PositivityTheory.HtPt.Re

theorem tens_hopf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), ∃ AA : HopfOrder (C := C) R (N₁ × N₂), AA.carrier = tens A₁.carrier A₂.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (z.1, 0)) ∈ AA.carrier) ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (0, z.2)) ∈ AA.carrier) ∧ ∀ c₁ c₂, HasColen R v A₁.carrier c₁ → HasColen R v A₂.carrier c₂ → HasColen R v AA.carrier (c₁ ^ Fintype.card N₂ * c₂ ^ Fintype.card N₁) := by
  intro p _ C _ _ _ v R _ _ _ _ N₁ _ _ _ N₂ _ _ _ A₁ A₂
  refine ⟨PositivityTheory.HtPt.Re.hopfProd A₁ A₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; rfl
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_inl A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_inr A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_stab₁ A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_stab₂ A₁ A₂
  · intro c₁ c₂ h₁ h₂
    rw [PositivityTheory.HtPt.Re.hopfProd_carrier]
    exact PositivityTheory.HtPt.Re.hasColen_tn h₁ h₂

end PositivityTheory.HtPt.Re
