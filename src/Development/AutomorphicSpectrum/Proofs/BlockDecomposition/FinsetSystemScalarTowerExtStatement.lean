module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemScalarTowerExt
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

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.finset_system_scalar_tower_ext : ∀ {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Module.Flat B A] {ι : Type} [DecidableEq ι] [Fintype ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, Module B (M S)] [∀ S, AddCommGroup (N S)] [∀ S, Module A (N S)] [∀ S, Module B (N S)] [∀ S, IsScalarTower B A (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T), (∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap B (r h)) → ∀ (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T), (∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap A (r' h)) → ∀ (ψ : ∀ S, M S →ₗ[B] N S), (∀ S, IsBaseChange A (ψ S)) → (∀ {S T : Finset ι} (h : S ⊆ T) x, r' h (ψ S x) = ψ T (r h x)) → ExP M r → ExP N r' := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat.exP_flat | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat.exP_flat | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat.exP_flat <;> assumption)
