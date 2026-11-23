module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLinearRelationDensityOfUnfoldingSteps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.period_linear_relation_density_of_unfolding_steps : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (G : ∀ i, (t (s i)).CC j), (∀ s, (t s).Is) → (∀ i a, IsContAut (c.X j) (φ i a)) → ∀ (W W' : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W' S') (It' : PolF D W'.rank (c.V (j + 1)).rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT (c.M (j + 1))), GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) M' It' → (∀ P₁ P₂ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 (c.It j P₁ (It' P₂ v))) = 0) → ∀ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 v) = 0 := by
  first | exact @GlobalTheory.SeeSaw.perF_rel_of_steps | exact GlobalTheory.SeeSaw.perF_rel_of_steps | (intros; apply GlobalTheory.SeeSaw.perF_rel_of_steps <;> assumption)
