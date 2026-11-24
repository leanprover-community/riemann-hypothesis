module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicFormMultMapValue
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSmoothAutomorphicForm_multMap_value : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : MMap M) (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) → (∀ v, Continuous (T v) ∧ (∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, T v (g * k) = T v g) ∧ T v ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T v) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)) → (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) → ∀ v, IsAutFunSm θ V (T v) := by
  first | exact @GlobalTheory.EquivValues.isAutFunSm | exact GlobalTheory.EquivValues.isAutFunSm | (intros; apply GlobalTheory.EquivValues.isAutFunSm <;> assumption)
