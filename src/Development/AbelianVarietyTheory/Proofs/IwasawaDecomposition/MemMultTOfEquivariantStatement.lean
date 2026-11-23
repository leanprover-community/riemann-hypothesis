module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariant
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_multT_of_equivariant' : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ) (L : SmT M →ₗ[ℂ] (GA D V → ℂ)), IsInfFam θ → V.SigOK → AllPlus M → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → FiniteDimensional ℂ (SmT M) → Function.Injective (inclT M) → IsTensAct M π → (∀ x, IsAutFun V (L x)) → (∀ x, ∀ k ∈ J, ∀ g, L x (g * k) = χ k * L x g) → (∀ τ u x, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x)) → L ∈ MultT θ M J χ := by
  first | exact @GlobalTheory.DefLiftMult.mem_multT_of_equivariant | exact GlobalTheory.DefLiftMult.mem_multT_of_equivariant | (intros; apply GlobalTheory.DefLiftMult.mem_multT_of_equivariant <;> assumption)
