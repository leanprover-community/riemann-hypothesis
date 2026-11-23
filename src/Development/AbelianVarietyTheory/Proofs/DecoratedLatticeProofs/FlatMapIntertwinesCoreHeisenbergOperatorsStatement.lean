module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperators
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.flatMap_intertwines_core_heisenbergOperators : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → (∀ w, evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x y = heisO ψ V₀ W₀ w (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x y)) ∧ (∀ w, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) = heisO ψ V₀ W₀ w (flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ)) ∧ ∀ γ, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ (ratW W₀ V₀ γ) = flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ 0 := by
  first | exact @GlobalTheory.FlatHeis.flatAt_heisO | exact GlobalTheory.FlatHeis.flatAt_heisO | (intros; apply GlobalTheory.FlatHeis.flatAt_heisO <;> assumption)
