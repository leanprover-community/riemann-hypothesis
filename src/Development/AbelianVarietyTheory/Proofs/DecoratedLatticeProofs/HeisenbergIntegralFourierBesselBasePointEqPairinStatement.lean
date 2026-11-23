module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIntegralFourierBesselBasePointEqPairin
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.heisenbergIntegral_fourierBesselBasePoint_eq_pairing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : HSp D) (B : BesLev D σ) (vB : VolM D (σ + 1) S.rank) (vT : VolM D σ S.rank) (vL : VolM D B.L.rank S.rank) (f : WO S B.V → ℂ) (y : WO S B.L → ℂ), Quasi ψ S B.V f → Quasi ψ S B.L y → (∫ b in vB.𝓕, f (x0 B ⬝ b) * star (y (zl B ⬝ b)) ∂vB.μ = contractT B.o S vL.μ vL.𝓕 (B.d.mixT S ψ vT.μ vT.𝓕 f 0) y 0) ∧ ∫⁻ v in vL.𝓕, ‖B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v))‖ₑ ∂vL.μ ≤ ∫⁻ b in vB.𝓕, ‖f (x0 B ⬝ b)‖ₑ ∂vB.μ := by
  first | exact @GlobalTheory.Unf.FB.heis_base | exact GlobalTheory.Unf.FB.heis_base | (intros; apply GlobalTheory.Unf.FB.heis_base <;> assumption)
