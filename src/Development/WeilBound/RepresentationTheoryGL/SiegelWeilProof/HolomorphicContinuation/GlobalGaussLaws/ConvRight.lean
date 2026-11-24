module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def ConvRight : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n →
    ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → ∀ g, GlobalTheory.Eis.CosetConv (P D n) (GF D n) (sect ω H Φ z) g

def ThLin : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ Φ', PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ →
    PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ' → PositivityTheory.PfSWUS.InRange V n →
    ∀ g, thetaInt ω ν (Φ + Φ') g = thetaInt ω ν Φ g + thetaInt ω ν Φ' g

def GLamBd : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ L ∈ lamSet (n := n) ψ,
    (∀ (a : ℂ) (F F' : G D n → ℂ), Continuous F → Continuous F' → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
      (∀ γ ∈ GF D n, ∀ g, F' (γ * g) = F' g) → L (a • F + F') = a * L F + L F') ∧
    ∃ C : Set (G D n), IsCompact C ∧ ∀ (F : G D n → ℂ) (M : ℝ), Continuous F → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
      (∀ x ∈ C, ‖F x‖ ≤ M) → ‖L F‖ ≤ M

def GLsing : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n), IsCharAF D.host.F ψ →
    IsInfFam θ → IsPlaceEmb θ τ ι → ∀ F : G D n → ℂ, Continuous F → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
    (∀ L ∈ lamSet (n := n) ψ, L F = 0) → ∀ ψ₀, IsSingTest ψ₀ → ∀ (nb : (Fin n → Fin n → ℝ) → GR n), (∀ x, mR (nb x) = nU (herm x)) →
      ∀ (g : G D n) (a b : GR n), ∫ x, F (g * ι (a * nb x * b)) * ψ₀ x = 0

def LNZ : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ), IsCharAF D.host.F ψ → IsInfFam θ →
    HasRealPar ψ θ l → ∀ τ, l τ ≠ 0

def MainSt : Prop :=
  AbsThm → SFrame → SEmb → SigOK → SplitFock → TensMem → LocOpEx → LocInst → LinSec → GSplit → GIauto → GIk → GIinv →
    GIdil → EisStrong → GLamBd → GLsing → PositivityTheory.PfSWUS.CoefND → ConvRight → ThLin → LNZ →
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (s0 V n) (thetaInt ω ν Φ g)

end PositivityTheory.Rg.Sw.Glob
