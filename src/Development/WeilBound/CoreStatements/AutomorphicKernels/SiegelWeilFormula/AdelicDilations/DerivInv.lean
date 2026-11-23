module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicFunctionalHolomorphicDerivativeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIteratedDerivHolomorphicFamilyStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
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

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

theorem famCont {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ) (hU : IsOpen U)
    (hd : ∀ g, DifferentiableOn ℂ (Ê · g) U) (hc : ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ)) :
    ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z :=
  GlobalTheory.T.continuous_iteratedDeriv_holomorphic_family U Ê hU hd hc

theorem lamDeriv {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (Lf : (G → ℂ) → ℂ)
    (hadd : ∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) → Lf (a • f + f') = a * Lf f + Lf f')
    (hbd : ∃ C : Set G, IsCompact C ∧ ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M)
    (U : Set ℂ) (Ê : ℂ → G → ℂ) (hU : IsOpen U) (hd : ∀ g, DifferentiableOn ℂ (Ê · g) U)
    (hc : ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ)) (hinv : ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, Ê z (γ * g) = Ê z g) :
    DifferentiableOn ℂ (fun z => Lf (Ê z)) U ∧
      ∀ z ∈ U, ∀ j : ℕ, iteratedDeriv j (fun z => Lf (Ê z)) z = Lf fun g => iteratedDeriv j (Ê · g) z :=
  GlobalTheory.T.automorphic_functional_holomorphic_derivative Γ Lf hadd hbd U Ê hU hd hc hinv

theorem derivInv {G : Type} [Mul G] (U : Set ℂ) (Ê : ℂ → G → ℂ) (hU : IsOpen U) (z : ℂ) (hz : z ∈ U) (γ g : G)
    (h : ∀ z ∈ U, Ê z (γ * g) = Ê z g) (j : ℕ) : iteratedDeriv j (Ê · (γ * g)) z = iteratedDeriv j (Ê · g) z := by
  have : (Ê · (γ * g)) =ᶠ[𝓝 z] (Ê · g) := Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => h w hw
  exact this.iteratedDeriv_eq j

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem nbRat (d : SD σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) :
    ∀ β ∈ nF σ d.Y d.b, nb β ∈ rat2 σ d.Y :=
  fun β hβ => kfour.nb_rat hc.1 β hβ

def Bj (d : SD σ) (Φ : d.Fn) (p : Polynomial ℂ) (Ê : ℂ → d.G → ℂ) (j : ℕ) (g : d.G) : ℂ :=
  iteratedDeriv j (Ê · g) (s0 d.m d.n) - iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * (2 * d.I Φ g)

end PositivityTheory.SiegelWeilFormula.AStep

end
