module

public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)


open Classical in
def atTau (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  if h : ∃ x, IsAtTau θ V τ g x then h.choose else 1

def lieAt (τ : D.what₂.Tau) : Set (Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  {X | Xᴴ * gramAt D V τ + gramAt D V τ * X = 0}

def oneP (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) : GA D V :=
  atTau θ V τ (NormedSpace.exp (t • X))

def Rder (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) : GA D V → ℂ :=
  fun g => deriv (fun t : ℝ => φ (g * oneP θ V τ X t)) 0

def conjAt (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  -((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ)

def RderC (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) : GA D V → ℂ :=
  Rder θ V τ ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) φ +
    Complex.I • Rder θ V τ ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) φ

def gelf (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ) : GA D V → ℂ :=
  ∑ idx : Fin (k + 1) → Fin V.rank,
    (List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) φ

def normInf (g : GA D V) : ℝ :=
  ∑ τ, ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖)

structure IsAutFunSm (φ : GA D V → ℂ) : Prop extends IsAutFun V φ where
  smooth : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)
  zfin : ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W
  growth : ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
    ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
      ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N

def ThetaSmoothnessCondition {X : ThetaX D} (T : ThetaTied D X) : Prop :=
  AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, V.SigOK → Set.range (T.ev V) = {φ | IsAutFunSm θ V φ}

end Formalism.L2.Theta

end
