module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.InfEmbGrpEq
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform
public import GroundTheory.AutomorphicForms.ReductionSiegel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace UpperTheory.V.Fb

def SmTo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (φ : GA E a → ℂ), φ ∈ TR.Sm E a → IsArchSmooth φ

def SmOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (φ : GA E a → ℂ), IsArchSmooth φ → φ ∈ TR.Sm E a

def CptIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (y : GL (Fin a) (TR.Rinf E)),
    grpEq E a y ∈ archCompact E a ↔ y.val ∈ Matrix.unitaryGroup (Fin a) (TR.Rinf E)

def KFinTo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (φ : TR.Sm E a),
    IsOpen {k | TR.finRep E a k φ = φ} →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => TR.cptRep E a k φ)) → IsKFinite φ.1

def HeightLe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ), ∃ N : ℕ, ∀ y : GL (Fin a) (TR.Rinf E),
    AutomorphicForm.height (TR.infGL E a y) ≤ TR.height y ^ N

def HeightGe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (g : GA E a),
    TR.height (GeneralLinearGroup.map (TR.pInf E) g) ≤ 3 * AutomorphicForm.height g

def VecLower : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ (g : AdelicGLn.AdelicGL K n) (x : Fin n → K),
    x ≠ 0 → 1 ≤ C * AutomorphicForm.height g ^ N * Reduction.height g x

def DetBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ g : AdelicGLn.AdelicGL K n,
    (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤ C * AutomorphicForm.height g ^ N

def SiegelHeight : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ω : Set (AdelicGLn.AdelicGL K n)), IsCompact ω →
    ω ⊆ (Reduction.adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) → ∀ t : ℝ, 0 < t →
    ∃ (C : ℝ) (N : ℕ), ∀ (g : AdelicGLn.AdelicGL K n) (γ : GL (Fin n) K),
      AdelicGLn.diagonal K n γ * g ∈ Reduction.siegelSet n ω t →
      AutomorphicForm.height (AdelicGLn.diagonal K n γ * g) ≤ C * AutomorphicForm.height g ^ N

def SiegelFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ω : Set (AdelicGLn.AdelicGL K n)), IsCompact ω → ∀ t : ℝ,
    ∃ Ω : Set (AdelicGLn.FiniteAdelicGL K n), IsCompact Ω ∧ ∀ g ∈ Reduction.siegelSet n ω t, finPart g ∈ Ω

def GrowthTo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (φ : TR.Sm E a),
    (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | TR.finRep E a k φ = φ} →
    (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * TR.infGL E a y)‖ ≤ C * TR.height y ^ N) → HasModerateGrowth φ.1

def CuspTo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (φ : GA E a → ℂ), IsLeftInvariant φ → Continuous φ →
    GlobalTheory.CuspRep.IsCuspidal φ → AutomorphicForm.IsCuspidal φ

def CuspOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (φ : GA E a → ℂ), IsLeftInvariant φ → Continuous φ →
    AutomorphicForm.IsCuspidal φ → GlobalTheory.CuspRep.IsCuspidal φ

end UpperTheory.V.Fb
