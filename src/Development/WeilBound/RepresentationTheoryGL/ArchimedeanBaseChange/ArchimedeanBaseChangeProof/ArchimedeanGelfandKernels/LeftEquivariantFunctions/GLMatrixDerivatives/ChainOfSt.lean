module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
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

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.LfSt.ChainPf

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def DC {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) (Fr : Mat n → (V →L[ℂ] V))
    (f : Mat n → V) : Mat n → V :=
  fun x => ∑ p, ε (hb p) (Rd (hb p) f x + fderiv ℝ Fr 1 (hb p) (f x))

def kapL {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) (Fr k : Mat n → (V →L[ℂ] V))
    (y : Mat n) : V →L[ℂ] V :=
  ∑ p, ε (hb p) * (Ld (hb p) k y + fderiv ℝ Fr 1 (hb p) * k y)

def kapR {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) (Fr k : Mat n → (V →L[ℂ] V))
    (y : Mat n) : V →L[ℂ] V :=
  ∑ p, (-(Rd (hb p) k y) * ε (hb p) + k y * ε (hb p) * fderiv ℝ Fr 1 (hb p))

def DCinCE : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ f ∈ CE E, DC ε Fr f ∈ CE E

def DCwave : Prop :=
  GelComm → ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ u, IsWave E u →
    IsWave E fun t => DC ε Fr (u t)

def ParamInt : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ (g : ℝ → ℝ) (T : ℝ), IsBump g T →
    ContDiffOn ℝ ∞ (fun x => ∫ t, (g t : ℂ) • u t x) (GLs n) ∧
    ∀ X, ∀ x ∈ GLs n, Rd X (fun x' => ∫ t, (g t : ℂ) • u t x') x = ∫ t, (g t : ℂ) • Rd X (u t) x

def ZopDC : Prop :=
  GelComm → ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (h : Mat n → E.V), ContDiffOn ℝ ∞ h (GLs n) → ∀ w : List (Bool × ℕ),
      ContDiffOn ℝ ∞ (zOp w h) (GLs n) ∧ ∀ x ∈ GLs n, zOp w (DC ε Fr h) x = DC ε Fr (zOp w h) x

def ActDer : Prop :=
  Unimod → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), ContDiffOn ℝ ∞ k (GLs n) → PositivityTheory.RgBcC.Cpt k → ContDiffOn ℝ ∞ f (GLs n) →
    ContDiffOn ℝ ∞ (act μ E k f) (GLs n) ∧
    ∀ X, ∀ x ∈ GLs n, Rd X (act μ E k f) x = ∫ y : G n, Ld X k y.val (f (x * y.val)) ∂μ

def IBPAct : Prop :=
  Unimod → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), ContDiffOn ℝ ∞ k (GLs n) → PositivityTheory.RgBcC.Cpt k → ContDiffOn ℝ ∞ f (GLs n) →
    ∀ X, ∀ x ∈ GLs n, ∫ y : G n, k y.val (Rd X f (x * y.val)) ∂μ = -∫ y : G n, Rd X k y.val (f (x * y.val)) ∂μ

def KapEquiv : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ (k : Mat n → (E.V →L[ℂ] E.V)),
    ContDiffOn ℝ ∞ k (GLs n) → (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂) →
    ContinuousOn (kapL ε Fr k) (GLs n) ∧ ContinuousOn (kapR ε Fr k) (GLs n) ∧
    ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ,
      kapL ε Fr k (y * k₂.1) = kapL ε Fr k y * E.ρ k₂ ∧ kapR ε Fr k (y * k₂.1) = kapR ε Fr k y * E.ρ k₂

end PositivityTheory.RgBcC.LfSt.ChainPf
