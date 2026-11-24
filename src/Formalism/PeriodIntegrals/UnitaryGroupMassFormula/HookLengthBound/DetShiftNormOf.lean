module

public import Formalism.PeriodIntegrals.HookBound
public import Formalism.PieriBlockIdeals.CapelliCentralEnveloping
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace PI.HookSteps

open MvPolynomial Formalism.GradedWeylDivisibility

def detX (N : ℕ) : MvPolynomial (Fin N × Fin N) ℚ :=
  (Matrix.of fun a b : Fin N => (X (a, b) : MvPolynomial (Fin N × Fin N) ℚ)).det

def MulXAdj : Prop :=
  ∀ (σ : Type) (v : σ) (f g : MvPolynomial σ ℚ), fockQ (X v * f) g = fockQ f (pderiv v g)

def RenameIso : Prop :=
  ∀ (σ τ : Type) (φ : σ → τ), Function.Injective φ → ∀ f g : MvPolynomial σ ℚ,
    fockQ (rename φ f) (rename φ g) = fockQ f g

def HwDetMul : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    hw ℚ le_rfl (fun i => ν i + 1) = detX N * hw ℚ le_rfl ν

def HwLastZero : Prop :=
  ∀ (n : ℕ) (ν : Fin (n + 1) → ℕ), Antitone ν → ν (Fin.last n) = 0 →
    hw ℚ le_rfl ν =
      rename (fun v : Fin n × Fin n => (Fin.castSucc v.1, Fin.castSucc v.2)) (hw ℚ le_rfl (fun i : Fin n => ν (Fin.castSucc i)))

def polE (N : ℕ) (a b : Fin N) : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
  ∑ s : Fin N, LinearMap.mulLeft ℚ (X (a, s)) ∘ₗ (pderiv (b, s) : Derivation ℚ _ _).toLinearMap

def detD (N : ℕ) : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
  ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
    (List.ofFn fun j : Fin N => ((pderiv (σ j, j) : Derivation ℚ _ _).toLinearMap :
      Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ))).prod

def DetAdj : Prop :=
  ∀ (N : ℕ) (f g : MvPolynomial (Fin N × Fin N) ℚ), fockQ (detX N * f) g = fockQ f (detD N g)

def DetDetId : Prop :=
  ∀ N : ℕ, LinearMap.mulLeft ℚ (detX N) * detD N =
    Formalism.CohomologicalDescent.HeightDescentMinors.capelli (polE N) (algebraMap ℚ _ ((N : ℚ) - 1))

def PolEqRowDiv : Prop :=
  ∀ (N : ℕ) (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ), polE N a b f = rowDiv ℚ a b 1 f

def DetShiftNorm : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    fockQ (detX N * hw ℚ le_rfl ν) (detX N * hw ℚ le_rfl ν) =
      (∏ i : Fin N, ((ν i + N - i : ℕ) : ℚ)) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)

def HookNorm : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) *
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((ν i - ν j + (j - i) : ℕ) : ℚ) =
      ∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℚ)

def DetShiftNormOf : Prop := DetAdj → DetDetId → PolEqRowDiv → HwDetMul → DetShiftNorm

def HookNormOf : Prop := RenameIso → HwDetMul → HwLastZero → DetShiftNorm → HookNorm

def HookBoundOf : Prop := HookNorm → PI.HookBound

end PI.HookSteps
