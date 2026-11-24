module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.BetaFun
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open Matrix GlobalTheory.PRep

namespace GlobalTheory.BZMir.Fun

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def SmPsiMinus : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), IsSmooth τ → IsSmooth (psiMinus k τ)

def SmPhiMinus : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (n + 1)) V),
    IsSmooth τ → IsSmooth (phiMinus k ψ τ)

def Exhaust : Prop :=
  ∀ (n : ℕ) (s : Finset (Mir k n)), (↑s : Set (Mir k n)) ⊆ MirUin k n →
    ∃ L : Subgroup (Mir k n), L ≤ MirUin k n ∧ (↑s : Set (Mir k n)) ⊆ L ∧ IsCompact (L : Set (Mir k n))

def ThetaOpen : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (a : Fin n → k), IsOpen ((thetaA k ψ a).ker : Set (MirUin k n))

def MirCharEq : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ), mirChar k ψ n = thetaA k ψ (Pi.single (Fin.last n) 1)

def ThetaConj : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (a : Fin n → k) (m : GL (Fin n) k) (u : MirUin k n),
    ∃ h : levi k n m * (u : Mir k n) * (levi k n m)⁻¹ ∈ MirUin k n,
      thetaA k ψ (vecMul a (m : Matrix (Fin n) (Fin n) k)) u = thetaA k ψ a ⟨_, h⟩

def TwKerConj : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (a : Fin n → k) (m : GL (Fin n) k) (v : V),
    v ∈ twKer τ (MirUin k n) (thetaA k ψ (vecMul a (m : Matrix (Fin n) (Fin n) k))) ↔
      τ (levi k n m) v ∈ twKer τ (MirUin k n) (thetaA k ψ a)

def Fourier : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V), IsSmooth τ → ∀ v : V,
      (∀ a : Fin n → k, v ∈ twKer τ (MirUin k n) (thetaA k ψ a)) → v = 0

def ExPsiMinus : Prop :=
  ∀ (n : ℕ) (V₁ V₂ V₃ : Type) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃]
    [Module ℂ V₃] (τ₁ : Representation ℂ (Mir k n) V₁) (τ₂ : Representation ℂ (Mir k n) V₂)
    (τ₃ : Representation ℂ (Mir k n) V₃), IsSmooth τ₁ → IsSmooth τ₂ → IsSmooth τ₃ →
    ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (τ₁ x v) = τ₂ x (f v)) (hg : ∀ x v, g (τ₂ x v) = τ₃ x (g v)),
      LinearMap.range f = LinearMap.ker g →
      LinearMap.range (twMap τ₁ τ₂ (MirUin k n) 1 f hf) = LinearMap.ker (twMap τ₂ τ₃ (MirUin k n) 1 g hg)

def ExPhiMinus : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V₁ V₂ V₃ : Type) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] (τ₁ : Representation ℂ (Mir k (n + 1)) V₁)
    (τ₂ : Representation ℂ (Mir k (n + 1)) V₂) (τ₃ : Representation ℂ (Mir k (n + 1)) V₃),
    IsSmooth τ₁ → IsSmooth τ₂ → IsSmooth τ₃ →
    ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (τ₁ x v) = τ₂ x (f v)) (hg : ∀ x v, g (τ₂ x v) = τ₃ x (g v)),
      LinearMap.range f = LinearMap.ker g →
      LinearMap.range (twMap τ₁ τ₂ (MirUin k (n + 1)) (mirChar k ψ n) f hf) =
        LinearMap.ker (twMap τ₂ τ₃ (MirUin k (n + 1)) (mirChar k ψ n) g hg)

def BetaInd : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (n + 1)) V)
    (v : V), betaFun ψ τ v ∈ indSpace (Q k n) (qRep k ψ (phiMinus k ψ τ))

def BetaSmooth : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (n + 1)) V),
    IsSmooth τ → ∀ v : V, IsOpen {g : Mir k (n + 1) | ∀ x, betaFun ψ τ v (x * g) = betaFun ψ τ v x}

def BetaCompact : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V), IsSmooth τ → ∀ v ∈ twKer τ (MirUin k (n + 1)) 1,
      ∃ C : Set (Mir k (n + 1)), IsCompact C ∧ ∀ g, betaFun ψ τ v g ≠ 0 → ∃ h ∈ Q k n, ∃ c ∈ C, g = h * c

end GlobalTheory.BZMir.Fun

end
