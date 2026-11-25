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

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def sLd {m : ℕ} (L : GR n → ((Fin m → Fin n → ℂ) → ℂ) → ((Fin m → Fin n → ℂ) → ℂ)) (c : ℝ) (P : PX m n) (y : GR n) : ℂ :=
  L y (fP c P) 0

def pqOf {m : ℕ} (ε : Fin m → Bool) (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : ℕ × ℕ :=
  if 0 < l τ then (cnt ε true, cnt ε false) else (cnt ε false, cnt ε true)

def LIl : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → l τ ≠ 0

def LIlin : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    (∀ (y : GR n) (a : ℂ) (P Q : PX V.rank n), L y (fP (cLoc l τ) (a • P + Q)) = a • L y (fP (cLoc l τ) P) + L y (fP (cLoc l τ) Q)) ∧
    ∀ P : PX V.rank n, L 1 (fP (cLoc l τ) P) = fP (cLoc l τ) P

def LIlaw : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ e : ℤ, ∀ (P : PX V.rank n) (y g : GR n), (mR y).toBlocks₂₁ = 0 →
      sLd L (cLoc l τ) P (y * g) = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e y * sLd L (cLoc l τ) P g

def LIcell : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ C : ℂ, C ≠ 0 ∧ ∀ (P : PX V.rank n) (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b →
      sLd L (cLoc l τ) P g = C * secN ε (cLoc l τ) (tLoc l τ) P b

def LIcont : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ P : PX V.rank n, Continuous (sLd L (cLoc l τ) P)

def LIrho : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n, (∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P)) ∧
      ∀ P, ∃ W : Submodule ℂ (PX V.rank n), FiniteDimensional ℂ W ∧ P ∈ W ∧ (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) ∧
        ∀ Q ∈ W, ∀ l' : PX V.rank n →ₗ[ℂ] ℂ, ContinuousOn (fun k : GR n => l' (ρ k Q)) {k | InK (mR k)}

def LIkact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n, (∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P)) →
      ∀ P (g k : GR n), InK (mR k) → sLd L (cLoc l τ) P (g * k) = sLd L (cLoc l τ) (ρ k P) g

def LIvac : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ), 0 < c →
    ((t = c ∧ p = cnt ε true ∧ q = cnt ε false) ∨ (t = -c ∧ p = cnt ε false ∧ q = cnt ε true)) →
    ∀ (S : GR n → ℂ) (C : ℂ), Continuous S → S 1 = 1 →
      (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → S (y * g) = F0 p q e y * S g) →
      (∀ (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b → S g = C * secN ε c t (1 : PX m n) b) →
      ∀ g, S g = F0 p q e g

def LIkvac : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ e : ℤ, (∀ g : GR n, sLd L (cLoc l τ) 1 g = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e g) →
    ∀ k : GR n, InK (mR k) → L k (fP (cLoc l τ) 1) = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e k • fP (cLoc l τ) 1

end PositivityTheory.Rg.Sw.Glob
