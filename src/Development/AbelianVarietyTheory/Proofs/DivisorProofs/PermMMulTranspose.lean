module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CovTop.VolUp

open NumberField MeasureTheory Matrix Formalism.BasicNotions GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

def dg {ι : Type} [DecidableEq ι] (a₀ : ι) (z : ℂ) : Matrix ι ι ℂ := Matrix.diagonal (Function.update 1 a₀ z)

def sMat {p q : ℕ} (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  UpqT.mat u * dg a₀ (UpqT.mat u).det⁻¹

def permM {ι : Type} {r : ℕ} (e : ι ≃ Fin r) : Matrix ι (Fin r) ℂ := Matrix.of fun i j => if e i = j then 1 else 0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def frBall (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (ε : ℝ) : Set (realSU Ψ G) :=
  {s | ∀ τ a b, ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε}

def IsIdent {κ : Type} (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) : Prop :=
  ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ = -(G.map (σ ρ).1)ᵀ ∧ A ρ * mat x (σ ρ) = permM (e ρ)

def IsProj {κ : Type} (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ))
    (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) : Prop :=
  ∀ b ρ, A ρ * (((π b).1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = sMat (a₀ ρ) (b ρ) * A ρ

section Adelic

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum GlobalTheory.AdelicScalar

def IsRealPart {D : D7} (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V → ∀ ρ, Upq V ρ) : Prop :=
  ∀ h ρ, UpqT.mat (rp h ρ) * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h

end Adelic

theorem permM_mul_transpose {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin r) : permM e * (permM e)ᵀ = 1 := by
  ext i j
  simp [permM, Matrix.mul_apply, Matrix.one_apply, eq_comm]

theorem transpose_mul_permM {ι : Type} [Fintype ι] (e : ι ≃ Fin r) : (permM e)ᵀ * permM e = 1 := by
  ext i j
  rw [Matrix.mul_apply, ← e.symm.sum_comp]
  simp [permM, Matrix.one_apply, eq_comm]

theorem det_dg {ι : Type} [Fintype ι] [DecidableEq ι] (a₀ : ι) (z : ℂ) : (dg a₀ z).det = z := by
  rw [dg, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

end GlobalTheory.CovTop.VolUp
