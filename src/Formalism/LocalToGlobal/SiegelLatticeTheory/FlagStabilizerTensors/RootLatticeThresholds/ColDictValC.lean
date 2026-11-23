module

public import Formalism.LocalRingCardinality.DataCoeff
public import Mathlib.LinearAlgebra.Matrix.PosDef
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.Params

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.ColDictPf

open Formalism.BasicNotions Matrix
open scoped ComplexOrder

section Copies

variable {ι : Type} [Fintype ι]

def tenV {R : Type} [CommRing R] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) R) :
    MvPolynomial (ι × Fin n × Fin n) R :=
  ∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)

def CSpanV {n : ℕ} (lam : ι → DomWeight n) : Submodule ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℂ, (∀ τ, f τ ∈ delSq ℂ n (lam τ)) ∧ p = tenV f}

variable {n : ℕ}

def FramesV (_G : ι → Matrix (Fin n) (Fin n) ℂ) : Type :=
  {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det}

def fnOfV (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₗ[ℂ] (FramesV G → ℂ) where
  toFun P := fun y => (∏ τ, (M τ * y.1 τ).det ^ s τ) *
    MvPolynomial.eval (fun x : ι × Fin n × Fin n => (M x.1 * y.1 x.1) x.2.1 x.2.2) P
  map_add' P Q := by funext y; simp [mul_add]
  map_smul' c P := by funext y; simp [MvPolynomial.smul_eval]; ring

def shiftOfV (lam : ι → DomWeight n) : ι → ℤ := fun τ => (lam τ).detShift

def ValCV (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) : Submodule ℂ (FramesV G → ℂ) :=
  (CSpanV lam).map (fnOfV G (shiftOfV lam) 1)

end Copies

def ValCIrr : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (G : ι → Matrix (Fin n) (Fin n) ℂ),
    (∀ τ, (G τ).PosDef ∨ (-G τ).PosDef) →
    ∀ (lam : ι → DomWeight n) (W : Submodule ℂ (FramesV G → ℂ)), W ≤ ValCV G lam → W ≠ ⊥ →
      (∀ g : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (g τ)ᴴ * G τ * g τ = G τ) →
        ∀ F ∈ W, ∃ F' ∈ W, ∀ y y' : FramesV G, (∀ τ, y'.1 τ = g τ * y.1 τ) → F' y = F y') →
      W = ValCV G lam

end Formalism.L2.SG.Pf.ColDictPf
