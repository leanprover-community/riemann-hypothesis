module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
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

open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.QuantumDeterminants

abbrev PairSp (k r : ℕ) := (Mt k r × Mt k r) × (Mt k r × Mt k r)

section Orb

variable {k r : ℕ}

def besselIntg (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p : PairSp k r) : L.Wq →L[ℂ] L.Wp :=
  (psi k r L.z L.c (Matrix.of p.1.2) * star (psi k r L.z' L.c (Matrix.of p.2.2))) •
    ((L.π (Matrix.of p.1.1)).comp
      ((F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1)).comp
        (L.π' (Matrix.of p.2.1)⁻¹)))

def pairMeas (L : LocBessel k r) : Measure (PairSp k r) := (L.μW.prod L.μN).prod (L.μW'.prod L.μN)

def RStab (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {a | a ∈ Nset k r ∧ g⁻¹ * a * g ∈ Nset k r}

def stabAct (g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p : PairSp k r) : PairSp k r :=
  ((p.1.1, fun i j => (a * Matrix.of p.1.2) i j), (p.2.1, fun i j => (g⁻¹ * a * g * Matrix.of p.2.2) i j))

def flagMat (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := fun i j =>
  if hi : i.val < r then (a *ᵥ fvec k r z j) (eI k r ⟨i.val, hi⟩) else (if i = j then 1 else 0)

def blockIdx : List (ℂ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (_, s) :: bs, p => if p < s then 0 else 1 + blockIdx bs (p - s)

def rootPat {r : ℕ} (γ : Point ℂ (r + 1)) : Finset (Fin (r + 1) × Fin (r + 1)) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ blockIdx γ.1 p.1.val = blockIdx γ.1 p.2.val

def rootCoords (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (γ : Point ℂ (r + 1)) (x : Mt k r) :
    (rootPat γ) → ℂ := fun p => flagMat k r z (Matrix.of x) p.1.1 p.1.2

def IsRootMeas (L : LocBessel k r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : Measure (Mt k r)) : Prop :=
  μR {x | Matrix.of x ∉ RStab k r g} = 0 ∧
    μR.map (rootCoords k r L.z γ) = ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card) • volume

def IsOrbQuot (L : LocBessel k r) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)) : Prop :=
  ∀ f : PairSp k r → ENNReal, Measurable f →
    ∫⁻ x, f x ∂(pairMeas L) = ∫⁻ x, (∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR) ∂ν

def IsRelStab (L : LocBessel k r) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ a ∈ RStab k r g, psi k r L.z L.c a = psi k r L.z' L.c (g⁻¹ * a * g)

def OrbInt (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ν : Measure (PairSp k r)) : L.Wq →L[ℂ] L.Wp :=
  ∫ x, besselIntg L F g x ∂ν

def IsPtRep (L : LocBessel k r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  g ∈ UH (Hpk k r) ∧ Zhat k r L.z L.z' g = ptMat γ

def ZhatO (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun a b => (-1 : ℂ) ^ (r - b.val) * Zhat k r z z' g a b

def IsPtRepO (L : LocBessel k r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  g ∈ UH (Hpk k r) ∧ ZhatO k r L.z L.z' g = ptMat γ

end Orb

def OrbRStabBig : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    (∀ a, c a ≠ 0) → μᴴ * Hb k * μ = Hb k → RStab k r (bigCell k r c μ) = {1}

end Formalism.MainNotions.S
