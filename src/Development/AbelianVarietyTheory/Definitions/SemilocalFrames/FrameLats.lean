module

public import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob

variable {E : Type} [Field E] [NumberField E]

def dInv (E : Type) [Field E] [NumberField E] (j : ℕ) : FractionalIdeal (𝓞 E)⁰ E :=
  ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹) ^ j

def SelfDual (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  Λ.FG ∧ ∀ v, v ∈ Λ ↔ ∀ w ∈ Λ, form σ J v w ∈ (algebraMap (𝓞 E) E).range

def frameLat {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ (b : Fin (r + 1)) (a : E), a ∈ dInv E (r - (b : ℕ)) ∧ v = a • fun i => P i b}

def PrimIn {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  M ≤ Λ ∧ ∀ v ∈ Λ, v ∈ Submodule.span E (M : Set (Fin n → E)) → v ∈ M

def pairLat {n r : ℕ} (g : ℕ) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  frameLat P ⊔ frameLat (((g : E)⁻¹) • (P' - P))

def latMap {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ.map (γ.mulVecLin.restrictScalars (𝓞 E))

abbrev Tri (E : Type) [Field E] [NumberField E] (n r : ℕ) : Type :=
  Submodule (𝓞 E) (Fin n → E) × Matrix (Fin n) (Fin (r + 1)) E × Matrix (Fin n) (Fin (r + 1)) E

def FrameLats (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Submodule (𝓞 E) (Fin n → E)) :=
  {Λ | SelfDual σ J Λ ∧ PrimIn (frameLat P) Λ}

end GlobalTheory.SgGlob
