module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

def pos (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k

abbrev UTr (r : ℕ) : Type := {p : Fin r × Fin r // p.1 < p.2}

abbrev Bk (r : ℕ) : Type := UTr r ⊕ Fin r ⊕ UTr r ⊕ Fin r

def VM (k r : ℕ) : Bk r → Type
  | .inl _ => ℂ
  | .inr (.inl _) => Fin (k + 1) → ℂ
  | .inr (.inr (.inl _)) => ℂ
  | .inr (.inr (.inr _)) => ℝ

instance instVM (k r : ℕ) : ∀ β, AddCommGroup (VM k r β)
  | .inl _ => inferInstanceAs (AddCommGroup ℂ)
  | .inr (.inl _) => inferInstanceAs (AddCommGroup (Fin (k + 1) → ℂ))
  | .inr (.inr (.inl _)) => inferInstanceAs (AddCommGroup ℂ)
  | .inr (.inr (.inr _)) => inferInstanceAs (AddCommGroup ℝ)

def cM (k r : ℕ) : ∀ β : Bk r, Mt k r → VM k r β
  | .inl p, x => x (eI k r p.1.1) (eI k r p.1.2)
  | .inr (.inl a), x => fun j => x (eI k r a) (wI k r j)
  | .inr (.inr (.inl p)), x => x (eI k r p.1.1) (esI k r p.1.2)
  | .inr (.inr (.inr a)), x => (x (eI k r a) (esI k r a)).im

section Glob

variable {E : Type} [Field E] [NumberField E]

def gM {k r : ℕ} (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (w : InfinitePlace E) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  A w * γ.map w.embedding * (A w)⁻¹

def actM {k r : ℕ} (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (x : InfinitePlace E → Mt k r) :
    InfinitePlace E → Mt k r :=
  fun w => Matrix.of.symm (A w * γ.map w.embedding * (A w)⁻¹ * Matrix.of (x w))

end Glob

section Bundle

variable {E : Type} [Field E] [NumberField E]

def IsVolData {F : Type} [Field F] [NumberField F] [Algebra F E] (σ : E →ₐ[F] E) {k r : ℕ}
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E))
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) : Prop :=
  IsCMExt F E σ ∧ Algebra.FormallyUnramified (𝓞 F) (𝓞 E) ∧ IsHermND σ J ∧
    GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ ∧ IsFrame (σ : E →+* E) J (algebraMap F E T) P ∧
    IsDual (σ : E →+* E) J P f ∧ tupLat (id1 E r) (sideM P f) ≤ Λ ∧ IsModelAt J A ∧ (∀ a, 0 < s a) ∧
    Adapted A P f s

end Bundle

end GlobalTheory.SnMass.VolN
