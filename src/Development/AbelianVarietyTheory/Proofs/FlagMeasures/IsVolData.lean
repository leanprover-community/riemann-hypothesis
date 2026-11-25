module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Mathlib.RingTheory.PiTensorProduct
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

end GlobalTheory.SnMass.VolN
