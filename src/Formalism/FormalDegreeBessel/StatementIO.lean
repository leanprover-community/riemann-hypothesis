module

public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Formalism.RealPlaceAnalysis.StatementE

@[expose] public section

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Top (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (u : ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => (if a = b then u • f g else 0) + Eop a b f g

def qminorOp {t : ℕ} (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun k : Fin t => Top Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).foldr (fun T h => T h) f)

def qdetOp (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  qminorOp Eop id id u f

def capelli (ε : Fin n → Bool) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  qdetOp (EabV ε) u f

def inUH (H g : Matrix (Fin n) (Fin n) ℂ) : Prop := gᴴ * H * g = H

def SmoothOnH (H : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀, inUH H g₀ → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, inUH H g → f g = F g

def hpart1 (H Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Z - H⁻¹ * Zᴴ * H)

def hpart2 (H Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I) : ℂ) • (Z + H⁻¹ * Zᴴ * H)

def EabH (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => RdV (hpart1 H (Matrix.single a b 1)) f g + Complex.I • RdV (hpart2 H (Matrix.single a b 1)) f g

def capelliH (H : Matrix (Fin n) (Fin n) ℂ) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  qdetOp (EabH H) u f

def GlRelAd : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ),
    GlRel E → Q * P = 1 →
    GlRel (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d)

end Formalism.QuantumDeterminants
