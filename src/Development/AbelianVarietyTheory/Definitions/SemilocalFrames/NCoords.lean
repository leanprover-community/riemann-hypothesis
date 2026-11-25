module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Formalism.FormalDegreeBessel.StatementBF
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass

section Ring

variable {A : Type} [CommRing A]

def sideM {n a b : ℕ} (P : Matrix (Fin n) (Fin a) A) (Q : Matrix (Fin n) (Fin b) A) :
    Matrix (Fin n) (Fin (a + b)) A := fun i => Fin.append (P i) (Q i)

end Ring

section Glob

variable {E : Type} [Field E] [NumberField E]

def id1 (E : Type) [Field E] [NumberField E] (r : ℕ) : Fin (r + 1 + r) → FractionalIdeal (𝓞 E)⁰ E :=
  Fin.append (fun b : Fin (r + 1) => dInv E (r - (b : ℕ))) fun b : Fin r => (dInv E (r - (b : ℕ)))⁻¹

def Adapted {k r : ℕ} (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E)
    (s : Fin r → ℝ) : Prop :=
  ∀ (w : InfinitePlace E) (a : Fin r),
    (A w).mulVec (fun i => w.embedding (P i a.castSucc)) = (s a : ℂ) • bvec (eI k r a) ∧
    (A w).mulVec (fun i => w.embedding (f i a)) = ((s a)⁻¹ : ℂ) • bvec (esI k r a)

variable {F : Type} [Field F] [NumberField F] [Algebra F E]


end Glob

end GlobalTheory.SnMass
