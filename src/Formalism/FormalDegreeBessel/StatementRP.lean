module

public import Formalism.FormalDegreeBessel.StatementBF
public import Formalism.FormalDegreeBessel.StatementIO
public import Formalism.FormalDegreeBessel.StatementWR

@[expose] public section

open scoped ContDiff
open MeasureTheory Matrix

noncomputable section

namespace Formalism.QuantumDeterminants

def levPos (k i r' : ℕ) (j : Fin (2 * r' + k + 1)) : Fin (2 * (i + r') + k + 1) := ⟨j.val + i, by omega⟩

def ιLev (k i r' : ℕ) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ := fun p q =>
  if hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then
    (if hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i then g ⟨p.val - i, by omega⟩ ⟨q.val - i, by omega⟩ else 0)
  else (if p = q then 1 else 0)

def liftVec (k i r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) : Fin (2 * (i + r') + k + 1) → ℂ := fun p =>
  if hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then v ⟨p.val - i, by omega⟩ else 0

def LevHom : Prop :=
  ∀ k i r' : ℕ, ιLev k i r' 1 = 1 ∧
    ∀ g h : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ,
      ιLev k i r' (g * h) = ιLev k i r' g * ιLev k i r' h

def LevUH : Prop :=
  ∀ (k i r' : ℕ) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ),
    g ∈ UH (Hpk k r') → ιLev k i r' g ∈ UH (Hpk k (i + r'))

def LevN : Prop :=
  ∀ (k i r' : ℕ) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ),
    g ∈ Nset k r' → ιLev k i r' g ∈ Nset k (i + r')

def LevUW : Prop :=
  ∀ (k i r' : ℕ) (z : Fin (2 * r' + k + 1) → ℂ) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ),
    g ∈ UWset k r' z → ιLev k i r' g ∈ UWset k (i + r') (liftVec k i r' z)

def LevWb : Prop :=
  ∀ (k i r' : ℕ) (z : Fin (2 * r' + k + 1) → ℂ), inWb k r' z →
    inWb k (i + r') (liftVec k i r' z) ∧ Tz k (i + r') (liftVec k i r' z) = Tz k r' z

def LevEll : Prop :=
  ∀ (k i r' : ℕ) (z : Fin (2 * r' + k + 1) → ℂ) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ),
    ell k (i + r') (liftVec k i r' z) (ιLev k i r' g) = ell k r' z g

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

def wbPart (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

def IsSection (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Prop :=
  (∀ i j : Fin (k + 1), ContDiffOn ℝ ∞ (fun ζ => μsec ζ i j) {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
    Matrix.conjTranspose (μsec ζ) * Hb k * μsec ζ = Hb k ∧ herm (Hb k) (μsec ζ *ᵥ wbPart k r z') (wbPart k r z) = ζ

def SectionExists : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' →
    0 < Tz k r z → 0 < Tz k r z' → ∃ μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsSection k r z z' μsec

abbrev Op (m : ℕ) (E : Type*) := ((Fin m → ℂ) → E) → (Fin m → ℂ) → E

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Tmat {m : ℕ} (l : Fin m) (Y : ℂ) : Matrix (Fin 2) (Fin 2) (Op m E) :=
  Matrix.of ![![fun f => Y • f + pOp l f, fun f => -(cOp l f)], ![ciOp l, fun _ => 0]]

def TmatStar {m : ℕ} (l : Fin m) (Y : ℂ) : Matrix (Fin 2) (Fin 2) (Op m E) :=
  Matrix.of ![![fun f => Y • f - pbOp l f, cbiOp l], ![fun f => -(cbOp l f), fun _ => 0]]

end Formalism.QuantumDeterminants
