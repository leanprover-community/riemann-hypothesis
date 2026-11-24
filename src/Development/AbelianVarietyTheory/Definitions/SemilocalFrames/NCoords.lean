module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Formalism.FormalDegreeBessel.StatementBF
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass

def nCoords (k r : ℕ) (x : Mt k r) :
    ({p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) // p.1.val < r ∧ p.1 < p.2 ∧ p.2.val ≤ r + k} → ℂ) ×
      ({p : Fin r × Fin r // p.1 < p.2} → ℂ) × (Fin r → ℝ) :=
  (fun p => x p.1.1 p.1.2, fun p => x (eI k r p.1.1) (esI k r p.1.2), fun a => (x (eI k r a) (esI k r a)).im)

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

def IsDomN (σ : E →+* E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (𝓓 : Set (InfinitePlace E → Mt k r)) : Prop :=
  MeasurableSet 𝓓 ∧ ∀ x : InfinitePlace E → Mt k r, (∀ w, Matrix.of (x w) ∈ Nset k r) →
    ∃! γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E, (InN σ J P γ ∧ latMap γ Λ = Λ) ∧
      (fun w => Matrix.of.symm (A w * γ.map w.embedding * (A w)⁻¹ * Matrix.of (x w))) ∈ 𝓓

variable {F : Type} [Field F] [NumberField F] [Algebra F E]


end Glob

end GlobalTheory.SnMass
