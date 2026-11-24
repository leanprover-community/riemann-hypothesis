module

public import Formalism.PeriodIntegrals.AlgValsFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1

namespace PI.AlgValsFin.W

variable (L : Type) [Field L] [NumberField L]

def UFin : Set (Ideles L) :=
  {x | (x : AdeleRing (𝓞 L) L).1 = 1 ∧
    ∀ v : HeightOneSpectrum (𝓞 L), Valued.v ((x : AdeleRing (𝓞 L) L).2 v) = 1}

def TorsUnits : Prop :=
  ∀ χ : HChar L, ∃ N : ℕ, 0 < N ∧ ∀ x ∈ UFin L, (χ.1 x) ^ N = 1

def Decomp : Prop :=
  ∀ (k : Lˣ) (T : Finset (HeightOneSpectrum (𝓞 L))), (∀ v, v ∉ T → ordF v k = 0) →
    ∃ r ∈ UFin L, diagUnits L k = infDiag k * (∏ v ∈ T, localIdele L v (atFin v k)) * r

def LocVal : Prop :=
  ∀ (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ), χ.UnrAt v →
    χ.loc v (atFin v k) = χ.val v ^ ordF v k

def ProdNorm : Prop :=
  ∀ (k : Lˣ) (T : Finset (HeightOneSpectrum (𝓞 L))), (∀ v, v ∉ T → ordF v k = 0) →
    ∏ φ : L →+* ℂ, ‖φ (k : L)‖ = ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ordF v k


open scoped Classical in
open Classical in
def ClassPow : Prop :=
  ∃ h : ℕ, 0 < h ∧ ∀ v : HeightOneSpectrum (𝓞 L), ∃ k : Lˣ,
    ∀ u : HeightOneSpectrum (𝓞 L), ordF u k = if u = v then (h : ℤ) else 0


open scoped Classical in
open Classical in
def ClassSame : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (c : HeightOneSpectrum (𝓞 L) → ι),
    ∀ v w, c v = c w → ∃ k : Lˣ, ∀ u : HeightOneSpectrum (𝓞 L),
      ordF u k = (if u = v then 1 else 0) - (if u = w then 1 else 0)

def KeyId : Prop :=
  ∀ (χ : HChar L) (s : ℝ) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) * ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ) =
      ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∀ (k : Lˣ) (T : Finset (HeightOneSpectrum (𝓞 L))), (∀ v, v ∉ T → ordF v k = 0) →
      (∀ v ∈ T, χ.UnrAt v) →
      ∃ r ∈ UFin L, (∏ v ∈ T, χ.valTw s v ^ ordF v k) * (∏ φ : L →+* ℂ, φ (k : L) ^ m φ) *
        ((χ.1 r : ℂˣ) : ℂ) = 1

def KeyIdOf : Prop := Decomp L → LocVal L → ProdNorm L → KeyId L

def Assemble : Prop := TorsUnits L → KeyId L → ClassPow L → ClassSame L → AlgValsFin L

end PI.AlgValsFin.W
