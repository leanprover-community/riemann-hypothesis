module

public import Formalism.HermitianCurvature.StatementQ
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField

@[expose] public section

open Formalism.FourierDecayAlt MeasureTheory NumberField

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.Gr

noncomputable section

section cls

variable {r : ℕ} {TT : ℝ}

def smM (m : ℕ∞) : WithTop ℕ∞ := ((m : ℕ∞) : WithTop ℕ∞)

end cls

section jets

variable {r : ℕ} {TT : ℝ}


end jets

section ord

variable {r : ℕ} {TT : ℝ}

end ord

section En

variable (P : M.Par) (m : ℕ∞)

end En

open scoped Matrix.Norms.Elementwise

def FFlM {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (m : ℕ∞) (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (i : Fin (r + 1)) (Dm : Set (Q.Mx k r)) : Set (Q.Mx k r → (Wq →L[ℂ] Wp)) :=
  {J | (∀ g₀ ∈ Q.Glev k r i ∩ Dm, ∃ (U : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)),
      IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ (smM m) F U ∧ ∀ g ∈ U, g ∈ Q.Glev k r i → J g = F g) ∧
    Q.LeftEq k r z i Dm J ∧ Q.RightEq k r z' i Dm J ∧
    ∀ g ∈ Q.Glev k r i ∩ Dm, ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset k r z',
      J (h * g * h') = (π h).comp ((J g).comp (π' h'))}

section place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

end place

end

end Formalism.FourierDecayAlt.P.CutMP.Gr
