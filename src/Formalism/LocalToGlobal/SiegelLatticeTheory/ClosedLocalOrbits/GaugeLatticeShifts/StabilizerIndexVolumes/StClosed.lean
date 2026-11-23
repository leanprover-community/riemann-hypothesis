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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def IntE (x : E) : Prop := ∃ o : 𝓞 E, (o : E) = x

def StSet (W : Matrix (Fin n) (Fin n) E) : Set (Matrix.GeneralLinearGroup (Fin n) E) :=
  {a | Formalism.MainNotions.S.IsLoUni (a : Matrix (Fin n) (Fin n) E) ∧ ∃ b : Matrix (Fin n) (Fin n) E,
    Formalism.MainNotions.S.IsUpUni b ∧ (a : Matrix (Fin n) (Fin n) E) * W * b = W}

def BddDen (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) E)) : Prop :=
  ∃ N : ℕ, N ≠ 0 ∧ ∀ h ∈ H, ∀ i j, IntE ((N : E) * (h : Matrix (Fin n) (Fin n) E) i j)

def CongIn (W : Matrix (Fin n) (Fin n) E) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) E)) : Prop :=
  ∃ N : ℕ, N ≠ 0 ∧ ∀ a : Matrix.GeneralLinearGroup (Fin n) E, a ∈ StSet W →
    (∀ i j, IntE (((a : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) / (N : E))) → a ∈ H

def StClosed : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (W : Matrix (Fin n) (Fin n) E),
    (1 : Matrix.GeneralLinearGroup (Fin n) E) ∈ StSet W ∧
    (∀ a ∈ StSet W, ∀ b ∈ StSet W, a * b ∈ StSet W) ∧ (∀ a ∈ StSet W, a⁻¹ ∈ StSet W)

def Commens : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (W : Matrix (Fin n) (Fin n) E)
    (H K : Subgroup (Matrix.GeneralLinearGroup (Fin n) E)),
    (H : Set (Matrix.GeneralLinearGroup (Fin n) E)) ⊆ StSet W → BddDen H → CongIn W K → K.relIndex H ≠ 0

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
