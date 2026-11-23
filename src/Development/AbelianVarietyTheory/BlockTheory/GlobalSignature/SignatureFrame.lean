module

public import Formalism.LocalRingCardinality.DataCD
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SignatureFrame

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

structure SignFrame {n : ℕ} (ε : Fin n → Bool) (P Q : ℕ) where

  e : Fin P ⊕ Fin Q ≃ Fin n
  pos : ∀ i, ε (e (Sum.inl i)) = true
  neg : ∀ j, ε (e (Sum.inr j)) = false

variable {n P Q : ℕ} {ε : Fin n → Bool}

theorem SignFrame.reindex_J (F : SignFrame ε P Q) :
    Matrix.reindex F.e F.e (Formalism.UG.Jpq P Q) = Jm ε := by
  ext a b
  obtain ⟨x, rfl⟩ := F.e.surjective a
  obtain ⟨y, rfl⟩ := F.e.surjective b
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Formalism.UG.Jpq, Jm, Matrix.diagonal_apply, Matrix.one_apply, F.pos, F.neg]
  split_ifs <;> simp

def SignFrame.unitsMap (F : SignFrame ε P Q) :
    GL (Fin P ⊕ Fin Q) ℂ →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  Units.map (Matrix.reindexAlgEquiv ℂ ℂ F.e).toMulEquiv.toMonoidHom

theorem SignFrame.inUJ_reindex (F : SignFrame ε P Q)
    (m : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    inUJ ε (Matrix.reindex F.e F.e m) ↔
      Formalism.UG.cT (starRingEnd ℂ) m * Formalism.UG.Jpq P Q * m = Formalism.UG.Jpq P Q := by
  unfold inUJ
  rw [← F.reindex_J]
  have h : Formalism.UG.cT (starRingEnd ℂ) m = mᴴ := by
    ext i j; simp [Formalism.UG.cT]
  rw [h]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact (Matrix.reindex F.e F.e).injective.eq_iff (a := mᴴ * Formalism.UG.Jpq P Q * m) (b := Formalism.UG.Jpq P Q)

def SignFrame.toDiag (F : SignFrame ε P Q) (g : UpqT P Q) : UJ ε :=
  let g' : Formalism.UG.Upq P Q := g
  ⟨F.unitsMap g'.1, (F.inUJ_reindex _).2 g'.2⟩

def cdMeasure (c : CDHaar) (F : SignFrame ε P Q) : Measure (UJ ε) :=
  Measure.map F.toDiag (c.cd P Q)

def dimV {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  (∏ a : Fin n, ∏ b ∈ Ioi a, (lam a - lam b)) /
    ∏ a : Fin n, ∏ b ∈ Ioi a, (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))

end GlobalTheory.IndefiniteRowSideFullHecke.SignatureFrame
