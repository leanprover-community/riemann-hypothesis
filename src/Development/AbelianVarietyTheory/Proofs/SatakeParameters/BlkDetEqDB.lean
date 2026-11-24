module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism.L2.Col

namespace GlobalTheory.TopLaw

theorem blkDet_eq_dB : ∀ {κ : Type} [CommRing κ] {n : ℕ} (β : ℕ → ℕ) (c s t : ℕ), s + t ≤ n → (∀ i, i < n → (β i = c ↔ s ≤ i ∧ i < s + t)) → ∀ (M : btG n κ β) (A : ℕ → ℕ → κ), (∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) → ((blkDet n κ β c M : κˣ) : κ) = GlobalTheory.DatumLaw.dB A s t := by
  intro κ _ n β c s t hn hβ M A hA
  rw [blkDet_val]
  unfold GlobalTheory.DatumLaw.dB
  let e : Fin t ≃ {i : Fin n // β i.1 = c} :=
    { toFun := fun u => ⟨⟨s + u.1, by have := u.2; omega⟩, (hβ _ (by have := u.2; omega)).2 ⟨by simp, by have := u.2; simp⟩⟩
      invFun := fun i => ⟨i.1.1 - s, by have := (hβ _ i.1.2).1 i.2; omega⟩
      left_inv := fun u => Fin.ext (by simp)
      right_inv := fun i => Subtype.ext (Fin.ext (by have := (hβ _ i.1.2).1 i.2; simp only; omega)) }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext u v
  exact (hA (e u).1 (e v).1).symm

end GlobalTheory.TopLaw
