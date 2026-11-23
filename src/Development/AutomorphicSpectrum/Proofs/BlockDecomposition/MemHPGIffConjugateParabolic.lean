module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem wGL_conj_apply (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k) (a b : Fin (i + t + 1)) :
    ((wGL k h * g * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) a b =
      (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (wPerm h a) (wPerm h b) := by
  have e1 : ((wGL k h : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix (wPerm h) id := rfl
  have e2 : (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix id (wPerm h) := rfl
  rw [Units.val_mul, Units.val_mul, e1, e2]
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem wPerm_two {i t : ℕ} (h : (i + 1) + t = i + t + 1) (x : Σ x, Two (Fin (i + 1)) (Fin t) x) :
    wPerm h (two (stdSum h) x) = ePG i t x := by
  simp [wPerm]

theorem mem_HPG_iff_conj_mem_parab (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (p : Mir k (i + t)) :
    p ∈ HPG k i t ↔ wGL k h * (p : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h)) := by
  show (p : GL (Fin (i + t + 1)) k) ∈ parab k (ePG i t) ↔ _
  rw [mem_parab_iff, mem_parab_iff]
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun x => forall_congr' fun y => ?_
  rw [wGL_conj_apply, wPerm_two, wPerm_two]

end GlobalTheory.CompanionTheory.BZRes
