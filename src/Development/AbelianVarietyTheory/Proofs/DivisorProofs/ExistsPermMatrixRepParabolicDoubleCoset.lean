module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism

@[expose] public section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.FinGL.Bruhat

theorem exists_perm_rep_blockTri : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ), Monotone b → Monotone b' → ∀ g : GL (Fin r) F, ∃ (w : Equiv.Perm (Fin r)) (p' : blockTri (κ := F) b') (p : blockTri (κ := F) b), g = (p' : GL (Fin r) F) * permGL F w * (p : GL (Fin r) F) := by
  intro F _ r b b' hb hb' g
  have hle : ∀ (c : Fin r → ℕ), Monotone c → ∀ u ∈ unip F r, u ∈ blockTri (κ := F) c := by
    intro c hc u hu
    rw [mem_blockTri]
    intro i j hij
    exact unip_lower hu (lt_of_not_ge fun h => absurd (hc h) (not_le.2 hij))
  obtain ⟨m, u, hu, u', hu', h⟩ := exists_decomp g
  have hdet : (Matrix.diagonal fun c => (m.2 c : F)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun c _ => (m.2 c).ne_zero
  let d : GL (Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hdv : (d : Matrix (Fin r) (Fin r) F) = Matrix.diagonal fun c => (m.2 c : F) := rfl
  have hd : d ∈ blockTri (κ := F) b := by
    rw [mem_blockTri]
    intro i j hij
    rw [hdv]
    exact Matrix.diagonal_apply_ne _ (fun e => by rw [e] at hij; exact lt_irrefl _ hij)
  have hm : mono m = (permGL F m.1 : Matrix (Fin r) (Fin r) F) * (d : Matrix (Fin r) (Fin r) F) := by
    ext a c
    rw [hdv, Matrix.mul_diagonal, permGL_apply]
    by_cases e : a = m.1 c <;> simp [mono, e]
  refine ⟨m.1, ⟨u, hle b' hb' u hu⟩, ⟨d * u', Subgroup.mul_mem _ hd (hle b hb u' hu')⟩, Units.ext ?_⟩
  rw [h, hm]
  simp only [Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.FinGL.Bruhat
