module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpConjEntriesHasFDerivAtZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Pc3

noncomputable def pBLin {n : ℕ} (ε : Fin n → Bool) : (Mode ε → ℂ) →ₗ[ℝ] Mat n where
  toFun := pB ε
  map_add' B C := by
    funext a b
    simp only [pB, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> simp [star_add]
  map_smul' r B := by
    funext a b
    simp only [pB, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul, star_mul', Complex.conj_ofReal]

theorem pB_mode {n : ℕ} (ε : Fin n → Bool) (B : Mode ε → ℂ) (x : Mode ε) :
    pB ε B x.1.1 x.1.2 = B x := by
  unfold pB
  rw [dite_eq_left x.2]

theorem stExpDeriv : StExpDeriv := by
  intro n ε
  obtain ⟨⟨L, hL, hD⟩, h2⟩ :=
    GlobalTheory.exp_conj_entries_hasFDerivAt_zero n (Mode ε) (pBLin ε) (fun x => x.1)
  refine ⟨?_, fun s => ?_⟩
  · have hLid : L = ContinuousLinearMap.id ℝ (Mode ε → ℂ) := by
      ext1 w; funext x
      rw [hL]
      exact pB_mode ε w x
    rw [← hLid]
    exact hD
  · obtain ⟨L', hL', hD'⟩ := h2 (Matrix.diagonal s)
    refine ⟨L', fun w x => ?_, hD'⟩
    rw [hL']
    change (Matrix.diagonal s * pB ε w - pB ε w * Matrix.diagonal s) x.1.1 x.1.2 = _
    rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, pB_mode]
    ring

end GlobalTheory.PsCo.Pc3
