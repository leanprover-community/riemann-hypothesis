module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.twistedEisensteinPiece_trivialCharacter_eq :
    ∀ {K : Type} [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (N L m w : ℕ) (c d : ℤ) (v v' : ℤ × ℤ) (ζ : K) (z₀ : ZMod (l ^ m)), 1 ≤ m → m ≤ L → ∀ r : ℕ, pieceT N l L m (w + 2) (1 : DirichletCharacter K (l ^ m)) c d v v' ζ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = z₀) r = -((l : K) ^ ((L : ℤ) * ((w : ℤ) - 2))) * ∑ γ ∈ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = z₀), cmul (smF c (w + 1) (N * l ^ L) ζ (rowT N l L γ 0 v).1 (rowT N l L γ 0 v).2) (smF d 1 (N * l ^ L) ζ (rowT N l L γ 1 v').1 (rowT N l L γ 1 v').2) r := by
  intro K _ _ l _ N L m w c d v v' ζ z₀ _ hmL r
  unfold pieceT
  have hd : l ^ m ∣ l ^ L := pow_dvd_pow l hmL
  have hexp : ((L : ℤ) * (((w + 2 : ℕ) : ℤ) - 4)) = (L : ℤ) * ((w : ℤ) - 2) := by
    push_cast
    ring
  have hk : w + 2 - 1 = w + 1 := by omega
  rw [hexp, hk]
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  have hu : IsUnit ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m))) := by
    rw [ZMod.natCast_val]
    have hdet : IsUnit (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit
    exact hdet.map (ZMod.castHom hd (ZMod (l ^ m)))
  rw [MulChar.one_apply hu, one_mul]
