module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.expLoss :
    ∀ (D : D7) (S : Finset ℕ) (h : ℕ → ℝ) (B : ℝ), GlobalTheory.NormSum.Exponents S h B →
      Loss (fun w : PlL D => (vw w ((GlobalTheory.SumSize.TopInt.primeUnder w : ℕ) : D.what₂.LL) : ℝ) * h (GlobalTheory.SumSize.TopInt.primeUnder w)) B := by
  intro D S h B hE
  have e : (fun w : PlL D => (vw w ((GlobalTheory.SumSize.TopInt.primeUnder w : ℕ) : D.what₂.LL) : ℝ) *
      h (GlobalTheory.SumSize.TopInt.primeUnder w)) = Formalism.PairingDivisionLocalBalance.wt (K := D.what₂.LL) S h := by
    funext w
    rw [hE.wt_eq (TopInt.primeUnder_prime w) w (TopInt.primeUnder_mem w), mul_comm]
  rw [e]
  refine ⟨hE.wt_size.1, ?_, hE.wt_size.2⟩
  have hf : ∀ l : ℕ, {w : PlL D | vw w (l : D.what₂.LL) ≠ 0}.Finite := fun l => by
    have hf := FractionalIdeal.finite_factors (K := D.what₂.LL)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) (l : D.what₂.LL))
    rw [Filter.eventually_cofinite] at hf
    exact hf
  refine (S.finite_toSet.biUnion fun l _ => hf l).subset fun w hw => ?_
  obtain ⟨l, hl, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  refine Set.mem_biUnion (Finset.mem_coe.2 hl) fun h1 => h0 ?_
  rw [h1]; simp
