module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwSharp

variable {D : D7} {u : D.what₂.Word}

theorem weight_eq (X Y : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j)) :
    (X.fm.lam j τ).w a = (Y.fm.lam j τ).w a := by
  have h := (X.fm.lam_eq j hj τ a).trans (Y.fm.lam_eq j hj τ a).symm
  exact_mod_cast h

theorem weightSup_eq (X Y : Ch D u) (τ : D.what₂.Tau) : TauWeight X τ = TauWeight Y τ := by
  unfold TauWeight
  refine Finset.sup_congr rfl fun i hi => Finset.sup_congr rfl fun a _ => ?_
  rw [weight_eq X Y i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) τ a]

theorem exponent_eq (X Y : Ch D u) : ETpi X = ETpi Y := by
  unfold ETpi Wt; simp only [weightSup_eq X Y]

theorem tupleChainSharpColumnValuation_of_twisted : ∀ (D : D7) (u : D.what₂.Word) (Tw : TwForms D) (μ : D.what₂.Tup),
    Step0Tie Tw u μ → Conclusion5Sharp (tw Tw u μ) → TupleChainSharpColumnValuation Tw u μ := by
  intro D u Tw μ hT h w hw c n hc hn x hx
  have hw' : OverT (tw Tw u μ) w := hw.trans (Tw.A_T u μ).symm
  have hown : ET (own D u) w = EatT D u w := rfl
  have hE : ET (tw Tw u μ) w = EatT D u w := by
    rw [← hown]; unfold ET
    rw [exponent_eq (tw Tw u μ) (own D u)]
    show (if (Tw.fm u μ).seenP w = true then _ else _) = _
    rw [(hT w hw).1]
  obtain ⟨y, hy, e⟩ := h w hw' c n hc (hE ▸ hn) (Tw.e0 u μ x) ((hT w hw).2 x hx)
  refine ⟨y, hy, e.trans ?_⟩
  show _ • (D.chTw u μ).col ((Tw.fm u μ).emb 0 (Tw.e0 u μ x)) = _
  rw [Tw.embed_mul_block_embedding]

end GlobalTheory.LvT.TwSharp
