module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalRootReZeroImSq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType

namespace GlobalTheory.CompRat

theorem exists_isSplit_of_splitLat (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty) (hD : SplitLat D) :
    ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsSplit hP := by
  obtain ⟨Lp, Lm, hs, ho, -, -, hp, hm⟩ := hD
  have two : ∀ m, (D.EF (H.rt • m) m : ℝ) = 2 * D.EF (H.w0 • m) m := fun m => by
    have : D.EF ((2 * H.w0) • m) m = D.EF ((1 + H.rt) • m) m := by rw [H.two_weight_eq_one_add_root]
    rw [two_mul, add_smul, add_smul, one_smul, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply,
      D.alt] at this
    have h : D.EF (H.rt • m) m = 2 * D.EF (H.w0 • m) m := by linarith
    exact_mod_cast h
  obtain ⟨P, hP, k₁, k₂⟩ := GlobalTheory.CM.FamCompare.exists_period D Lp Lm
    (fun z => ⟨1, one_pos, hs ▸ Submodule.mem_top⟩) ho
    (fun x hx => by
      by_cases h : x = 0
      · simp [h]
      · have := hp x hx h
        rw [two] at this
        linarith)
    (fun x hx => by
      by_cases h : x = 0
      · simp [h]
      · have := hm x hx h
        rw [two] at this
        linarith) hty
  exact ⟨P, hP, top_le_iff.1 (hs ▸ sup_le_sup k₁ k₂)⟩

end GlobalTheory.CompRat
