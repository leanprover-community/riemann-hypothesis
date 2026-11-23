module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocalizedQuotientIsSimpleModuleOfMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem zero_le_divCycle {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R] (P : Ideal (MRing ι R))
    (f : MRing ι R) (W : Ideal (MRing ι R)) : 0 ≤ divCycle P f W := by
  unfold divCycle
  split_ifs <;> positivity

theorem BlowUpExcessDecreases.proof (hpos : ExcessPositive.Statement.{u})
    (hres : ResidualComparison.Statement.{u}) (hexc : ExceptionalComparison.Statement.{u}) :
    BlowUpExcessDecreases.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH hcommon
  set N := commonExcess ϖ P f g s with hN
  have hε : 0 < N := hpos O ϖ hϖ K ι P d hP b f g hD s hsP hcommon

  have hbdd : BddAbove (Set.range fun G : {G : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G} =>
      (divCycle P s G.1 * ratDiv P f g G.1).toNat) := by
    refine (((DivCycleFiniteSupport.proof O K ι P s).image
      fun G => (divCycle P s G * ratDiv P f g G).toNat).insert 0).bddAbove.mono ?_
    rintro _ ⟨G, rfl⟩
    by_cases h : divCycle P s G.1 = 0
    · left; simp [h]
    · right; exact ⟨G.1, h, rfl⟩
  have hle : ∀ G, (C ϖ : MRing ι O) ∈ G → ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → x ≤ divCycle P s G →
      y ≤ ratDiv P f g G → x * y ≤ N := by
    intro G hG x y hx hy hxG hyG
    have h1 : (divCycle P s G * ratDiv P f g G).toNat ≤ N := le_ciSup hbdd ⟨G, hG⟩
    have h2 : x * y ≤ divCycle P s G * ratDiv P f g G := mul_le_mul hxG hyG hy (hx.trans hxG)
    exact h2.trans ((Int.self_le_toNat _).trans (by exact_mod_cast h1))

  have hterm : ∀ x y : ℤ, 0 ≤ x → (0 < x → 0 < y → x * y < N) → (x * y).toNat ≤ N - 1 := by
    intro x y hx h
    rcases lt_or_ge 0 x with hx' | hx'
    · rcases lt_or_ge 0 y with hy | hy
      · have h1 := h hx' hy
        generalize x * y = p at h1 ⊢
        omega
      · have h1 : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hy
        generalize x * y = p at h1 ⊢
        omega
    · obtain rfl : x = 0 := le_antisymm hx' hx
      simp
  have hne : Nonempty {G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O) //
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G'} := ⟨⟨⊤, Submodule.mem_top⟩⟩
  constructor
  ·
    have h : commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m)
        (liftForm s) ≤ N - 1 := by
      refine ciSup_le fun G' => hterm _ _ (zero_le_divCycle _ _ _) fun hx hy => ?_
      obtain ⟨G, hG, h1, h2⟩ :=
        hres O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G'.1 G'.2 hx hy
      have h3 := hle G hG _ _ hx.le (add_nonneg hx.le hy.le) h1 h2
      exact (mul_lt_mul_of_pos_left (lt_add_of_pos_left _ hx) hx).trans_le h3
    omega
  ·
    have h : commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) (newVar none) ≤ N - 1 := by
      refine ciSup_le fun G' => hterm _ _ (zero_le_divCycle _ _ _) fun hx hy => ?_
      obtain ⟨G, hG, h1, h2⟩ :=
        hexc O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G'.1 G'.2 hx hy
      have h3 := hle G hG _ _ (add_nonneg hx.le hy.le) hy.le h1 h2
      exact (mul_lt_mul_of_pos_right (lt_add_of_pos_right _ hy) hy).trans_le h3
    omega

end GroundTheory.Heights₂.Heights.NumbersDVR
