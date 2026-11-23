module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffBoundOfLinearIndependentSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionsFgOfProjArithVarietyStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem fg_addSubgroup_field_finite_or_basis {K : Type} [Field K] (H : AddSubgroup K) (hH : H.FG) :
    (H : Set K).Finite ∨ ∃ (r : ℕ) (f : Fin r → K), (∀ j, f j ∈ H) ∧ LinearIndependent ℤ f ∧
      ∀ x ∈ H, ∃ c : Fin r → ℤ, x = ∑ j, c j • f j := by
  have hfin : Module.Finite ℤ H :=
    Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg H).2 hH)
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | h0
  · left
    have htor : Module.IsTorsion ℤ H := by
      intro x
      refine ⟨⟨(ringChar K : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hq.ne_zero)⟩, ?_⟩
      ext
      simp [ringChar.Nat.cast_ringChar]
    have : Finite H := Module.finite_of_fg_torsion H htor
    exact Set.toFinite _
  · right
    haveI : CharP K 0 := h0 ▸ ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    haveI : NoZeroSMulDivisors ℤ H := inferInstance
    haveI : Module.Free ℤ H := Module.free_of_finite_type_torsion_free'
    let bs := Module.finBasis ℤ H
    refine ⟨_, fun j => (bs j : K), fun j => (bs j).2, ?_, ?_⟩
    · exact bs.linearIndependent.map' H.subtype.toIntLinearMap
        (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    · intro x hx
      refine ⟨bs.repr ⟨x, hx⟩, ?_⟩
      have h := congrArg Subtype.val (bs.sum_repr ⟨x, hx⟩)
      calc x = ((⟨x, hx⟩ : H) : K) := rfl
        _ = ((∑ i, bs.repr ⟨x, hx⟩ i • bs i : H) : K) := h.symm
        _ = ∑ j, bs.repr ⟨x, hx⟩ j • (bs j : K) := by
          change H.subtype (∑ i, bs.repr ⟨x, hx⟩ i • bs i) = _
          rw [map_sum]
          rfl

theorem bl_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (R : ℝ), (P.Bl a b R).Finite := by
  intro k _ X _ p D hX P a b R
  rcases fg_addSubgroup_field_finite_or_basis (P.H a b) (GlobalTheory.T.pairSections_fg_of_projArithVariety k X p D hX P a b) with
    hfin | ⟨r, f, hf, hli, hspan⟩
  · exact hfin.subset (fun x hx => hx.1)
  · obtain ⟨C, -, hC⟩ := GlobalTheory.T.exists_coeff_bound_of_linearIndependent_sections k X p D hX P a b r f hf hli
    have hS : {c : Fin r → ℤ | ∀ j, |(c j : ℝ)| ≤ C * R}.Finite := by
      refine (Set.Finite.pi (t := fun _ : Fin r => Set.Icc (-⌈C * R⌉) ⌈C * R⌉)
        (fun _ => Set.finite_Icc _ _)).subset ?_
      intro c hc j _
      have h := abs_le.1 (hc j)
      have hc1 := Int.le_ceil (C * R)
      have h1 : (c j : ℝ) ≤ (⌈C * R⌉ : ℝ) := h.2.trans hc1
      have h2 : -((⌈C * R⌉ : ℤ) : ℝ) ≤ c j := by linarith
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
    refine (hS.image (fun c => ∑ j, c j • f j)).subset ?_
    intro x hx
    obtain ⟨c, rfl⟩ := hspan x hx.1
    exact ⟨c, fun j => hC c R hx j, rfl⟩

end GlobalTheory.HSNef
