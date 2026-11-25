module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj

theorem GlobalTheory.FinEtRank.isIsogDeg_of_card :
  ∀ {S : Scheme.{0}} (A K : Over S) (i : K ⟶ A), Mono i → IsFinite K.hom → Etale K.hom → ∀ (d : ℕ), 1 ≤ d → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ A // GlobalTheory.IwLevel.InSub i y} = d) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) d := by
  intro S A K i hi hfin het d hd hcard
  have h : (toUnit K).left = K.hom := by simpa using Over.w (toUnit K)
  have hrank : ∀ s : S, K.hom.finrank s = d := by
    intro s
    obtain ⟨k, _, _, t, ht⟩ := GlobalTheory.FinEt.exists_algClosed_point S s
    obtain ⟨z, rfl⟩ : s ∈ Set.range t := by rw [ht]; rfl
    obtain ⟨-, hc⟩ := GlobalTheory.FinEt.card_points_eq_finrank K.hom t z
    rw [← hc, ← hcard k t]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨Over.homMk x.1 x.2 ≫ i, ⟨Over.homMk x.1 x.2, rfl⟩⟩) ⟨?_, ?_⟩)
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have := (cancel_mono i).1 (congrArg Subtype.val hab)
      exact Subtype.ext (congrArg CommaMorphism.left this)
    · rintro ⟨y, y', hy'⟩
      refine ⟨⟨y'.left, Over.w y'⟩, Subtype.ext ?_⟩
      simp only
      rw [← hy']
      congr 1
  have hflat : Flat K.hom := inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h]; exact hfin
  · rw [h]; exact hflat
  · rw [h]; exact (Scheme.Hom.one_le_finrank_iff_surjective K.hom).1 fun s => (hrank s).symm ▸ hd
  · intro y; rw [h]; exact hrank y
