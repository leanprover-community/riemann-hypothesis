module

public import Development.EtaleCohomology.EtaleSheaves.LeafDegCut
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSurj0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem cov_of_points {B : Scheme.{0}} (U : B.Etale) (P : ∀ U' : B.Etale, (U' ⟶ U) → Prop)
    (h : ∀ x : U.left, ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
      ∀ (U'' : B.Etale) (b : U'' ⟶ U'), P U'' (b ≫ a)) : Cov U P := by
  choose Z f hx hP using h
  refine ⟨Sieve.ofArrows Z f, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hx x⟩
  · rintro U' a ⟨Y, b, g, ⟨j⟩, rfl⟩
    exact hP j U' b

def LeafSurj0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ Set.range ι → ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
    ∀ (U'' : B.Etale) (b : U'' ⟶ U'), rY q i (g2 ≫ g1 ≫ p) ι (b ≫ a) 0 y = 0

def LeafSurj0V : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ V → ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
    ∀ (U'' : B.Etale) (b : U'' ⟶ U'), ∃ c : Hrel (ZMod q) (sch.map (prB ι U'')) (tw q i) 0,
      bY q i (g2 ≫ g1 ≫ p) ι U'' 0 c = rY q i (g2 ≫ g1 ≫ p) ι (b ≫ a) 0 y

theorem LeafSurj0_of (hW : LeafSurj0W) (hV : LeafSurj0V) : LateralTheory.E.LeafDegCut.LeafSurj0 := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hVW p g1 g2 h0 h1 h2 hS U y
  refine cov_of_points U _ fun x => ?_
  by_cases hx : U.hom x ∈ V
  · exact hV hy q k hq i b ι V hVW p g1 g2 h0 h1 h2 hS U y x hx
  · have hxW : U.hom x ∈ Set.range ι := by
      have : U.hom x ∉ (V : Set B) := hx
      rw [hVW] at this
      simpa using this
    obtain ⟨U', a, hxa, hz⟩ := hW hy q k hq i b ι V hVW p g1 g2 h0 h1 h2 hS U y x hxW
    exact ⟨U', a, hxa, fun U'' b' => ⟨0, by rw [map_zero, hz U'' b']⟩⟩

end LateralTheory.E.LeafSurj0Pf
