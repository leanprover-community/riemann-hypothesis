module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
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

open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem card_ker_eq_card_quot_range {O : Type} [CommRing O] {N : Type} [AddCommGroup N] [Module O N]
    [Finite N] (f : N →ₗ[O] N) :
    Nat.card (LinearMap.ker f) = Nat.card (N ⧸ LinearMap.range f) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h3 : Nat.card (N ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr (f.quotKerEquivRange).toEquiv
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  rw [h3] at h1
  rw [h1] at h2
  nlinarith [h2]

def invariantsOfKilledLevelEquiv {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (c : O) :
    ReciprocityTheory.Gal.H0 (levRep ρ c) ≃
      LinearMap.ker (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants) where
  toFun x := ⟨⟨x.1.val, fun g => by
      have h : levRep ρ c g x.1 = x.1 := x.2 g
      have := congrArg Lev.val h
      rwa [levRep_val] at this⟩, by
      apply Subtype.ext
      show c • x.1.val = 0
      exact Lev.smul_val x.1⟩
  invFun y := ⟨Lev.mk y.1.1 (by
      have h : (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants) y.1 = 0 := y.2
      exact congrArg Subtype.val h), by
      show ∀ g, _
      intro g
      apply Lev.ext
      rw [levRep_val, Lev.val_mk]
      exact y.1.2 g⟩
  left_inv x := by
    apply Subtype.ext
    apply Lev.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem card_H0_level_rep : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (c : O), Finite ρ.invariants →
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
      Nat.card (ρ.invariants ⧸ LinearMap.range (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  intro O _ G _ _ M _ _ ρ c hfin
  rw [Nat.card_congr (invariantsOfKilledLevelEquiv ρ c)]
  exact card_ker_eq_card_quot_range _

end GlobalTheory.ShapeNeg
