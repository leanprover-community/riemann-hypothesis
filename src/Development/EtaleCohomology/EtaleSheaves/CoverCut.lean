module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
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
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.CoverCut

def ClopenSys {Y : Scheme.{0}} (y : Y) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D)
    (ι : ∀ j, D.obj j ⟶ Y) : Prop :=
  Nonempty (IsLimit c) ∧ (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
    ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)

def Build : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P],
  ∃ (Y : Scheme.{0}) (k : Y ⟶ P), IsIntegralHom k ∧ Surjective k ∧
    ∀ y : Y, ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
      ClopenSys y D c ι ∧ AICSch c.pt ∧ ∀ j, IsIntegralHom ((c.π.app j ≫ ι j) ≫ k)

def ProEqv : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)),
  (∀ y : Y, ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
      ClopenSys y D c ι ∧ ∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) →
  PB q i g

theorem goal_of (hB : Build) (hP : ProEqv) : Cover := by
  intro H q i A _ _ hq P _ _ p hZ
  obtain ⟨Y, k, hk, hs, hY⟩ := hB (P := P)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace k
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated k
  refine ⟨Y, k, hk, hs, hP H q i A hq (k ≫ p) fun y => ?_⟩
  obtain ⟨J, _, _, D, c, ι, hc, hA, hint⟩ := hY y
  refine ⟨J, inferInstance, inferInstance, D, c, ι, hc, fun j => ?_⟩
  have := hZ c.pt ((c.π.app j ≫ ι j) ≫ k) (hint j) hA
  simpa only [Category.assoc] using this

end LateralTheory.E.CoverCut
