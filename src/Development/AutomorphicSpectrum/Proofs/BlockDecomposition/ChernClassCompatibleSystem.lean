module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.ChernSys

theorem inv_cech (hpt : CrystallineSemistableComparison.E.CechPt) (l : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X)
    (hl : IsUnit (l : Γ(X, ⊤))) (n : ℕ) : GlobalTheory.EtC.Inv (l ^ n) (cech f) := by
  rintro U ⟨z⟩
  obtain ⟨x, y, h, -⟩ := (hpt Y X f 0 U).1 z
  have h1 : IsUnit (l : Γ(U, ⊤)) := by
    have := hl.map x.appTop.hom
    rwa [map_natCast] at this
  rw [Nat.cast_pow]
  exact h1.pow n

theorem chern_class_compatible_system (hpt : CrystallineSemistableComparison.E.CechPt) : CrystallineSemistableComparison.E.FirstChernCompatibleSystem := by
  intro a2 a11 l _ Y X f _ _ hl L
  have hinv := inv_cech hpt l f hl
  have hne : ∀ n, NeZero (l ^ n) := fun n => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨hinv, ?_⟩
  have hb : ∀ n, Function.Bijective (pull (ZMod (l ^ n)) (cechAug f) (tw (l ^ n) 1) 2) :=
    fun n => a2 (ZMod (l ^ n)) f (tw (l ^ n) 1) 2
  choose x hx using fun n => (hb n).2 (c1 (l ^ n) L)
  refine ⟨⟨x, fun k => ?_⟩, hx⟩
  apply (hb k).1
  have e := ((a11 (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) (cech f)).2.1 (hinv (k + 1))).2 L
  have e2 := pull_red (l ^ (k + 1)) (l ^ k) (cechAug f) 2 1 (x (k + 1))
  exact e2.trans ((congrArg _ (hx (k + 1))).trans (e.trans (hx k).symm))

end GlobalTheory.CompanionTheory.ChernSys
