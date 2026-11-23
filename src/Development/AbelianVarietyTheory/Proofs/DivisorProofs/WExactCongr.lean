module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactCongr

variable {T : Type 1} [Category.{0} T]

theorem exactAt_iff {N M : T ⥤ AddCommGrpCat.{1}} (ε : N ⟶ M) {X : CosimplicialObject T}
    (hX : ∀ k, IsIso (ε.app (X.obj k))) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ N)).ExactAt (n + 1) ↔
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ M)).ExactAt (n + 1) := by
  haveI : ∀ k, IsIso ((Functor.whiskerLeft X ε).app k) := fun k => hX k
  have hw : IsIso (Functor.whiskerLeft X ε) := NatIso.isIso_of_isIso_app _
  let e := (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).mapIso (@asIso _ _ _ _ (Functor.whiskerLeft X ε) hw)
  exact ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

theorem wExact_iff (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (N M : T ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M) (hU : IsIso (ε.app U)) (hX : ∀ k, IsIso (ε.app (X.obj k))) :
    WExact N a ↔ WExact M a := by
  have nat : ∀ {P Q : T} (f : P ⟶ Q) (x : N.obj P), M.map f (ε.app P x) = ε.app Q (N.map f x) := by
    intro P Q f x
    exact (ConcreteCategory.congr_hom (ε.naturality f) x).symm
  have surj : ∀ (P : T), IsIso (ε.app P) → ∀ (x : M.obj P), ∃ x', ε.app P x' = x := by
    intro P hP x
    refine ⟨inv (ε.app P) x, ?_⟩
    have := ConcreteCategory.congr_hom (IsIso.inv_hom_id (ε.app P)) x
    simpa using this
  have inj : ∀ (P : T), IsIso (ε.app P) → ∀ (x y : N.obj P), ε.app P x = ε.app P y → x = y := by
    intro P hP x y hxy
    have h := congrArg (inv (ε.app P)) hxy
    have hx := ConcreteCategory.congr_hom (IsIso.hom_inv_id (ε.app P)) x
    have hy := ConcreteCategory.congr_hom (IsIso.hom_inv_id (ε.app P)) y
    simp only [ConcreteCategory.comp_apply] at hx hy
    rw [hx, hy] at h
    simpa using h
  have h0 := hX (SimplexCategory.mk 0)
  have h1 := hX (SimplexCategory.mk 1)
  constructor
  · rintro ⟨i1, i2, i3⟩
    refine ⟨?_, ?_, fun n => (exactAt_iff ε hX n).1 (i3 n)⟩
    · intro x y hxy
      obtain ⟨x, rfl⟩ := surj _ hU x
      obtain ⟨y, rfl⟩ := surj _ hU y
      erw [nat, nat] at hxy
      rw [i1 (inj _ h0 _ _ hxy)]
    · intro y hy
      obtain ⟨y, rfl⟩ := surj _ h0 y
      erw [nat, nat] at hy
      obtain ⟨x, hx⟩ := i2 y (inj _ h1 _ _ hy)
      exact ⟨ε.app U x, (nat _ x).trans (congrArg _ hx)⟩
  · rintro ⟨i1, i2, i3⟩
    refine ⟨?_, ?_, fun n => (exactAt_iff ε hX n).2 (i3 n)⟩
    · intro x y hxy
      have h := congrArg (ε.app _) hxy
      erw [← nat, ← nat] at h
      exact inj _ hU _ _ (i1 h)
    · intro y hy
      have h := congrArg (ε.app _) hy
      erw [← nat, ← nat] at h
      obtain ⟨x, hx⟩ := i2 _ h
      obtain ⟨x, rfl⟩ := surj _ hU x
      erw [nat] at hx
      exact ⟨x, inj _ h0 _ _ hx⟩

end GlobalTheory.EtC.WExactCongr

theorem GlobalTheory.EtC.wExact_congr : ∀ (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T)
    (a : (CosimplicialObject.const T).obj U ⟶ X) (N M : T ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M),
    IsIso (ε.app U) → (∀ k, IsIso (ε.app (X.obj k))) → (WExact N a ↔ WExact M a) :=
  fun _ _ U X a N M ε hU hX => GlobalTheory.EtC.WExactCongr.wExact_iff U X a N M ε hU hX
