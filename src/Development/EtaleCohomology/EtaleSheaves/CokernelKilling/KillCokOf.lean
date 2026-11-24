module

public import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.AssembleOf
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
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.KillCokPf.Asm

namespace LateralTheory.E.KillCokPf.Glue

theorem et_pi {D : CommRingCat.{0}} {ι : Type} [Finite ι] (D₁ : ι → CommRingCat.{0}) (e : ∀ k, D ⟶ D₁ k)
    (he : ∀ k, Et (e k)) : Et (piMap D₁ e) := by
  letI : ∀ k, Algebra D (D₁ k) := fun k => (e k).hom.toAlgebra
  haveI : ∀ k, Algebra.Etale D (D₁ k) := he
  have h : Algebra.Etale D (∀ k, D₁ k) := inferInstance
  exact h

def PushGlue : Prop := Coprod → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') (m : ℤ)
  (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m) {ι : Type} [Fintype ι] (D₁ : ι → CommRingCat.{0}) (e : ∀ k, D ⟶ D₁ k),
  (∀ k, Et (e k)) →
  (∀ k, ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ k ⟶ Y₁), IsPushout φ' (e k) u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)) →
  ∃ (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : CommRingCat.of (∀ k, D₁ k) ⟶ Y''),
    IsPushout φ' (piMap D₁ e) u φ'' ∧
    pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ'')) (tw q i) m)

theorem ProdGlue_of (hP : PushGlue) : ProdGlue := by
  intro hC q _ i D Y' φ' m y ι _ D₁ e he hk
  exact ⟨et_pi D₁ e he, hP hC q i φ' m y D₁ e he hk⟩

theorem KillCok_of' (hC : Coprod) (hP : LateralTheory.E.KillCokPf.Pointwise) (hG : PushGlue) : LateralTheory.E.DescLocPf.Fine.KillCok :=
  LateralTheory.E.KillCokPf.KillCok_of hC hP (Assemble_of (ProdGlue_of hG))

end LateralTheory.E.KillCokPf.Glue
