module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageInfOfIsSeparatedOver
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
import Mathlib.Geometry.Euclidean.Volume.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory

namespace GlobalTheory.CompanionTheory.RelInjAbs

open CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Onto

section Cxs

variable {R : Type} [CommRing R]

end Cxs

section Abs

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} (m : CH.Mor F F' (RingHom.id R))
  {ι : Type} [DecidableEq ι]

theorem bij_res_of_eq {Ut V₁ V₂ : ObjectProperty C} (e : V₁ = V₂) {Q : ObjectProperty C} (hQ : Cosieve Q) (h₁ : V₁ ≤ Ut)
    (h₂ : V₂ ≤ Ut) (n : ℕ) (hb : Function.Bijective ((RC.res F hQ h₁).mapH n)) :
    Function.Bijective ((RC.res F hQ h₂).mapH n) := by
  subst e
  exact hb

theorem capU_empty (U : ι → ObjectProperty C) : (fun T => ∃ α, U α T) = capU U ∅ := by
  funext T
  exact propext ⟨fun h => ⟨h, fun α hα => absurd hα (Finset.notMem_empty α)⟩, fun h => h.1⟩

theorem capU_nonempty (U : ι → ObjectProperty C) (P : ObjectProperty C) (S : Finset ι) (hS : S.Nonempty)
    (h : ∀ T, P T ↔ ∀ α ∈ S, U α T) : capU U S = P := by
  funext T
  refine propext ⟨fun hT => (h T).2 hT.2, fun hT => ?_⟩
  obtain ⟨α, hα⟩ := hS
  exact ⟨⟨α, (h T).1 hT α hα⟩, (h T).1 hT⟩

end Abs

end GlobalTheory.CompanionTheory.RelInjAbs

namespace GlobalTheory.CompanionTheory.RelInjZ

open Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.RelInjAbs

variable {K : Type} [Field K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
  {D : E.LineData Y} {d : ℕ}

theorem affine_inf (q : Z ⟶ Spec (CommRingCat.of K)) [IsSeparated q] {V V' : Z.Opens} (h : IsAffineOpen V) (h' : IsAffineOpen V') :
    IsAffineOpen (V ⊓ V') :=
  GlobalTheory.FinNear.isAffineOpen_preimage_inf_of_isSeparated_over (𝟙 Z) q (isAffineOpen_top (Spec (CommRingCat.of K))) h
    (fun _ _ => trivial) h' (fun _ _ => trivial)

theorem affine_finset_inf (q : Z ⟶ Spec (CommRingCat.of K)) [IsSeparated q] {κ : Type} (V : κ → Z.Opens) (S : Finset κ)
    (hS : S.Nonempty) (h : ∀ o ∈ S, IsAffineOpen (V o)) : IsAffineOpen (S.inf V) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using h a (by simp)
    · exact affine_inf q (h a (by simp)) (ih hs fun o ho => h o (Finset.mem_insert_of_mem ho))

theorem inU_finset_inf (hs : SiteLaws) (i : W ⟶ Z) {κ : Type} (V : κ → Z.Opens) (S : Finset κ) (T) :
    inU q (S.inf V) T ↔ ∀ o ∈ S, inU q (V o) T := by
  classical
  obtain ⟨-, -, htop, hinf, -, -⟩ := hs K W Z Z q i (𝟙 Z)
  induction S using Finset.induction_on with
  | empty => simpa using htop T
  | insert a s ha ih =>
    rw [Finset.inf_insert, hinf, ih]
    simp

end GlobalTheory.CompanionTheory.RelInjZ
