module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}

theorem lbIso_pull_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X}
    (H : LBIso L' (L.pull φ)) (φ' : X'' ⟶ X') : LBIso (L'.pull φ') (L.pull (φ' ≫ φ)) :=
  LBIso.chartPull (chartPullPull L' φ' φ' rfl) (chartPullSame L _ _ _ φ' fun _ => rfl) H

theorem TMap.refl (t : TObj g k J b s) : TMap t t (𝟙 S) := by
  refine ⟨𝟙 _, ?_, ?_, fun i => by simp, fun j => by simp⟩
  · have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
    exact isGrpPullback_of_iso (Iso.refl t.A)
  · exact LBIso.chartPull (chartPullId t.L) (chartPullPull t.L _ _ rfl) (GlobalTheory.PolBaseChange.lbIso_refl t.isLB)

theorem TMap.comp {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h' : TMap t'' t' f') (h : TMap t' t f) : TMap t'' t (f' ≫ f) := by
  obtain ⟨φ, h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨φ', k₁, k₂, k₃, k₄⟩ := h'
  refine ⟨φ' ≫ φ, k₁.comp h₁, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) k₂ (lbIso_pull_comp h₂ φ')
  · rw [← Category.assoc, k₃, Category.assoc, h₃, Category.assoc]
  · rw [← Category.assoc, k₄, Category.assoc, h₄, Category.assoc]

theorem TMap.cancel {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h : TMap t' t f) (n : TMap t'' t (f' ≫ f)) : TMap t'' t' f' := by
  obtain ⟨φ, h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨ψ, k₁, k₂, k₃, k₄⟩ := n
  have hp := h₁.1
  obtain ⟨F, hF, hw⟩ : ∃ F : t''.A.left ⟶ t'.A.left, F ≫ φ = ψ ∧ F ≫ t'.A.hom = t''.A.hom ≫ f' :=
    ⟨hp.lift ψ (t''.A.hom ≫ f') (by rw [k₁.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  subst hF
  refine ⟨F, h₁.cancel k₁ hw, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t.isLB _) (pull_isLB t'.isLB _) k₂ (lbIso_pull_comp h₂ F).symm
  · apply hp.hom_ext
    · rw [Category.assoc, k₃, Category.assoc, Category.assoc, h₃]
    · have a₁ : (t''.pt i).left ≫ t''.A.hom = 𝟙 S'' := Over.w (t''.pt i)
      have a₂ : (t'.pt i).left ≫ t'.A.hom = 𝟙 S' := Over.w (t'.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  · apply hp.hom_ext
    · rw [Category.assoc, k₄, Category.assoc, Category.assoc, h₄]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

theorem tmap_id_comp_cancel : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (s'' : S'' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (t'' : TObj g k J b s''), TMap t t (𝟙 S) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S'), TMap t' t f → (TMap t'' t' f' ↔ TMap t'' t (f' ≫ f)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ t _ _ => ⟨TMap.refl t, fun _ _ h => ⟨fun h' => h'.comp h, fun n => h.cancel n⟩⟩

end GlobalTheory.ZM
end
