module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.LeafKunEmptyPf

variable {R : Type} [CommRing R]

theorem sec_sub (F : Shv R) (U : Scheme.{0}) [IsEmpty U] : Subsingleton (Sec F U) :=
  ModuleCat.isZero_iff_subsingleton.mp (Sheaf.isTerminalOfBotCover F U (Scheme.bot_mem_grothendieckTopology U)).isZero

theorem subsingleton_freePresheaf_hom_of_isEmpty (Z : Scheme.{0}) [IsEmpty Z] (M : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    (hM : ∀ U : Scheme.{0}, IsEmpty U → Subsingleton (M.obj (op U))) :
    Subsingleton ((freeP R).obj (yoneda.obj Z) ⟶ M) := by
  constructor; intro α β
  apply NatTrans.ext; funext U
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  by_cases h : IsEmpty ((Opposite.unop U : Scheme.{0}) : Type)
  · haveI := hM _ h; exact Subsingleton.elim _ _
  · haveI : IsEmpty (Opposite.unop U ⟶ Z) := ⟨fun f => h ⟨fun y => isEmptyElim (f.base y)⟩⟩
    have hs : Subsingleton (((freeP R).obj (yoneda.obj Z)).obj U) := by
      change Subsingleton (ULift.{1} (Opposite.unop U ⟶ Z) →₀ ULift.{1} R); infer_instance
    rw [Subsingleton.elim x 0, map_zero, map_zero]

theorem free_zero (Z : Scheme.{0}) [IsEmpty Z] : IsZero ((free R).obj (yoneda.obj Z)) := by
  rw [IsZero.iff_id_eq_zero]
  have h1 := subsingleton_freePresheaf_hom_of_isEmpty (R := R) Z ((sheafToPresheaf Scheme.etaleTopology _).obj ((free R).obj (yoneda.obj Z)))
    (fun U hU => by haveI := hU; exact sec_sub _ U)
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv ((freeP R).obj (yoneda.obj Z))
    ((free R).obj (yoneda.obj Z))).injective
  exact h1.elim _ _

theorem chains_zero (Z : Scheme.{0}) [IsEmpty Z] (p : ℤ) : IsZero (((chains R).obj (sch.obj Z)).X p) := by
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = p
  · obtain ⟨j, hj⟩ := h
    have hz : IsZero (((chainsN R).obj (sch.obj Z)).X j) := free_zero (R := R) Z
    exact hz.of_iso (HomologicalComplex.extendXIso ((chainsN R).obj (sch.obj Z)) ComplexShape.embeddingDownNat hj)
  · push Not at h
    exact HomologicalComplex.isZero_extend_X ((chainsN R).obj (sch.obj Z)) ComplexShape.embeddingDownNat p h

theorem H_sub (Z : Scheme.{0}) [IsEmpty Z] (F : Shv R) (n : ℤ) : Subsingleton (H R (sch.obj Z) F n) := by
  constructor; intro x y
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective y
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro p q hpq
  exact (chains_zero (R := R) Z p).eq_of_src _ _

end LateralTheory.E.LeafKunEmptyPf
