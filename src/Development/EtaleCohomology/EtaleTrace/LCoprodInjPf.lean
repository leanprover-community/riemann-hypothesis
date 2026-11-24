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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

theorem chains_zero (R : Type) [CommRing R] (E : Scheme.{0}) (hZ : IsZero ((free R).obj (yoneda.obj E))) (p : ℤ) :
    IsZero (((chains R).obj (sch.obj E)).X p) := by
  rcases le_or_gt p 0 with h | h
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = -(m : ℤ) := ⟨p.natAbs, by omega⟩
    exact hZ.of_iso (chainsXIso R (sch.obj E) m)
  · apply HomologicalComplex.isZero_extend_X
    intro i hi
    have : (ComplexShape.embeddingDownNat).f i = -(i : ℤ) := rfl
    omega

theorem H_sub (R : Type) [CommRing R] (E : Scheme.{0}) (hZ : IsZero ((free R).obj (yoneda.obj E))) (F : Shv R) (n : ℤ) :
    Subsingleton (H R (sch.obj E) F n) := by
  have : Subsingleton (CochainComplex.HomComplex.Cochain ((chains R).obj (sch.obj E)) (res R F) n) :=
    ⟨fun a b => CochainComplex.HomComplex.Cochain.ext _ _ (fun p q _ => (chains_zero R E hZ p).eq_of_src _ _)⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective x
  obtain ⟨b, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective y
  have hab : a = b := Subtype.ext (@Subsingleton.elim _ this _ _)
  rw [hab]

end LateralTheory.EtaleTrace

end
