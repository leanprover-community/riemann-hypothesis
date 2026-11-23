module

public import Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfLocalTwist
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex Opposite

namespace LateralTheory.EtaleTrace

theorem free_ext (R : Type) [CommRing R] (P : PSh) {G : Shv R} (f g : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)),
      (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := (freeP R).obj P) f.hom g.hom G.property ?_
  ext U : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have := h U.unop x
  simp only [freeGen] at this
  simp only [freeP, ModuleCat.freeMk] at this
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  exact this

theorem cocEq : CocEq := by
  intro R _ F X α β h
  apply Cocycle.ext
  apply Cochain.ext₀
  intro q
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
    exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 q hq).eq_of_tgt _ _
  · have key : (chainsXIso R (sch.obj X) 0).inv ≫ α.1.v _ _ (show -((0:ℕ):ℤ) + 0 = 0 by simp) =
        (chainsXIso R (sch.obj X) 0).inv ≫ β.1.v _ _ (show -((0:ℕ):ℤ) + 0 = 0 by simp) := by
      apply free_ext
      intro U x
      exact h U x
    have := congrArg (fun φ => (chainsXIso R (sch.obj X) 0).hom ≫ φ) key
    simpa using this
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_extend_X
    intro i hi
    change -(i:ℤ) = q at hi
    omega

theorem CocEq_of : CocEq := cocEq

end LateralTheory.EtaleTrace
