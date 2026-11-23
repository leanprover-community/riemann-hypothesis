module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem disc_eq_trivV (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)) : V = trivV N (disc.obj F) := by
  ext n U x
  have h := congrArg
    (fun φ : (disc.obj F).obj (op (SimplexCategory.mk 0)) ⟶ (ofCat (glCat N)).obj n =>
      ConcreteCategory.hom (φ.app U) x)
    (V.naturality (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op)
  simp at h
  show (ConcreteCategory.hom ((V.app n).app U)) x = _
  rw [h]
  generalize (ConcreteCategory.hom ((V.app (op (SimplexCategory.mk 0))).app U)) x = y
  refine CategoryTheory.Functor.ext (fun i => rfl) ?_
  intro i j f
  change (y : Fin 1 ⥤ (glCat N).obj (Scheme.Γ.obj U)).map (𝟙 (0 : Fin 1)) = _
  refine (CategoryTheory.Functor.map_id (y : Fin 1 ⥤ (glCat N).obj (Scheme.Γ.obj U)) 0).trans ?_
  change 𝟙 (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))) =
    eqToHom (rfl : SingleObj.star (GL (Fin N) (Scheme.Γ.obj U)) = _) ≫
      𝟙 (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))) ≫ eqToHom rfl
  erw [Category.id_comp, Category.id_comp]
  exact (eqToHom_refl _ _).symm

end GlobalTheory.EtC
