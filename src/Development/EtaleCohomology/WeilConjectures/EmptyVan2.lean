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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.EWeil.EmptyVan₂

instance isEmpty_bot : IsEmpty (⊥_ Scheme.{0}) := by
  infer_instance

theorem sec_subsingleton {R : Type} [CommRing R] (G : Shv R) {U : Scheme.{0}} (f : U ⟶ ⊥_ Scheme.{0}) :
    Subsingleton (G.obj.obj (op U)) := by
  have : IsEmpty U := ⟨fun x => isEmptyElim (f.base x)⟩
  exact (ModuleCat.isZero_iff_subsingleton).1
    (IsTerminal.isZero (Sheaf.isTerminalOfBotCover G U (Scheme.bot_mem_grothendieckTopology U)))

theorem free_hom_subsingleton {R : Type} [CommRing R] (G : Shv R) :
    Subsingleton ((free R).obj (yoneda.obj (⊥_ Scheme.{0})) ⟶ G) := by
  constructor
  intro f g
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv _ _).injective
  ext U x
  by_cases h : Nonempty (U.unop ⟶ ⊥_ Scheme.{0})
  · obtain ⟨φ⟩ := h
    exact @Subsingleton.elim _ (sec_subsingleton G φ) _ _
  · have : IsEmpty (U.unop ⟶ ⊥_ Scheme.{0}) := not_nonempty_iff.1 h
    have hx : x = 0 := Finsupp.ext fun a => isEmptyElim (a.down : U.unop ⟶ ⊥_ Scheme.{0})
    subst hx
    simp only [map_zero]

theorem isZero_free {R : Type} [CommRing R] : IsZero ((free R).obj (yoneda.obj (⊥_ Scheme.{0}))) := by
  rw [IsZero.iff_id_eq_zero]
  have := free_hom_subsingleton (R := R) ((free R).obj (yoneda.obj (⊥_ Scheme.{0})))
  exact Subsingleton.elim _ _

end LateralTheory.EWeil.EmptyVan₂
