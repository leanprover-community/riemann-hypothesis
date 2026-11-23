module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
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

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

theorem tt_sheafify_locSurj (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : ((presheafToSheaf Scheme.etaleTopology.{0} _).obj P).obj.obj (op U)) :
    Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology.{0} P).app (op V)).hom x =
      (((presheafToSheaf Scheme.etaleTopology.{0} _).obj P).obj.map g.op).hom y :=
  ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} P) y,
    fun _ _ ⟨x, hx⟩ => ⟨x, hx⟩⟩

theorem tt_sheafify_locInj (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (x : P.obj (op U)) (hx : ((toSheafify Scheme.etaleTopology.{0} P).app (op U)).hom x = 0) :
    Loc U fun _ g => (P.map g.op).hom x = 0 := by
  refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} P) x 0
    (by simpa using hx), fun _ _ h => ?_⟩
  simpa using h

end LateralTheory.EtaleFoundations
