module

public import Development.EtaleCohomology.EtaleSheaves.LocSecPfB
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LocSecPfC

variable (R : Type) [CommRing R] (X : Scheme.{0})

def eqv (G : Shv R) : ((free R).obj (yoneda.obj X) ⟶ G) ≃ Sec G X :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ G).trans <|
  (((ModuleCat.adj (ULift.{1} R)).whiskerRight (C := Scheme.{0}ᵒᵖ)).homEquiv (yoneda.obj X ⋙ uliftFunctor.{1}) G.obj).trans
  (uliftYonedaEquiv.{1} (X := X) (F := G.obj ⋙ forget _))

theorem eqv_apply (G : Shv R) (f : (free R).obj (yoneda.obj X) ⟶ G) :
    eqv R X G f = (f.hom.app (op X)).hom (freeGen R _ X (𝟙 X)) := by
  rfl

def eqvAdd (G : Shv R) : ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X :=
  { eqv R X G with
    map_add' := fun f g => by
      change eqv R X G (f + g) = eqv R X G f + eqv R X G g
      rw [eqv_apply, eqv_apply, eqv_apply]
      rfl }

theorem homSec : LateralTheory.E.LocSecPfB.HomSec := by
  intro R _ X
  refine ⟨eqvAdd R X, fun φ f => ?_⟩
  change eqv R X _ (f ≫ φ) = Sec.map φ (eqv R X _ f)
  rw [eqv_apply, eqv_apply]
  rfl

theorem LocSec_of (h2 : LateralTheory.E.LocSecPfB.ClassSec) : LateralTheory.E.LeafLocPf.LocSec :=
  LateralTheory.E.LocSecPfB.LocSec_of homSec h2

end LateralTheory.E.LocSecPfC
