module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.Alg

namespace UpperTheory.V.Th


open UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws in
def SpPt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c), Ctx2 D ∨ Ctx3 D →
    ∀ r, D.EPt r → Irr r → ∃ T : Tower D, T.Fit ∧ T.Deep ∧ ∀ c₁ : Coef l,
      ∃ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l)
        (r₁ : G ℚ Ω →* M4 (PadicAlgCl l)), c₁.O ≤ c'.O ∧ IsConj4 r r₁ ∧ D.Mult r₁ ∧
        r₁.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r ∧
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) ∧ Irr (r₁.comp T.L.fixingSubgroup.subtype)

end UpperTheory.V.Th

end
