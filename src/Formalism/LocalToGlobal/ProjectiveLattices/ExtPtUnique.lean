module

public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem extPt (Y : Model Xo c β) (T : CDVR) (b : O →+* T.V) (x : Sp T.Fr ⟶ Xo.XF c)
    (hx : x ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b) :
    ∃ yt : Sp T.V ⟶ Y.X, Out.jK T.V ≫ yt = x ≫ Y.j ∧ yt ≫ Y.s = spMap b := by
  haveI : IsProper Y.s := projProper _ _ _ Y.proj
  have hE : ValuativeCriterion.Existence Y.s := by
    have h1 : UniversallyClosed Y.s := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h1
    exact h1.1
  let S : ValuativeCommSq Y.s :=
    { R := T.V, K := FractionRing T.V, i₁ := x ≫ Y.j, i₂ := spMap b,
      commSq := ⟨by rw [Category.assoc]; exact hx⟩ }
  obtain ⟨⟨⟨l, hl1, hl2⟩⟩⟩ := hE S
  exact ⟨l, hl1, hl2⟩

end Formalism.L2.Pj
