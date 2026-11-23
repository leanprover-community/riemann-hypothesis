module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory

theorem evR_sum_smul_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) {ι : Type} (s : Finset ι) (t : ι → c.F) (f : ι → Rul Xo c)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (∑ i ∈ s, t i • f i) y = ∑ i ∈ s, algebraMap c.F S (t i) * evR Xo c (f i) y := by
  classical
  have hL : ∑ i ∈ s, t i • f i = ∑ j : Fin s.card, t (s.equivFin.symm j) • f (s.equivFin.symm j) := by
    rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp s.equivFin.symm (fun i : s => t i • f i)).symm
  have hR : ∑ i ∈ s, algebraMap c.F S (t i) * evR Xo c (f i) y =
      ∑ j : Fin s.card, algebraMap c.F S (t (s.equivFin.symm j)) * evR Xo c (f (s.equivFin.symm j)) y := by
    rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp s.equivFin.symm (fun i : s => algebraMap c.F S (t i) * evR Xo c (f i) y)).symm
  rw [hL, hR]
  exact Formalism.L2.Pj.evR_sum_smul y (fun j => t (s.equivFin.symm j)) (fun j => f (s.equivFin.symm j))

end GlobalTheory
