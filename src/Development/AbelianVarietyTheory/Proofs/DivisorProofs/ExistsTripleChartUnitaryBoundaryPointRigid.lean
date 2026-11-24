module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointRigidTautologicalChartUnitaryBoundaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartBoundaryEquationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartIsEtaleCompletionLocalRingStatement
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem uPre_of_boundary_pointRigid {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (hpq : 1 ≤ Dw.p + Dw.q)
    (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) (hns : NoSelfInt H.bar (min Dw.p Dw.q) φ)
    {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S)
    (hP : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) (hS : SepB Xo c φ j)
    (x : S) (hx : x ∉ Set.range j) : UPre Xo c φ j BD d x := by
  obtain ⟨k, _, m, e, C, ξ, hT, hy, hξ⟩ :=
    GlobalTheory.T.exists_pointRigid_tautological_chart_unitary_boundary Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS x hx
  have hE := GlobalTheory.T.tautologicalChart_isEtaleCompletion_localRing Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  obtain ⟨hset, hred, a, ha, hbd⟩ :=
    GlobalTheory.T.tautologicalChart_boundary_equations Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  exact ⟨k, inferInstance, m, e, C, ξ, a, hT.1, hy, hξ, hE, hred, hset, ha, hbd⟩

end GlobalTheory.UCanon
