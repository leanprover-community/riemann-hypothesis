module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfRatPoint
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.NeutralPart


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.SS.NeutralPart.geometricallyConnected_of_section {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [QuasiCompact f] (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
    (h : ∀ s : S, _root_.IsConnected (f ⁻¹' {s})) : GeometricallyConnected f := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro s
  haveI : ConnectedSpace (f ⁻¹' {s}) := isConnected_iff_connectedSpace.mp (h s)
  haveI : ConnectedSpace (f.fiber s) :=
    (f.fiberHomeo s).symm.surjective.connectedSpace (f.fiberHomeo s).symm.continuous
  haveI : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    instLocallyOfFiniteTypeSndScheme f (S.fromSpecResidueField s)
  exact _root_.GlobalTheory.RatPointConn.of_section (k := S.residueField s)
    (f.fiberToSpecResidueField s)
    (pullback.lift (S.fromSpecResidueField s ≫ e) (𝟙 _) (by simp [he]))
    (pullback.lift_snd _ _ _)

end GlobalTheory.SS.NeutralPart
