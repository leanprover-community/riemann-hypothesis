module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

set_option autoImplicit false

namespace GlobalTheory.RatDegZeros

theorem mem_range_fst : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (x : X), CharZero (X.residueField x) → x ∈ Set.range (ratFibre.fst p) := by
  intro k _ X p x hx
  let q : Spec (X.residueField x) ⟶ Sp ℚ := Spec.map (CommRingCat.ofHom (algebraMap ℚ (X.residueField x)))
  let y0 := (ratFibre.isPullback p).lift (X.fromSpecResidueField x) q (specZIsTerminal.hom_ext _ _)
  let z : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  refine ⟨y0 z, ?_⟩
  have e : (y0 ≫ ratFibre.fst p) z = X.fromSpecResidueField x z := by
    rw [(ratFibre.isPullback p).lift_fst]
  rw [Scheme.Hom.comp_apply] at e
  exact e.trans (X.fromSpecResidueField_apply x z)

end GlobalTheory.RatDegZeros
