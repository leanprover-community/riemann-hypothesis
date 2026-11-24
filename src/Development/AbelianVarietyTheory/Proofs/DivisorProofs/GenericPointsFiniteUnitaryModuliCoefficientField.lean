module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.XScov

theorem genericPoints_XF_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), (genericPoints (Xo.XF c)).Finite := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨N, i, hi, hq, he⟩ := Xo.qproj
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (KA l) N
  haveI : QuasiCompact Xo.s := he ▸ inferInstance
  haveI : LocallyOfFiniteType Xo.s := he ▸ inferInstance
  haveI : QuasiCompact (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  haveI : LocallyOfFiniteType (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  haveI : IsLocallyNoetherian (Xo.XF c) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  haveI : CompactSpace (Xo.XF c) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  haveI : IsNoetherian (Xo.XF c) := {}
  exact genericPoints.finite finite_irreducibleComponents_of_isNoetherian

end GlobalTheory.XScov
