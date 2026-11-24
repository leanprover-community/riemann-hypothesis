module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxForm (IsRelAcyclic)
open GlobalTheory GlobalTheory.AbLaw
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleSymModel

def polPull {S : Scheme.{0}} (P : Out.PolAV S) {R : Type} [CommRing R] (f : Sp R ⟶ S) : Out.PolAV (Sp R) :=
  have h := isGrpPullback_pullback P.A f
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom f)
  have := P.isAb.proper
  { A := (Over.pullback f).obj P.A
    isAb := isAbelianScheme_pullback_obj f P.A P.isAb
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull (pullback.fst P.A.hom f)
    isLB := hL'
    rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym
    ample := AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample h.1
    ktriv := by
      obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hL'
      exact kTriv_pull h P.isLB hL' ((isGen_iff w).1 hw) P.ktriv }

end GlobalTheory.AmpleSymModel
