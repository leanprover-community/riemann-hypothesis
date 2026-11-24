module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem isDomain_and_isIntegrallyClosed_stalk_sp_field (K : Type) [Field K] (y : Sp K) :
    IsDomain ((Sp K).presheaf.stalk y) ∧ IsIntegrallyClosed ((Sp K).presheaf.stalk y) := by
  let p : PrimeSpectrum K := y
  have hle : p.asIdeal.primeCompl ≤ IsUnit.submonoid K := fun x hx =>
    isUnit_iff_ne_zero.2 fun h0 => hx (h0 ▸ p.asIdeal.zero_mem)
  let e₁ : K ≃+* Localization.AtPrime p.asIdeal :=
    (IsLocalization.atUnits K p.asIdeal.primeCompl hle).toRingEquiv
  let e₂ : (Sp K).presheaf.stalk y ≃+* Localization.AtPrime p.asIdeal :=
    (AlgebraicGeometry.Spec.stalkIso (CommRingCat.of K) p).commRingCatIsoToRingEquiv
  let e : K ≃+* (Sp K).presheaf.stalk y := e₁.trans e₂.symm
  haveI := Field.instIsIntegrallyClosed K
  exact ⟨(MulEquiv.isField (Field.toIsField K) e.symm.toMulEquiv).isDomain, IsIntegrallyClosed.of_equiv e⟩

theorem isDomain_stalk_of_smoothOfRelativeDimension_field (K : Type) [Field K] (e : ℕ)
    (X : Scheme.{0}) (g : X ⟶ Sp K) (hg : SmoothOfRelativeDimension e g) (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  haveI : Smooth g := SmoothOfRelativeDimension.smooth e g
  exact (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g
    (isDomain_and_isIntegrallyClosed_stalk_sp_field K) x).1

end GlobalTheory.CompanionTheory.Ar.SncBase
