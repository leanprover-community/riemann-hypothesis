module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSteepOnOfGermZero
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteInvLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp

theorem vV_algebraMap_unit (T : CDVR) (u : T.Vˣ) : vV T.V (algebraMap T.V T.Fr (u : T.V)) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr (u : T.V)) = 1 := by
    unfold valV
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    refine (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 ?_
    show (u : T.V) ∉ IsLocalRing.maximalIdeal T.V
    exact fun h => h u.isUnit
  simp [vV, h1]

theorem log_ofAdd_neg (m : ℤ) :
    WithZero.log ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = -m := by
  first | rfl | simp [WithZero.log] | exact WithZero.log_coe _

theorem isLocalHom_of_centred {Y : Scheme.{0}} {y : Y} {ν : Valuation (Y.presheaf.stalk y) (WithZero (Multiplicative ℤ))}
    (hν : Centred y ν) (T : CDVR) (g : Y.presheaf.stalk y →+* T.V) (ρ : ℝ) (hρ : 0 < ρ)
    (hval : ∀ a, ν a ≠ 0 → -((WithZero.log (ν a) : ℤ) : ℝ) = ρ * (vV T.V (algebraMap T.V T.Fr (g a)) : ℝ)) :
    IsLocalHom g := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ IsLocalRing.maximalIdeal _ := hna
  have h0 : ν a ≠ 0 := by
    intro h
    rw [hν.2.2 a h, map_zero] at ha
    exact not_isUnit_zero ha
  have hlt := hν.2.1 a hm
  have hlog : WithZero.log (ν a) < 0 := by
    have := (WithZero.log_lt_log h0 one_ne_zero).2 hlt
    simpa using this
  have hv := hval a h0
  obtain ⟨u, hu⟩ := ha
  rw [← hu, vV_algebraMap_unit] at hv
  have : (0 : ℝ) < -((WithZero.log (ν a) : ℤ) : ℝ) := by
    have : ((WithZero.log (ν a) : ℤ) : ℝ) < 0 := by exact_mod_cast hlog
    linarith
  rw [hv] at this
  simp at this


end GlobalTheory.HSApp
