module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaU
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsHeckeIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HdEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckePolyCoeffZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JEnd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JTwistA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THasAutOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLevelU
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm
private theorem locP_of (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : _root_.UpperTheory.V.Pa.LocPAlt :=
  ⟨P.loc.bz, P.loc.geo, GlobalTheory.Published.TameLocal_of_duality P.coh.lt⟩
theorem UpperTheory.V.Hi.hida_unitary_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.W.HidaUAlt := by
  intro P l _ L Ω _ _ _ _ _ _ s V hS _ c _ n hn r B Λ ι
  obtain ⟨R⟩ := _root_.UpperTheory.V.Hi.nonempty_unitaryHeckeData P l L Ω s n hn V (QData.empty V hS) c r ι Λ
  let K : (hset (QData.empty V hS) R.τ₀).Lev := ⟨fun q => Empty.elim q, fun q => Empty.elim q⟩
  obtain ⟨J, hJ⟩ := _root_.UpperTheory.V.Hi.exists_hecke_ideal P l L Ω s n hn V _ c r ι B Λ R K
  have hE := _root_.UpperTheory.Gal.projectedFormsSystemPart.decomposition_and_automorphicAway_of_isJ P l L Ω s n hn V _ c r ι B Λ R K hS J hJ
  have := coef_isCoef l c
  exact ⟨J, ⟨_root_.UpperTheory.V.Hi.ring_props_of_is_j_unitary_hecke_data P l L Ω s n hn V _ c r ι B Λ R K hS J hJ, _root_.UpperTheory.V.Hi.dense_of_is_j_unitary_hecke_data P l L Ω s n hn V _ c r ι B Λ R K hS J hJ,
    _root_.UpperTheory.V.Hi.hecke_ideal_point_properties P l L Ω s n hn V _ c r ι B Λ R K hS J hJ, hE.1, hE.2, _root_.UpperTheory.V.Z.Desc.W.twistOk_of_isJ P l L Ω s n hn V _ c r ι B Λ R K hS J hJ⟩,
    _root_.UpperTheory.V.Pa.has_automorphy_of_statement (locP_of P.litN) l L Ω s V c.O n r B J hS (_root_.UpperTheory.V.Hi.level_of_is_j_unitary_hecke_data P l L Ω s n hn V _ c r ι B Λ R K hS J hJ)⟩
end
