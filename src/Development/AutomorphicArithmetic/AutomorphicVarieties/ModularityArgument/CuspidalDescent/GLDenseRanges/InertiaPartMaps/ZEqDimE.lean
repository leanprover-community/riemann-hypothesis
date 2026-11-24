module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import GroundTheory.LocalFields.UnramifiedHensel
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.AbsIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfBis

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField



namespace UpperTheory.V.Z.Desc.V0

private theorem ePart_zero {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) :
    ePart ρ 0 0 = ⊤ := by
  simp [ePart, opE]

private theorem card_not_dvd {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (j : ℕ) : ¬ l ∣ Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j := by
  have hl : l.Prime := Fact.out
  have hw : (s.w s.v0).under (𝓞 (Lp L)) = s.v0 := by
    ext x
    exact (s.hw s.v0 (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA s.v0 x)
  have h2 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← s.norm_v0_eq_one, normV, ← nsmul_one]
    exact card_nsmul_eq_zero'
  have h3 : ((s.p : ℕ) : 𝓞 L) ∈ (s.w s.v0).asIdeal := by
    rw [← hw] at h2
    have h4 : algebraMap (𝓞 (Lp L)) (𝓞 L) ((s.p : ℕ) : 𝓞 (Lp L)) ∈ (s.w s.v0).asIdeal := h2
    rwa [map_natCast] at h4
  have hd : Ideal.absNorm (s.w s.v0).asIdeal ∣ Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h3)
  have hn : Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) = s.p ^ Module.finrank ℤ (𝓞 L) := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 L)), Algebra.norm_algebraMap]
    simp [Int.natAbs_pow]
  rw [hn] at hd
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow s.p_prime).1 hd
  have hq : Nat.card 𝓀[(s.w s.v0).adicCompletion L] = s.p ^ e := by
    refine (resCard_eq_normV (s.w s.v0)).trans ?_
    rw [normV, ← Ideal.absNorm_eq_natCard]
    exact he
  intro h
  rw [hq] at h
  exact s.p_ne ((Nat.prime_dvd_prime_iff_eq hl s.p_prime).1 (hl.dvd_of_dvd_pow (hl.dvd_of_dvd_pow h))).symm


end UpperTheory.V.Z.Desc.V0
