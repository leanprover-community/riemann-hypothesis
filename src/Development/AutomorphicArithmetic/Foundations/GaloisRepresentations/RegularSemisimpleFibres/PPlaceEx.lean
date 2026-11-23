module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.placeEx :
    PlaceEx := by
  intro K M Ω _ _ _ _ _ _ _ _ A v hv n P
  let f : 𝓞 M →+* A := ((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A (map_isIntegral_int (algebraMap M Ω) x.isIntegral_coe)
  let I : Ideal (𝓞 M) := (IsLocalRing.maximalIdeal A).comap f
  have hmem : ∀ x : 𝓞 M, x ∈ I ↔ A.valuation (algebraMap M Ω (x : M)) < 1 := fun x =>
    ValuationSubring.valuation_lt_one_iff A (f x)
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hval : A.valuation ((Ideal.absNorm v.asIdeal : ℕ) : Ω) < 1 := by
    have h := (hv ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K)).2 (Ideal.absNorm_mem v.asIdeal)
    simpa using h
  have hne : I ≠ ⊥ := by
    intro h0
    have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 M) ∈ I := (hmem _).2 (by simpa using hval)
    rw [h0, Ideal.mem_bot] at h1
    exact Nat.cast_ne_zero.2 hN0 h1
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M n P
    ⟨I, Ideal.comap_isPrime _ _, hne⟩
  exact ⟨⟨I, Ideal.comap_isPrime _ _, hne⟩, fun x => (hmem x).symm, τ, hτ⟩
