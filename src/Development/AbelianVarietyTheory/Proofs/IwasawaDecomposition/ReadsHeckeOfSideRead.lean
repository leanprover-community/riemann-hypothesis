module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameValuesGaloisCharFormResidueUnitCharacter
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.ValQ

theorem tameVal_eq_locK (hGAR : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (i : D.ntw.Tw) (k : ℕ)
    (e : NX.Kk D i k →+* ℂ) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (χ : HChar D.host.E)
    (hR : ReadsHecke e ψ χ) (hopen : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)))
    (hord : ∀ σ, ∃ N : ℕ, ψ σ ^ (D.ntw.l i ^ N) = 1) (P' : PlE D.host)
    (hl : ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal) (a : 𝓞 D.host.E) (y : D.host.Eˣ)
    (ha : a ∉ P'.asIdeal) (hy : (y : D.host.E) = (a : D.host.E)) :
    e (NX.ofOk D i k (NX.tameVal ψ P' 1 a).1) = ((χ.locK P' y : ℂˣ) : ℂ) := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨art, hart, hH⟩ := hR
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver D.nd.Om P'
  obtain ⟨hq2, hq1⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem P'
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ0 : 𝓞 D.host.E, ϖ0 ∈ P'.asIdeal ∧ ϖ0 ∉ P'.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P'.asIdeal) P'.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E))
    (show 0 < normV P' - 1 by omega)
  have hxu : IsUnitAt P' (atFin P' y) := by
    show Valued.v (((y : D.host.E) : P'.adicCompletion D.host.E)) = 1
    rw [hy, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 ha
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art hart
    P' A hA ϖ hϖ1 hϖ2 π hπ (atFin P' y) a hxu (by simp [atFin, hy])
  have hTR : NX.TameRep P' 1 σ a := ⟨A, hA, hσI, ϖ, π, hϖ1, hϖ2, hπ, by simpa using hσval⟩
  have hI : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' → ∀ σ ∈ Ine (F := D.host.E) A,
      ∃ N : ℕ, ψ σ ^ (D.ntw.l i ^ N) = 1 := fun _ _ σ _ => hord σ
  rw [GlobalTheory.TameResRead.tameVal_eq_of_tameRep ψ P' 1 (D.ntw.l i) hopen hl hI σ a ha hTR]
  have h1 := hH _ σ hσart.symm
  exact (congrArg (fun z : ℂˣ => (z : ℂ)) h1).symm

end GlobalTheory.LevCmp.ValQ
