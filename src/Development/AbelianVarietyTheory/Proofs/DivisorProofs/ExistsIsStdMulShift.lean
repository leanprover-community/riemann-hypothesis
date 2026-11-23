module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit
namespace GlobalTheory.StdRescale

theorem exists_isStd_mulShift : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∃ a : F, a ≠ 0 ∧ IsStd (ψ.mulShift (algebraMap F (AF F) a)) := by
  intro F _ _ hF ψ h
  haveI := hF
  obtain ⟨a₀, ha₀, hinf⟩ := GlobalTheory.AdeleCharConductor.exists_scaling h
  have him : ∀ (w : InfinitePlace F) (x : F), (w.embedding x).im = 0 := fun w x => by
    have := congrArg Complex.im (GlobalTheory.AdeleCharConductor.embedding_re w x)
    simpa using this.symm
  have hkey : ∀ w : InfinitePlace F, (w.embedding a₀).re * (w.embedding (-a₀⁻¹)).re = -1 := fun w => by
    have := congrArg Complex.re
      (show w.embedding (a₀ * -a₀⁻¹) = -1 by rw [mul_neg, mul_inv_cancel₀ ha₀, map_neg, map_one])
    rw [map_mul, Complex.mul_re, him, him, mul_zero, sub_zero] at this
    simpa using this
  refine ⟨-a₀⁻¹, neg_ne_zero.2 (inv_ne_zero ha₀), ?_, ?_, ?_⟩
  · exact h.1.comp (continuous_const.mul continuous_id)
  · intro x
    rw [AddChar.mulShift_apply, ← map_mul]
    exact h.2.2.1 _
  · intro b hb
    have hu : evI F (pairA F 0 1) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    have hb2 : b.2 = 0 := by
      have h0 := congrArg Prod.snd (hb (pairA F 0 1) hu)
      change (1 : Af F) * b.2 = 0 at h0
      rwa [one_mul] at h0
    have e1 : algebraMap F (AF F) (-a₀⁻¹) * b = pairA F (algebraMap F (Ainf F) (-a₀⁻¹) * b.1) 0 := by
      refine Prod.ext rfl ?_
      change (algebraMap F (AF F) (-a₀⁻¹)).2 * b.2 = 0
      rw [hb2, mul_zero]
    have hterm : ∀ w : InfinitePlace F, (w.embedding a₀).re *
        (InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) (-a₀⁻¹) * b.1) w)).re =
        -(InfinitePlace.Completion.extensionEmbedding w (b.1 w)).re := fun w => by
      rw [show (algebraMap F (Ainf F) (-a₀⁻¹) * b.1) w = algebraMap F (Ainf F) (-a₀⁻¹) w * b.1 w from rfl, map_mul, GlobalTheory.AdeleCharConductor.extensionEmbedding_algebraMap, Complex.mul_re, him,
        zero_mul, sub_zero, ← mul_assoc, hkey, neg_one_mul]
    rw [AddChar.mulShift_apply, e1]
    show psiInf F ψ _ = _
    rw [hinf, GlobalTheory.WrongSignPair.trace_evI]
    simp only [hterm, Finset.sum_neg_distrib]
    push_cast
    ring_nf

end GlobalTheory.StdRescale
