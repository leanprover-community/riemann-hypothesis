module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem genPt_exists_spec {S : Scheme.{0}} (s : S) : ∃ t : S, t ⤳ s ∧ GenPt t := by
  have hC : IsIrreducible (irreducibleComponent s) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent s) := isClosed_irreducibleComponent
  have ht : IsGenericPoint hC.genericPoint (irreducibleComponent s) :=
    hC.isGenericPoint_genericPoint hcl
  refine ⟨hC.genericPoint, ht.specializes mem_irreducibleComponent, ?_⟩
  intro t' h'
  have hsub : irreducibleComponent s ⊆ closure {t'} := by
    rw [← ht.def]
    exact h'.closure_subset
  have heq : closure ({t'} : Set S) = irreducibleComponent s :=
    eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible hsub
  have ht' : IsGenericPoint t' (irreducibleComponent s) := heq
  exact ht'.eq ht

private theorem genPt_open {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (s : U) :
    GenPt (j s) ↔ GenPt s := by
  have he := j.isOpenEmbedding
  constructor
  · intro h t hts
    exact he.injective (h _ (hts.map he.continuous))
  · intro h t hts
    have hmem : t ∈ Set.range j := hts.mem_open he.isOpen_range ⟨s, rfl⟩
    obtain ⟨t', rfl⟩ := hmem
    have : t' ⤳ s := he.isInducing.specializes_iff.1 hts
    rw [h t' this]

private theorem genPt_integral (S : Scheme.{0}) [IsIntegral S] (s : S) :
    GenPt s ↔ s = genericPoint S := by
  constructor
  · intro h
    exact (h _ (genericPoint_specializes s)).symm
  · rintro rfl t ht
    exact (ht.antisymm (genericPoint_specializes t)).eq

theorem UpperTheory.Gal.TranscendenceTraces.genBasic_of :
    GenBasic := by
  refine ⟨fun S => ?_, fun j _ s => genPt_open j s, fun S _ s => genPt_integral S s⟩
  rw [dense_iff_inter_open]
  rintro N hN ⟨s, hs⟩
  obtain ⟨t, hts, ht⟩ := genPt_exists_spec s
  exact ⟨t, hts.mem_open hN hs, ht⟩
