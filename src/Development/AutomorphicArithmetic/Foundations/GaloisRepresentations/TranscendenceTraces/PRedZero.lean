module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.redZero_of :
    RedZero := by
  intro Q q _ _ hqQ i
  obtain ⟨f, hf_nat, hf_gen⟩ := GlobalTheory.EtC.RedExists.twRed_sec Q q hqQ i
  refine ⟨f, hf_nat, ?_⟩
  intro U a
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) _ U).1
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U _ _ ((GlobalTheory.T.tateTwist_sections_locally_generated Q i).1 U a) ?_
  intro V g h
  rw [SemiMap.nat, ← map_res, ← map_res, hf_nat]
  rcases h with h | ⟨ζ, c, h⟩
  · rw [h]
    simp only [Sec.map, map_zero]
  · rw [h]
    have key := GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i V ζ (GlobalTheory.EtC.RedExists.powPrim hqQ ζ) rfl
    simp only [GlobalTheory.EtC.resGen] at key
    simp only [Sec.map, map_nsmul, map_zsmul] at key ⊢
    rw [key, hf_gen V ζ (GlobalTheory.EtC.RedExists.powPrim hqQ ζ) rfl]
