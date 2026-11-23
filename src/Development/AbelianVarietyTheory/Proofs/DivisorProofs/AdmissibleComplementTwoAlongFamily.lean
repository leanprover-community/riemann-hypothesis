module

public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDegreeCountAlongFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleOffTypeFamilyBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegConstDiscriminantTermLeBudgetFamilyAStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimesLossLogSumAdmissibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalRamifiedBoundAlongFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeSizesLeBudgetFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeValuationSumEqLogGapFamilyStatement
public import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

theorem familySecondComplementInputs_of_tuSize_of_dGamSize : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm →
    Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm := by
  intro eps Fm h0 h1 hT hG
  obtain ⟨Cdeg, xd, -, hdeg⟩ := GlobalTheory.T.exists_degreeCountBound_of_eps_lt_one_div_52 Fm h0 h1
  obtain ⟨Cg, xg, hCg, hsz⟩ := GlobalTheory.T.typePrime_sizes_le_budget_family Fm h0 h1 hG Cdeg
  obtain ⟨CT, xT, -, hoT⟩ := GlobalTheory.T.admissible_off_type_family_bound Fm h0 h1 hT
  obtain ⟨CG, xG, -, hoG⟩ := GlobalTheory.T.exists_const_stabiliserLog_bound_along_family Fm h0 h1 hT hG
  obtain ⟨Cd, xD, -, hoD⟩ := GlobalTheory.T.offDiagonalRamified_bound_along_family' Fm h0 h1
  obtain ⟨CI, xI, -, hoI⟩ := GlobalTheory.T.inertPrimeLossBound_eventually Fm h0 h1
  refine ⟨Cdeg, Cg, CT, CG, Cd, CI, max xd (max xg (max xT (max xG (max xD xI)))), hCg, ?_⟩
  intro x hx0 hx i
  have a1 : xd ≤ x := (le_max_left _ _).trans hx0
  have r1 := (le_max_right _ _).trans hx0
  have a2 : xg ≤ x := (le_max_left _ _).trans r1
  have r2 := (le_max_right _ _).trans r1
  have a3 : xT ≤ x := (le_max_left _ _).trans r2
  have r3 := (le_max_right _ _).trans r2
  have a4 : xG ≤ x := (le_max_left _ _).trans r3
  have r4 := (le_max_right _ _).trans r3
  have a5 : xD ≤ x := (le_max_left _ _).trans r4
  have a6 : xI ≤ x := (le_max_right _ _).trans r4
  exact ⟨fun u j h => (Fm.D x i).T_ne_g u j h.symm, GlobalTheory.T.normDecompositionCond_famP Fm x hx i, hdeg x a1 hx i, hsz x a2 hx i,
    hoT x a3 hx i, hoG x a4 hx i, hoD x a5 hx i, hoI x a6 hx i⟩

end GlobalTheory
