module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section
namespace GlobalTheory.CoverDS

theorem unitEquiv_of_dsUnique : GlobalTheory.Dec.DSUnique → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R R' : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasParam R' lam → UnitEquiv R R' := by
  intro hU p q hn T R R' lam hl hR hR'
  have h0 : 0 < p + q := hn
  obtain ⟨P, e, -, h, rfl | rfl⟩ := GlobalTheory.RealPar.isParam_cases hl
  · obtain ⟨σ, hσ, hP⟩ := (GlobalTheory.RealPar.hasParam_iff_factors R h0 P h).1 hR
    obtain ⟨σ', hσ', hP'⟩ := (GlobalTheory.RealPar.hasParam_iff_factors R' h0 P h).1 hR'
    obtain ⟨V, hV⟩ := hU (p + q) P.sgn P.lam R.U.H σ R'.U.H σ' P.hc hP hP'
    refine ⟨V, fun x v => ?_⟩
    rw [hσ x, hσ' x]
    exact hV _ (h.cov_mem T x) v
  · obtain ⟨σ, hσ, hP⟩ := (GlobalTheory.RealPar.hasParam_half_iff R h0 P h).1 hR
    obtain ⟨σ', hσ', hP'⟩ := (GlobalTheory.RealPar.hasParam_half_iff R' h0 P h).1 hR'
    obtain ⟨V, hV⟩ := hU (p + q) P.sgn P.lam R.U.H σ R'.U.H σ' P.hc hP hP'
    refine ⟨V, fun x v => ?_⟩
    rw [hσ x, hσ' x, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]
    rw [hV _ (h.cov_mem T x) v]

end GlobalTheory.CoverDS

end
