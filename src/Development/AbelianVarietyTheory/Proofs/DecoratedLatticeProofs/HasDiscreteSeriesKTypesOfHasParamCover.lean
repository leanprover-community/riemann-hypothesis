module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesCoverOfFactorsThroughCoveStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfSqrtDetTwistStatement
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

namespace GlobalTheory.CoverDS

theorem hasTypes_of_hasParam_of_group : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar →
    ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ),
      IsParam lam → HasParam R lam → HasTypes R lam := by
  intro hL hK hD p q hpq T R lam hlam hR
  have hn : 0 < p + q := hpq
  obtain ⟨P, e, -, hB, hcase⟩ := isParam_cases hlam
  rcases hcase with rfl | rfl
  · obtain ⟨σ, hf, hds⟩ := (hasParam_iff_factors R hn P hB).1 hR
    exact GlobalTheory.T.hasDiscreteSeriesKTypes_cover_of_factorsThroughCovering hL hK hD p q (p + q) e P T R σ hB hf hds
  · obtain ⟨σ, hπ, hds⟩ := (hasParam_half_iff R hn P hB).1 hR
    have hf : Factors (Cover.twist R).U e σ := (factors_twist_iff R σ).2 hπ
    exact GlobalTheory.T.hasDiscreteSeriesKTypes_of_sqrtDetTwist p q T R (blockPar P e)
      (GlobalTheory.T.hasDiscreteSeriesKTypes_cover_of_factorsThroughCovering hL hK hD p q (p + q) e P T (Cover.twist R) σ hB hf hds)

end GlobalTheory.CoverDS
