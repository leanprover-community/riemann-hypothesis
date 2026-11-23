module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsSubspacesContaining
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.sum_integralIndicator_cosets_subspaces_containing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D') RK, IsRepsK (GlobalTheory.GLDoubling.torusElt k D' ϖ (indic s)) RK → ∀ y : Matrix D' D k, ((¬ ∀ i j, y i j ∈ 𝒪[k]) → ∑ g ∈ RK, GlobalTheory.ParHecke.intInd ((g⁻¹).1 * y) = 0) ∧ ∀ y₀ : Matrix D' D 𝒪[k], y = y₀.map (algebraMap 𝒪[k] k) → ∑ g ∈ RK, GlobalTheory.ParHecke.intInd ((g⁻¹).1 * y) = (Nat.card {U : Submodule 𝓀[k] (D' → 𝓀[k]) // LinearMap.range (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ≤ U ∧ Module.finrank 𝓀[k] U + s.card = Fintype.card D'} : ℂ) := by
  first | exact @GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up | exact GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up | (intros; apply GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up <;> assumption)
