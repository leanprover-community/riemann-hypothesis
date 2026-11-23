module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartInProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical


theorem _root_.GlobalTheory.T.swap_twist_compact_part_in_prod : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → d ∈ K → d' ∈ K →
  cptPart (twCent (MonoidHom.id H) (d * σ d')) ≤ K →
  (∀ g : H, g⁻¹ * (d * σ d') * MonoidHom.id H g ∈ K → ∃ t ∈ twCent (MonoidHom.id H) (d * σ d'), t⁻¹ * g ∈ K) →
  cptPart (twCent (swTw σ) (d, d')) ≤ K.prod K ∧
    ∀ y : H × H, y⁻¹ * (d, d') * swTw σ y ∈ K.prod K → ∃ t ∈ twCent (swTw σ) (d, d'), ∃ k ∈ K.prod K, y = t * k := by
  first | exact @GlobalTheory.CompanionTheory.SplitUnit.main | exact GlobalTheory.CompanionTheory.SplitUnit.main | (intros; apply GlobalTheory.CompanionTheory.SplitUnit.main <;> assumption)
