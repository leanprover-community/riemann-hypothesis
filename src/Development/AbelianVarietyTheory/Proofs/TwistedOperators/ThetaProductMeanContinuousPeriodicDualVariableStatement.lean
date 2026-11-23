module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProductMeanContinuousPeriodicDualVariable
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaProductMean_continuous_periodic_dualVariable : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ P G, IsThetaFunO ψ V W P → IsThetaFunO ψ V W G → Continuous (fun t : Mx D W.rank r => ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) ∧ ∀ γ ∈ ratMx D W.rank r, ∀ t : Mx D W.rank r, (∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  first | exact @GlobalTheory.TwistThetaMean.mean_continuous_periodic | exact GlobalTheory.TwistThetaMean.mean_continuous_periodic | (intros; apply GlobalTheory.TwistThetaMean.mean_continuous_periodic <;> assumption)
