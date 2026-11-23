module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainUnfoldingTwoSums
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ValueFormula
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis


theorem _root_.GlobalTheory.T.fundamental_domain_unfolding_two_sums : ∀ {A X Y U : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A)
    (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] [Countable U] (c : X → Y) (y0 : Y)
    (F : X → A → ℂ) (F0 : U → A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam)
    (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1)
    (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1)
    (Um : X → ℝ) (_ : Summable Um) (τ : Λ → X ≃ X)
    (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q)
    (_ : ∀ b, ∃ l : Λ, ∀ q, ‖F q b‖ ≤ Um (τ l q))
    (e : Λ × U → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e)
    (_ : ∀ (l l' : Λ) u, τ l' (e (l, u)) = e (l' + l, u))
    (_ : ∀ (l : Λ) u b, F (e (l, u)) b = F0 u ((l : A) + b))
    (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b),
    (∀ u, Integrable (F0 u) lam ∧ ∫ b, ‖F0 u b‖ ∂lam ≤ ∑' l : Λ, Um (e (l, u))) ∧
    HasSum (fun u => ∫ b, F0 u b * ch b ∂lam) (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) := by
  exact @GlobalTheory.CompanionTheory.UnfoldFam.unfold_fam
