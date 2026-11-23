module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOOneOne
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceBoxProductInnerFactorizes
import Formalism.DoubleCosetMeasures.StatementZ
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace


theorem _root_.GlobalTheory.T.doubledSpace_boxProduct_inner_factorizes : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D),
    ∃ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T))) (𝓕 : Set (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T)))
      (μ₁ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕₁ : Set (Formalism.IndefR.Datum.WO S T)),
      μ.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL (GlobalTheory.Doubling.dblSp T) S) 𝓕 μ ∧
      μ₁.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL T S) 𝓕₁ μ₁ ∧
      ∀ a a' b b' : Formalism.IndefR.Datum.WO S T → ℂ, Formalism.IndefR.Datum.IsThetaFunO ψ S T a → Formalism.IndefR.Datum.IsThetaFunO ψ S T a' →
        Formalism.IndefR.Datum.IsThetaFunO ψ S T b → Formalism.IndefR.Datum.IsThetaFunO ψ S T b' →
        ∫ w in 𝓕, GlobalTheory.DblBox.box a b w * star (GlobalTheory.DblBox.box a' b' w) ∂μ =
          (∫ u in 𝓕₁, a u * star (a' u) ∂μ₁) * star (∫ u in 𝓕₁, b u * star (b' u) ∂μ₁) := by
  first | exact @GlobalTheory.DblBoxHaar.box_integral | exact GlobalTheory.DblBoxHaar.box_integral | (intros; apply GlobalTheory.DblBoxHaar.box_integral <;> assumption)
