module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOrientedModelEqOfRealAdelicPoints
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section


theorem _root_.GlobalTheory.T.thetaFunction_orientedModel_eq_of_realAdelicPoints : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f₁ f₂ : WO S T → ℂ),
    IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ →
    (∀ X : Matrix (Fin T.rank) (Fin S.rank) D.host.E, f₁ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X) = f₂ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X)) →
    f₁ = f₂ := by
  first | exact @GlobalTheory.ThetaUniqReal.eq_of_eq_realPt | exact GlobalTheory.ThetaUniqReal.eq_of_eq_realPt | (intros; apply GlobalTheory.ThetaUniqReal.eq_of_eq_realPt <;> assumption)
