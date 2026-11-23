module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatImpliesFieldGeneration
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBruhatDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HalfTrAddSwap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupInductionGenerators
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceInnerMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationCovarianceLevi
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covar_of (hB : Bruhat) (hR : RatPts) : Covar := by
  intro D n V ψ χ θ μ ω hS γ hγ v Φ Ψ hΨ
  obtain ⟨-, -, -, -, -, -, ⟨𝓕, hC⟩, hW⟩ := hS
  have hF : FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) n :=
    FieldGenPf.fieldGen_of_bruhat hB D.host.E _ (fun x => star_star x) two_ne_zero n
  exact Transfer.ratPts_transfer hR D n hF (CovAt ψ V ω) (fun _ _ h₁ h₂ => covAt_mul h₁ h₂)
    (fun g a h => covAt_levi D n V ψ χ θ μ ω hW g a h)
    (fun g b hb h => covAt_unip D n V ψ χ θ μ ω hW g b hb h)
    (fun g h => covAt_weyl D n V ψ χ θ μ ω hW hC.1 g h) γ hγ v Φ Ψ hΨ

theorem covar : Covar :=
  covar_of GlobalTheory.CompanionTheory.BruhatCell.bruhat GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn

end GlobalTheory.CompanionTheory.EisCovar
