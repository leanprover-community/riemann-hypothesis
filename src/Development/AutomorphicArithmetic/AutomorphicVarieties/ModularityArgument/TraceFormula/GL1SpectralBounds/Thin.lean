module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.SecondFromFirstStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.LyingOverPrimes.InertThin
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.PrimeNonSummability.PrimeSumConvergesAndDiverges
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.IntegralityGoodReduction
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

theorem UpperTheory.V.Z.Tf.GOne.thin :
    Thin := by
  intro E _ _ _
  have hs : Summable fun w : {w : HeightOneSpectrum (𝓞 E) // ¬ IsSplitAt w} =>
      ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)⁻¹ := PositivityTheory.Rg.BcB.Desc.inertThin_holds E
  refine ⟨hs, fun hfin => ?_⟩
  apply PositivityTheory.RgJS.PrimeSumConvergence.not_summable_all (E := E)
  have hf : Summable fun w : {w : HeightOneSpectrum (𝓞 E) | IsSplitAt w} =>
      ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)⁻¹ :=
    hfin.summable (fun w : HeightOneSpectrum (𝓞 E) => ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹)
  exact (summable_subtype_and_compl (f := fun w : HeightOneSpectrum (𝓞 E) => ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹)
    (s := {w : HeightOneSpectrum (𝓞 E) | IsSplitAt w})).1 ⟨hf, hs⟩
