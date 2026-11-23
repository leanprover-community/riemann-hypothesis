module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.InfLifts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteOrderTwists
public import Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.NotRealComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.infStep :
    UpperTheory.Gal.InertialTypesAlt.StableOf → InfStep := by
  intro hS K M _ _ _ _ _ _ _ _ hp n hn π P hw τ
  obtain ⟨hconj, -⟩ := hS K M hp n hn π P hw
  have hK : IsTotallyComplex K := inferInstance
  obtain ⟨-, hD, hF⟩ := UpperTheory.ConvolutionTheory.cbcc K M hp hK n hn
  obtain ⟨Q, hQw, hQinf, -⟩ := hD (.cx P) hconj
  cases Q with
  | re Q => exact (PositivityTheory.Pf1.CLGD.K.LKW.not_real_complex K inferInstance hK).elim
  | cx π₁ =>
    obtain ⟨η, hη, hi⟩ := (hF (.cx π) (.cx P) hconj hw).2 (.cx π₁) hQw
    have hP := GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk P) τ
    have h2 : π₁.HasInfChar (τ.comp (algebraMap K M)) ((CG.mk P).infChar τ) := hQinf τ _ hP
    have h3 : (CG.mk π₁).infChar (τ.comp (algebraMap K M)) = (CG.mk P).infChar τ :=
      CG.HasInfChar.infChar_eq h2
    have h4 : CG.mk (π.twist η) = CG.mk π₁ := Quotient.sound hi
    have h5 : (CG.mk (π.twist η)).infChar (τ.comp (algebraMap K M)) =
        (CG.mk π).infChar (τ.comp (algebraMap K M)) := by
      rcases hη with rfl | hη
      · exact GlobalTheory.RoadU.FinTwist.infChar_twist π
          (GlobalTheory.RoadU.FinTwist.isAlg_zero (m := 1) one_pos (pow_one _)) _
      · exact GlobalTheory.RoadU.FinTwist.infChar_twist π
          (GlobalTheory.RoadU.FinTwist.isAlg_zero hp.pos hη.2.1) _
    rw [← h3, ← h4, h5]
