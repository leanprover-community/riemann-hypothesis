module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.AutomorphicFormsFiniteUnitaryIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviBlockCentreFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreFiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreInducedUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RallisTowerUnitary
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace GlobalTheory.ThK

structure KP : Prop where

  base : GlobalTheory.FunPr.Hypotheses₂

  howeDualityUnitary : GlobalTheory.Published.HoweDualityUnitary

  howeDualityReal : GlobalTheory.Published.HoweDualityReal

  automorphicFormsUnitary : GlobalTheory.Published.AutomorphicFormsUnitary

  eisensteinIsotropicLine : GlobalTheory.Published.EisensteinIsotropicLine

  genericityGL : GlobalTheory.Published.GenericityGL

  complementaryThetaInert : GlobalTheory.Published.ComplementaryThetaInert

  siegelSetUnitary : GlobalTheory.Published.SiegelSetUnitary

  minguezThetaGL : GlobalTheory.Published.MinguezThetaGL

  jacquetShalika : GlobalTheory.Published.JacquetShalika

  discreteSpectrumGL : GlobalTheory.Published.DiscreteSpectrumGL

  heckeTateFunctionalEquation : GlobalTheory.Published.HeckeTateFunctionalEquation

  automorphicFormsFiniteUnitary : GlobalTheory.Published.AutomorphicFormsFiniteUnitary

  geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration

  cuspidalSpectrumGL : GlobalTheory.Published.CuspidalSpectrumGL

  siegelWeilAnisotropicCM : GlobalTheory.Published.SiegelWeilAnisotropicCM

  siegelWeilAnisotropicHermitian : GlobalTheory.Published.SiegelWeilAnisotropicHermitian

  siegelEisensteinDoubled : GlobalTheory.Published.SiegelEisensteinDoubled

  leviCentreFiniteUnitary : GlobalTheory.Published.LeviCentreFiniteUnitary

  leviBlockCentreFinite : GlobalTheory.Published.LeviBlockCentreFinite

  leviCentreInducedUnitary : GlobalTheory.Published.LeviCentreInducedUnitary

  eisensteinResidueLine : GlobalTheory.Published.EisensteinResidueLine

  rallisTowerUnitary : GlobalTheory.Published.RallisTowerUnitary

end GlobalTheory.ThK
