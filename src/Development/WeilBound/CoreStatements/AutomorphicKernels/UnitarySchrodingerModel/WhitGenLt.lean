module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.LocFin2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.CpowProdOfReal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.UnrWhitOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.FactorCore
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.WXMain
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.ChapterTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Imports
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.PfSWUS

open PositivityTheory.SiegelWeilFormula

theorem whitGenLt : PositivityTheory.SiegelWeilFormula.Gen.WhitGenLt :=
  Gen.whitGenLtOf SwLocFin.locFin2 Gunr.unrWhit (GReal.realWhit_of PositivityTheory.Rg.Sw.WR.wr) GFac.factorX
    PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA

end PositivityTheory.PfSWUS
