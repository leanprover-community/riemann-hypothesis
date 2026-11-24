module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimateStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinGluingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinIwasawaEstimateStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopologyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionExistsStatement
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
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

namespace PositivityTheory.Rg.SwEis.Hd

open PositivityTheory.RgEis.Hd

theorem eisStrong : PositivityTheory.Rg.Sw.Glob.EisStrong :=
  GlobalTheory.T.eisenstein_topology dict dictInf (cmGood_of stdGood dict dictInf) grpTop bdetLaw extLaw (parLaw_of bdetLaw extLaw grpTop)
    sgAll GlobalTheory.T.standard_section_exists (GlobalTheory.T.eisenstein_iwasawa_estimate (GlobalTheory.T.chart_section_exists dict dictInf GlobalTheory.T.standard_section_exists)) (GlobalTheory.T.scalar_section_exists secLaw (wallLaw_of secLaw))
    (GlobalTheory.T.eisenstein_far_estimate htLip) GlobalTheory.T.eisenstein_gluing

end PositivityTheory.Rg.SwEis.Hd
