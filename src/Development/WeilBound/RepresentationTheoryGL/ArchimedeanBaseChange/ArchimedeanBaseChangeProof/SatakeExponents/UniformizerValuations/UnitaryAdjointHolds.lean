module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnitHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalAlgebraHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebraStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.SphStarUPlug
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SphericalHeckeUnitary.PuSphHecke
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

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.U

theorem unitary_words_holds : UWord :=
  UU.uWordOfU GlobalTheory.T.diagonal_algebra_holds GlobalTheory.T.local_algebra_holds (GlobalTheory.T.spherical_one_of_local_algebra GlobalTheory.T.local_algebra_holds) GlobalTheory.T.compact_unit_holds PositivityTheory.Rg.BcB.F.Fok.sphStarU

theorem unitary_adjoint_holds : UAdj :=
  UU.uAdjOfU GlobalTheory.T.diagonal_algebra_holds GlobalTheory.T.local_algebra_holds (GlobalTheory.T.spherical_one_of_local_algebra GlobalTheory.T.local_algebra_holds) GlobalTheory.T.compact_unit_holds PositivityTheory.Rg.BcB.F.Fok.sphStarU

end PositivityTheory.Rg.BcB.F.U
