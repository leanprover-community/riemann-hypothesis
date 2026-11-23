module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.GlobalComplexCoefficients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterWeightMapStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticLocalIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G2OfLocalOrbitCharacterStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitalSignAlmostEverywhereStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.InfinitesimalWeightZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Count1
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

namespace PositivityTheory.Rg.BcB.F.F0

theorem complex_coefficient_multiplicity_holds : PositivityTheory.Rg.BcB.G8.GlobalComplexCoefficients := GlobalTheory.T.globalComplexCoefficients_of_local_orbit_character GlobalTheory.T.elliptic_local_identity GlobalTheory.T.orbital_sign_almost_everywhere GlobalTheory.T.character_weight_map

theorem chain_existence_of_global_character (h4 : PositivityTheory.Rg.BcB.G8.G4) : PositivityTheory.Rg.BcB.F.ChainEx :=
  chainEx_of complex_coefficient_multiplicity_holds PositivityTheory.Rg.BcB.G3.g3 h4

end PositivityTheory.Rg.BcB.F.F0
