module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeTheoremOfPerfectStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreadingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOutStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LbSpreadsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectOfModelsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpreadStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOutStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

set_option autoImplicit false

namespace GlobalTheory.SpreadingModels

theorem cubeTheorem_holds : GlobalTheory.Published.CubeTheorem :=
  GlobalTheory.T.cube_theorem_of_perfect (GlobalTheory.T.perfect_of_models (GlobalTheory.T.has_model_of_spreading GlobalTheory.T.scheme_models_spread GlobalTheory.T.smooth_spreads_out GlobalTheory.T.isProper_spreads_out GlobalTheory.T.line_bundle_spreads_out'))

end GlobalTheory.SpreadingModels
