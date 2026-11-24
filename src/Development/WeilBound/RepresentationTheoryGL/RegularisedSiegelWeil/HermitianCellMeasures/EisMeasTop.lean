module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulLeftFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisMeas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermScaleMain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralLeOfMinor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbEx
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopX
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

namespace PositivityTheory.Rg.Rsw.Em

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

theorem eisMeas : IdemEx → BumpEx → Major → FixW → FixTh → ThProd → MuCell → FibEx → RCell → PosExt → ApproxId → EisMeas :=
  fun hI hB hM hW hT hP hC hF hR hE hA =>
  have hX := GlobalTheory.CompanionTheory.RswEmTop.topX
  have hRi := GlobalTheory.CompanionTheory.AlgRich.algRich hI hB hX
  have hS := GlobalTheory.CompanionTheory.SigL.main hI hX
  GlobalTheory.CompanionTheory.EisE.eisMeas hI hB hM hW hT hP hC hF hR hX hRi hS
    (GlobalTheory.CompanionTheory.OrbExist.orbEx hI hA (GlobalTheory.CompanionTheory.EisDens.dens_main hE) hX hRi (GlobalTheory.CompanionTheory.AlgStab.algStab hI) hS (GlobalTheory.CompanionTheory.HermSc.hermScale_main hI hX))

end PositivityTheory.Rg.Rsw.Em
