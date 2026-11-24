module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPEOm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPExh
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPIpSwap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPJFMem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPLoc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPOp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPZeroR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_pairing_identity : RDSPair :=
  rDSPair_of_cut spectral_pairing_inner_swap spectral_pairing_big_cell spectral_pairing_zero_right spectral_pairing_exhaustion spectral_pairing_orbital_membership spectral_pairing_operator
    spectral_pairing_locality

end Formalism.FourierDecayAlt.P.CutSE
