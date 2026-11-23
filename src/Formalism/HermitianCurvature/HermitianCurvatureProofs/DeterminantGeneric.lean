module

public import Formalism.HermitianCurvature.StatementQr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AlgebraicQuantumDeterminant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AnisotropicColumnSums
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorCommutation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorExpansion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem algebraic_quantum_determinant : Qr.AlgDet :=
  qr_algDet_of (qr_algDetBasis_of quantum_jacobi_identity quantum_determinant_vector quantum_minor_covariance)

theorem capelli_hat_frame : Qr.ChatFrame := qr_chatFrame_of frame_minor

theorem determinant_hat : DetHat :=
  qr_detHat_of algebraic_quantum_determinant capelli_hat_frame capelli_right_good left_right_swap

end Formalism.FourierDecayAlt.P
