module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSmoothCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymExp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermZeroOfTrace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermZeroRight
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

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_zero_of_lieW {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (z : Fin (2 * r + k + 1) → ℂ)
    (hW : ∀ X ∈ lieOf (UWset k r z), (Matrix.trace (ζ * X)).re = 0)
    (u v : Fin (2 * r + k + 1) → ℂ) (hu : inWb k r u) (hv : inWb k r v)
    (huz : herm (Hpk k r) u z = 0) (hvz : herm (Hpk k r) v z = 0) :
    herm (Hpk k r) (ζ *ᵥ u) v = 0 := by
  refine herm_zero_of_trace hζ u v (hW _ (xuv_lieW z u v hu hv huz hvz)) (hW _ ?_)
  refine xuv_lieW z u _ hu (inWb_smul _ hv) huz ?_
  rw [herm_smul_left, hvz, mul_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

end Formalism.FourierDecayAlt.P.CutMP.JfS
