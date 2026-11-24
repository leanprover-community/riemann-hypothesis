module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem kapJ_eq (P : M.Par) (j : ℕ) : kapJ P j = levelZeroKernel P.k P.r j := rfl

theorem headJ_of (hW : WordInd) (hB : HeadBridge) : HeadJ := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hγ' φ hφ t ht e
  obtain ⟨X, _, μ, ℓ, Zx, Fx, Dm, φx, hDm, hDmsub, hR, hZ, hφx, hL, hRt⟩ :=
    hB Wp Wq P p F j hj w h hh γ hF hw hγ hγ' φ hφ t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (by simp)).2
  rw [hL, hRt]
  congr 1
  funext x
  rw [hW P.k P.r j hj _ _ (Wq →L[ℂ] Wp) Dm (Fx x) p.T.base.z_mem p.T.base.z'_mem hDm hDmsub (hR x) (Zx x) γ
    (hZ x).1 hγ (hZ x).2 w (φx x) (hφx x) t ht0 e, kapJ_eq]

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
