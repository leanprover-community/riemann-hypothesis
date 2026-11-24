module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyOne
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def xvL (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O :=
  ∑ b : Fin (X.m + 1), C (dW O w (hhLetters X.TT) 1 (topStart X j, true) b) * MvPolynomial.X ((topStart X j, true), b) *
    C (psiO X.p X.n' O ((topStart X j : X.TT).val.val : ℤ) (g⁻¹ b a))

def locExpr (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j0 : Fin (numSeg X.TT)) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O :=
  xvL X O w g j0 0 * ∏ c : Fin X.m, (∏ j : Fin (numSeg X.TT), xvL X O w g j 0 ^ (X.p ^ segG X.TT j - 1) -
    ∏ j : Fin (numSeg X.TT), xvL X O w g j c.succ ^ (X.p ^ segG X.TT j - 1))

theorem liftSubst_start (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) g (MvPolynomial.X ((topStart X j, true), a)) =
      MvPolynomial.map (algebraMap O (KK O)) (xvL X O w g j a) := by
  rw [liftSubst_X_vec X.p X.n' O w (hhLetters X.TT) 1 g hg (topStart X j, true) a rfl]

  simp only [xvL, map_sum, map_mul, map_C, map_X, sigMat_apply]
  rfl

theorem locR_lift (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (j0 : Fin (numSeg X.TT)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) g (locR O X j0) =
      MvPolynomial.map (algebraMap O (KK O)) (locExpr X O w g j0) := by
  unfold locR locC locExpr
  simp only [map_mul, map_prod, map_sub, map_pow, liftSubst_start X O w g hg]

def LocalDivisibilityBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      (C S.w : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O) ∣ locExpr X O S.w g j0

theorem loc4Ord_of (h : LocalDivisibilityBound) : LocalOrderBound := by
  intro X _ O _ _ _ _ S hS hD h2 j0 g hg hpl
  obtain ⟨Q, hQ⟩ := h X O S hS hD h2 j0 g hg hpl
  unfold InWjRg
  rw [locR_lift X O S.w g hg j0, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

end Formalism.MainNotions.ColumnSystems.Pf
