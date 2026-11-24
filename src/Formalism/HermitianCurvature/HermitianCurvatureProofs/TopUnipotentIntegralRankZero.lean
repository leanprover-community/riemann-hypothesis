module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CompactCoefficientAppend

theorem locPt_zero {h : C.LPt} {n : ℕ} (hh : D.IsLocPt h n) (hn : n = 0) : h = [] := by
  rcases h with _ | ⟨b, t⟩
  · rfl
  · exfalso
    have h1 := (hh.1 b (by simp)).1
    have h2 := hh.2
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_cons] at h2
    omega

theorem top_unipotent_integral_zero (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r)) (hR : P.r = 0)
    (hF : KB.CptCoef p.T.base F) (hζ : ζ ≠ 0)
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) :
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)] := by
  have hh0 : h = [] := locPt_zero hh hR
  subst hh0
  rcases P with ⟨k, r, T, T', u, u'⟩
  dsimp only at hR
  subst hR
  have e1 : p.ν' = ν'r := by
    rw [← hν]
    funext i
    simp only [D.castV, liftVec]
    rw [dite_eq_left (by simp; omega)]
    exact congrArg ν'r (Fin.ext (by simp))
  have e2 : p.m₀ = m₀r := by
    rw [← hm]
    ext i j
    simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]
    rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega)]
    exact congrArg₂ m₀r (Fin.ext (by simp)) (Fin.ext (by simp))
  have e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' F []) = F := by
    funext γ
    simp only [D.castF]
    refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem F _).trans ?_
    exact congrArg F (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ)
  simp only [List.nil_append]
  rw [e3]
  subst e1
  subst e2
  rfl

end Formalism.FourierDecayAlt.P.CompactCoefficientAppend

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
