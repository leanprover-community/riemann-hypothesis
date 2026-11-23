module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementR
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.BridgeJ
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.DifferenceLinearCoeff
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.EqWSerSubst
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Laurent
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ToLTDenMulInv
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.TwoTorsionIntegral
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

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

namespace Rr

variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem wpPrimeInZ : expSer W ^ 3 * (-2 + X ^ 3 * derivative (wpReg W))
    = X ^ 3 * (-2 * (xS W).subst (expSer W) + C W.a₁ * expSer W * (xS W).subst (expSer W)
        + C W.a₃ * expSer W ^ 3) := by
  have h1 := (wpODE K W).1
  have h2 := (wpPrimeShape K W).1
  have hq := Two.exp_mul_inv W
  have hz : (toL X : LaurentSeries K) * uPow (-1) = 1 := Plus.toL_X_mul
  have hy : (yS W).subst (expSer W) = -(xS W).subst (expSer W) := by
    rw [yS, ← coe_substAlgHom (Two.he W), map_neg]
  rw [h2, xZ, yZ, hy, Plus.uPow_neg_three] at h1
  apply toL_injective
  simp only [map_mul, map_add (f := _), map_neg, map_pow, map_ofNat, toL_C] at h1 ⊢
  generalize toL ((xS W).subst (expSer W)) = xs at h1 ⊢
  generalize toL (derivative (wpReg W)) = P at h1 ⊢
  generalize (toL (expSer W))⁻¹ = q at h1 hq ⊢
  generalize toL (expSer W) = E at hq ⊢
  generalize (uPow (-1) : LaurentSeries K) = zi at h1 hz
  generalize (toL X : LaurentSeries K) = Z at hz ⊢
  linear_combination E ^ 3 * Z ^ 3 * h1 + 2 * E ^ 3 * ((Z * zi) ^ 2 + Z * zi + 1) * hz
    - Z ^ 3 * (2 * xs * ((E * q) ^ 2 + E * q + 1) - HahnSeries.C W.a₁ * E * xs * (E * q + 1)) * hq

end Rr

theorem weierstrass_p_prime_unit : WpPrimeInU.{u} := by
  intro K _ _ W
  obtain ⟨l0, -, -, -⟩ := logSpec K W
  obtain ⟨-, -, -, hel, -⟩ := expSpec K W
  have hl : HasSubst (logSer W) := HasSubst.of_constantCoeff_zero' l0
  have h := congrArg (ISer.subHom (logSer W) l0) (Rr.wpPrimeInZ W)
  have k := subst_comp_subst_apply (Two.he W) hl (xS W)
  rw [hel, X_subst] at k
  simp only [map_mul, map_add (f := _), map_neg, map_pow, map_ofNat, ISer.subHom_C, ISer.subHom_X] at h
  simp only [ISer.subHom_apply, hel, k] at h
  exact h

theorem three_curves_relation : BridgeCurve3 := by
  intro K _ _ _ W hW
  refine ⟨weierstrass_p_prime_unit K W, ?_⟩
  obtain ⟨-, ⟨e, he, he0, hdet⟩, -⟩ :=
    cube_mem' K W (Formalism.G.unitBall K) hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2
  refine ⟨e, Bridge.integral_of_mvCoeff he, he0, ?_⟩
  have hy : ∀ i : Fin 3, (yS W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K)
      = -(xS W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) := by
    intro i
    have hs : HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) := HasSubst.X i
    rw [yS, ← coe_substAlgHom hs, map_neg]
  simp only [hy] at hdet
  unfold Formalism.L2.Th1.B.F3 Formalism.InvariantFactorPaths.G7.in3 Formalism.InvariantFactorPaths.G7.at1
  exact hdet

end Formalism.L2.Th1.A
