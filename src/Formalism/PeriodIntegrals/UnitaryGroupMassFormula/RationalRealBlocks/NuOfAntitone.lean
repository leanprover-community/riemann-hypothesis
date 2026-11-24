module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.EvenStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.Bridge
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.GradedWeylDivisibility.StatementA

@[expose] public section

open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal.UnitaryGroupMassFormula

theorem nuOf_antitone {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  have h1 := h hab
  exact Int.toNat_le_toNat (by omega)

theorem det_map_ne {LL : Type} [Field LL] (embLL : LL →+* ℂ) {k : ℕ} (M0 : GL (Fin k) LL) :
    (M0.1.map embLL).det ≠ 0 := by
  have hu : IsUnit M0.1.det := (Matrix.isUnit_iff_isUnit_det _).mp M0.isUnit
  have hm := RingHom.map_det embLL M0.1
  rw [RingHom.mapMatrix_apply] at hm
  rw [← hm]
  exact (map_ne_zero embLL).mpr hu.ne_zero

theorem evenStep : EvenStep := by
  intro m LL _ embLL lam hl M0 f hf
  refine ⟨C (M0.1.det ^ (-lam (Fin.last m))) * Formalism.GradedWeylDivisibility.rowAct LL (↑M0⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)
    (MvPolynomial.map (Int.castRingHom LL) f), ?_, fun y _ => ?_⟩
  · rw [MvPolynomial.C_mul']
    exact Submodule.smul_mem _ _ (s2 _ _ _ _ (s1 _ _ _ (nuOf_antitone hl) f hf))
  · have hd := det_map_ne embLL M0
    have hmul : (↑M0⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map embLL * (M0.1.map embLL * y) = y := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, M0.inv_mul, Matrix.map_one embLL (map_zero _) (map_one _),
        Matrix.one_mul]
    have hc : embLL (M0.1.det ^ (-lam (Fin.last m))) = (M0.1.map embLL).det ^ (-lam (Fin.last m)) := by
      rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]
    rw [map_mul, map_C, eval_mul, eval_C, eval_map_rowAct, hmul, map_map_int, hc, Matrix.det_mul, mul_zpow,
      _root_.zpow_neg]
    field_simp

end PI.BlockRatReal.UnitaryGroupMassFormula
