module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDetEqDoubleSumAdjugateEntryStatement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem modeDerivation_det_eq_zero : GlobalTheory.PsCo.Cw2a.T_dM_detb := by
  intro n ε x
  let Mx : Matrix (Fin n) (Fin n) (Poly n) := Matrix.of fun a b => X (Sum.inr (a, b))
  let W : Matrix (Fin n) (Fin n) (Poly n) := (barM ε (Matrix.single x.1.2 x.1.1 1)).map C
  have hD : ∀ i j, dM ε x (Mx i j) = (Mx * W - W * Mx) i j := by
    intro i j
    simp only [dM, dZ, Mx, W, Matrix.of_apply, mkDerivation_X, Sum.elim_inr, Matrix.sub_apply,
      Matrix.mul_apply, Matrix.map_apply, Finset.sum_sub_distrib]
  have key := GlobalTheory.T.derivation_det_eq_double_sum_adjugate_entry (dM ε x) Mx
  have hdet : detbP n = Mx.det := rfl
  rw [hdet, key]
  simp_rw [hD]
  have htr : ∑ i, ∑ j, Mx.adjugate j i * (Mx * W - W * Mx) i j
      = Matrix.trace (Mx.adjugate * (Mx * W - W * Mx)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
  rw [htr, Matrix.mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc Mx.adjugate Mx W, Matrix.adjugate_mul,
    ← Matrix.mul_assoc Mx.adjugate W Mx, Matrix.trace_mul_comm (Mx.adjugate * W) Mx,
    ← Matrix.mul_assoc Mx Mx.adjugate W, Matrix.mul_adjugate, sub_self]

end GlobalTheory.PsCo.Cw2a
