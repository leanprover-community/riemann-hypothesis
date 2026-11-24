module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
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

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem quantum_minor_border_expansion_first {n m : ℕ} (E : Fin n → Fin n → A) (e : Fin n) (f b : Fin m → Fin n) (hE : GlRel E)
    (hf : ∀ j, f j ≠ e) (hb : ∀ j, b j ≠ e) (u : ℂ) :
    qminor E (bE e f) (bE e b) u = Tm E u e e * qminor E f b (u - 1) -
      ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E (f w) e * qminor E (f ∘ skip1 w) (b ∘ skip1 x) (u - 2) * E e (b x)) := by
  rw [Qx6.expFCE E expansion_first_column]
  refine Qx6.add_eq_sub_of ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Qx6.qm_dropE E expansion_last_line quantumMinorRowSkew_holds hE, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Qx6.Tm_ne E _ (hf w), Qx6.Tm_ne E _ (hb x).symm, ← zsmul_eq_mul, mul_smul_comm, smul_smul, ← pow_add,
    ← neg_smul, show u - 1 - 1 = u - 2 by ring, mul_assoc]
  congr 1
  rw [show (w : ℕ) + 1 + (x : ℕ) = (w : ℕ) + (x : ℕ) + 1 by ring, pow_succ]
  ring

end Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas
