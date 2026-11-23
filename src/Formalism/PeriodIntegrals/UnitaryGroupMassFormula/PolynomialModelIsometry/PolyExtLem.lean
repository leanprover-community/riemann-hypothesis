module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.IsPolyMon
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.Params
public import Mathlib.Algebra.MvPolynomial.Monad

@[expose] public section

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

lemma pe_evM_detPoly {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) : evM g (detPoly N) = g.det := by
  unfold evM detPoly
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

lemma pe_one_mem (N : ℕ) : (1 : Matrix (Fin N) (Fin N) ℂ) ∈ Kset (allPos N) := by
  refine ⟨one_mem _, by simp⟩

lemma pe_mul_mem {N : ℕ} {g h : Matrix (Fin N) (Fin N) ℂ} (hg : g ∈ Kset (allPos N)) (hh : h ∈ Kset (allPos N)) :
    g * h ∈ Kset (allPos N) := by
  refine ⟨mul_mem hg.1 hh.1, ?_⟩
  rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]

lemma pe_unitary_mem {N : ℕ} (u : Matrix (Fin N) (Fin N) ℂ) (hu : uᴴ * u = 1) : u ∈ Kset (allPos N) := by
  have hJ : Jm (allPos N) = 1 := by
    unfold Jm allPos
    simp
  refine ⟨?_, by rw [hJ]; simp⟩
  rw [Matrix.mem_unitaryGroup_iff']
  exact hu

lemma pe_right {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ Q' : MvPolynomial (Fin N × Fin N) ℂ, ∀ g, evM g Q' = evM (g * h) Q := by
  refine ⟨bind₁ (fun pq : Fin N × Fin N => ∑ r, X (pq.1, r) * C (h r pq.2)) Q, fun g => ?_⟩
  induction Q using MvPolynomial.induction_on with
  | C a => simp [evM]
  | add p q hp hq => simp only [map_add (f := _), evM] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, evM, bind₁_X_right] at *
    rw [hp]
    simp [Matrix.mul_apply]

lemma pe_left {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ Q' : MvPolynomial (Fin N × Fin N) ℂ, ∀ h, evM h Q' = evM (g * h) Q := by
  refine ⟨bind₁ (fun pq : Fin N × Fin N => ∑ r, C (g pq.1 r) * X (r, pq.2)) Q, fun h => ?_⟩
  induction Q using MvPolynomial.induction_on with
  | C a => simp [evM]
  | add p q hp hq => simp only [map_add (f := _), evM] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, evM, bind₁_X_right] at *
    rw [hp]
    simp [Matrix.mul_apply]

end PI.WMI
