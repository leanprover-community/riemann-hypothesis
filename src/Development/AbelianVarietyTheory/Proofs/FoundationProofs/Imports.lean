module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.IdealPowerMembership

open MvPolynomial

theorem main : ∀ (K L : Type) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] [inst_3 : FiniteDimensional K L], ∃ (f : MvPolynomial (Fin (Module.finrank K L)) K), MvPolynomial.IsHomogeneous f (Module.finrank K L) ∧ ∀ (x : L), (Algebra.norm K : L → K) x = (MvPolynomial.eval fun (i : Fin (Module.finrank K L)) ↦ ((Module.Basis.repr (Module.finBasis K L) : L → Fin (Module.finrank K L) →₀ K) x : Fin (Module.finrank K L) → K) i : MvPolynomial (Fin (Module.finrank K L)) K → K) f := by
  intro K L _ _ _ _
  classical
  let b := Module.finBasis K L
  let P : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) (MvPolynomial (Fin (Module.finrank K L)) K) :=
    fun j k => ∑ i, X i * C (Algebra.leftMulMatrix b (b i) j k)
  have hP : ∀ j k, (P j k).IsHomogeneous 1 := by
    intro j k
    apply IsHomogeneous.sum
    intro i _
    simpa using (isHomogeneous_X K i).mul (isHomogeneous_C (Fin (Module.finrank K L)) (Algebra.leftMulMatrix b (b i) j k))
  refine ⟨P.det, ?_, ?_⟩
  · rw [Matrix.det_apply]
    apply IsHomogeneous.sum
    intro σ _
    have h := IsHomogeneous.prod (Finset.univ : Finset (Fin (Module.finrank K L))) (fun i => P (σ i) i) (fun _ => 1) (fun i _ => hP (σ i) i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]; exact h
    · rw [hs, Units.neg_smul, one_smul]; exact h.neg
  · intro x
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext j k
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    have e1 : Algebra.leftMulMatrix b x = ∑ i, b.repr x i • Algebra.leftMulMatrix b (b i) := by
      conv_lhs => rw [hx]

      rw [map_sum]
      simp only [map_smul]
    rw [e1, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply]

    simp only [P, map_sum, eval_mul, eval_X, eval_C, Matrix.smul_apply, smul_eq_mul]
    rfl
