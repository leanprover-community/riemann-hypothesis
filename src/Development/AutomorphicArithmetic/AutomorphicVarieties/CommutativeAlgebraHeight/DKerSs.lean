module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_ker_ss :
    ∀ {n : ℕ} {k E ι : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E] [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = n) (r : E →ₐ[k] Matrix ι ι k), IsSemisimpleRing r.range → ∀ x, x ∈ (Det.ofRep h r).ker ↔ r x = 0 := by
  intro n k E ι _ _ _ _ _ _ h r hss x
  rw [Det.mem_ker]
  constructor
  · intro hx
    obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
      (Ideal.span {(⟨r x, x, rfl⟩ : r.range)})
    have h1 : e ∈ Ideal.span {(⟨r x, x, rfl⟩ : r.range)} := hI ▸ Ideal.subset_span rfl
    have h2 : (⟨r x, x, rfl⟩ : r.range) ∈ Ideal.span {e} := hI ▸ Ideal.subset_span rfl
    obtain ⟨⟨a, u, rfl⟩, ha⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h2
    have ha' : r u * r x = (e : Matrix ι ι k) := congrArg Subtype.val ha
    have hb' : (b : Matrix ι ι k) * (e : Matrix ι ι k) = r x := congrArg Subtype.val hb
    have he' : (e : Matrix ι ι k) * e = e := congrArg Subtype.val he
    have h3 : (Det.repS r k (1 + (1 ⊗ₜ (-u)) * (1 ⊗ₜ x) * 1)).det = (Det.repS r k 1).det :=
      hx k 1 (1 ⊗ₜ (-u)) 1
    have h4 : Det.repS r k (1 + (1 ⊗ₜ (-u)) * (1 ⊗ₜ x) * 1) = 1 - (e : Matrix ι ι k) := by
      rw [map_add (f := _), map_mul, map_mul, map_one, Det.repS_tmul, Det.repS_tmul, ← ha']
      simp [sub_eq_add_neg]
    rw [h4, map_one, Matrix.det_one] at h3
    have h5 : IsUnit (1 - (e : Matrix ι ι k)) := by
      rw [Matrix.isUnit_iff_isUnit_det, h3]; exact isUnit_one
    have h6 : (e : Matrix ι ι k) = 0 := by
      apply h5.mul_left_cancel
      rw [sub_mul, one_mul, he', sub_self, mul_zero]
    rw [← hb', h6, mul_zero]
  · intro hx S _ _ y u v
    show (Det.repS r S (y + u * (1 ⊗ₜ x) * v)).det = (Det.repS r S y).det
    rw [map_add (f := _), map_mul, map_mul, Det.repS_tmul, hx]
    simp
