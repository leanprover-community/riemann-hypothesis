module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem ev_eq_sum {A : Type} [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] {Γ : Type} [CommGroup Γ] [Fintype Γ]
    (χ : Γ →* Ωˣ) (z : MonoidAlgebra A Γ) :
    ev A χ z = ∑ g, algebraMap A Ω (z.coeff g) * ((χ g : Ωˣ) : Ω) := by
  classical
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul, Finset.sum_add_distrib]
  | single g n =>
    rw [ev_single, Finset.sum_eq_single g]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, hb, hb.symm]
    · simp

theorem UpperTheory.V.B5.sum_char_mul_quotientMatrix_eq_charEval_mul :
    ∀ {A : Type} [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ∀ (χ : Ch Ω c ε) (z : MonoidAlgebra A Γ) (j : Qc c), ∑ i : Qc c, ((χ.1 (rep i) : Ωˣ) : Ω) * algebraMap A Ω (mat c ε z i j) = ev A χ.1 z * ((χ.1 (rep j) : Ωˣ) : Ω) := by
  intro A _ Ω _ _ Γ _ _ c ε h2 h1 χ z j
  have := Fintype.ofFinite Γ
  have hc : ((χ.1 c : Ωˣ) : Ω) = (ε : Ω) := χ.2
  rw [ev_eq_sum, Finset.sum_mul, ← Equiv.sum_comp (Equiv.mulRight (rep j)⁻¹), sum_rep h2 h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hj : ((χ.1 (rep j) : Ωˣ) : Ω) ≠ 0 := Units.ne_zero _
  simp only [mat, Matrix.of_apply, Equiv.coe_mulRight, map_add (f := _), map_mul, map_intCast, mul_assoc, map_inv,
    Units.val_mul, Units.val_inv_eq_inv_val, hc, inv_mul_cancel₀ hj]
  ring
