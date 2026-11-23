module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory.DI

section
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

theorem forms_gen_mem {B : Set K} {L : Set V} {q : ℕ} {b : K} (hb : b ∈ B) (v : Fin q → V)
    (hv : ∀ k, v k ∈ L) : b • ExteriorAlgebra.ιMulti K q v ∈ forms B L q :=
  AddSubgroup.subset_closure ⟨b, hb, v, hv, rfl⟩

theorem forms_le_comap_of_gen {B B' : Set K} {L L' : Set V} {q q' : ℕ}
    (φ : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (h : ∀ b ∈ B, ∀ v : Fin q → V, (∀ k, v k ∈ L) →
      φ (b • ExteriorAlgebra.ιMulti K q v) ∈ forms B' L' q') :
    forms B L q ≤ (forms B' L' q').comap φ := by
  show AddSubgroup.closure _ ≤ _
  rw [AddSubgroup.closure_le]
  rintro x ⟨b, hb, v, hv, rfl⟩
  exact h b hb v hv

theorem ι_mul_ιMulti_eq (u : V) {q : ℕ} (w : Fin q → V) :
    ExteriorAlgebra.ι K u * ExteriorAlgebra.ιMulti K q w =
      ExteriorAlgebra.ιMulti K (q + 1) (Fin.cons u w) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  rfl

theorem ιMulti_one_eq (u : Fin 1 → V) : ExteriorAlgebra.ιMulti K 1 u = ExteriorAlgebra.ι K (u 0) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

theorem forms_mul_smul_mono (A : Subring K) (L : Set V) :
    (1 : ExteriorAlgebra K V) ∈ forms (A : Set K) L 0 ∧
    (∀ q x y, x ∈ forms (A : Set K) L 1 → y ∈ forms (A : Set K) L q →
      x * y ∈ forms (A : Set K) L (q + 1)) ∧
    (∀ q (c : K) y, c ∈ A → y ∈ forms (A : Set K) L q → c • y ∈ forms (A : Set K) L q) ∧
    (∀ (B : Set K) q (c : K) y, y ∈ forms B L q → c • y ∈ forms ((fun b => c * b) '' B) L q) ∧
    ∀ (B B' : Set K) (L' : Set V) q, B ⊆ B' → L ⊆ L' → forms B L q ≤ forms B' L' q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := forms_gen_mem (B := (A : Set K)) (L := L) A.one_mem (Fin.elim0 : Fin 0 → V)
      (fun k => k.elim0)
    simpa using h
  · intro q x y hx hy

    have key : ∀ a ∈ (A : Set K), ∀ u : Fin 1 → V, (∀ k, u k ∈ L) →
        a • ExteriorAlgebra.ιMulti K 1 u * y ∈ forms (A : Set K) L (q + 1) := by
      intro a ha u hu
      have := forms_le_comap_of_gen (B := (A : Set K)) (L := L) (B' := (A : Set K)) (L' := L)
        (q := q) (q' := q + 1) (AddMonoidHom.mulLeft (a • ExteriorAlgebra.ιMulti K 1 u)) ?_ hy
      · exact this
      intro b hb w hw
      show a • ExteriorAlgebra.ιMulti K 1 u * (b • ExteriorAlgebra.ιMulti K q w) ∈ _
      rw [smul_mul_smul_comm, ιMulti_one_eq, ι_mul_ιMulti_eq]
      refine forms_gen_mem (A.mul_mem ha hb) _ ?_
      intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hu 0
      · simpa using hw k
    exact forms_le_comap_of_gen (B' := (A : Set K)) (L' := L) (q' := q + 1)
      (AddMonoidHom.mulRight y) (fun a ha u hu => key a ha u hu) hx
  · intro q c y hc hy
    refine forms_le_comap_of_gen (B' := (A : Set K)) (L' := L) (q' := q)
      (DistribSMul.toAddMonoidHom _ c) ?_ hy
    intro b hb v hv
    show c • b • ExteriorAlgebra.ιMulti K q v ∈ _
    rw [smul_smul]
    exact forms_gen_mem (A.mul_mem hc hb) v hv
  · intro B q c y hy
    refine forms_le_comap_of_gen (B' := (fun b => c * b) '' B) (L' := L) (q' := q)
      (DistribSMul.toAddMonoidHom _ c) ?_ hy
    intro b hb v hv
    show c • b • ExteriorAlgebra.ιMulti K q v ∈ _
    rw [smul_smul]
    exact forms_gen_mem (B := (fun b => c * b) '' B) (Set.mem_image_of_mem _ hb) v hv
  · intro B B' L' q hB hL
    refine (forms_le_comap_of_gen (B' := B') (L' := L') (q' := q) (AddMonoidHom.id _) ?_)
    intro b hb v hv
    exact forms_gen_mem (hB hb) v (fun k => hL (hv k))

end

end GlobalTheory.DI
