module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory UpperTheory.V UpperTheory.V.Af.BA

private theorem hom_sum_apply {Γ : Type} [Group Γ] {A B : Rep.{0} ℂ Γ} {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (f : ι → (A ⟶ B)) (x : A) :
    (∑ i ∈ s, c i • f i).hom x = ∑ i ∈ s, c i • (f i).hom x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Rep.add_hom, Rep.smul_hom]
    simp [ih]

private theorem d_coeff {Γ I : Type} [Group Γ] [MulAction Γ I] (K : Cx Γ I) (p : ℕ)
    (x : K.Tup (p + 1)) (y : K.Tup p) :
    ((K.d p).hom.toLinearMap (Finsupp.single x 1) : K.Tup p →₀ ℂ) y =
      ((KH.faceD (fun (i : Fin (p + 2)) => K.re i.succAbove) (Finsupp.single x 1) y : ℤ) : ℂ) := by
  classical
  show (Rep.Hom.hom (K.d p)) (Finsupp.single x 1) y = _
  simp only [Cx.d]
  rw [hom_sum_apply]
  simp [KH.faceD_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Cx.reC_single, Finsupp.single_apply]
  split_ifs <;> simp

theorem UpperTheory.exactCOf_of_exactBase :
    UpperTheory.V.Af.BA.ExactBase → UpperTheory.V.Af.BA.ExactCOf := by
  intro hB Γ I _ _ K hZ
  classical
  obtain ⟨hs, he0, -⟩ := hZ 0
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hs 1
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    obtain ⟨t, -⟩ := Finsupp.support_nonempty_iff.2 hv0
    intro c
    exact ⟨Finsupp.single t c, by rw [augC_single]⟩
  · have key := hB (K.Tup 1) (K.Tup 0) Unit _
      ((Finsupp.lsingle ()) ∘ₗ KH.aug (K.Tup 0)) _
      ((Finsupp.lsingle ()) ∘ₗ (Rep.Hom.hom (augC Γ (K.Tup 0))).toLinearMap) (d_coeff K 0) ?_ ?_
    · intro y
      have hy := key y
      simpa [Finsupp.single_eq_zero] using hy
    · intro y z
      simp [KH.aug_single]
      exact augC_single y 1
    · intro y
      have hy := he0 y
      simpa [Finsupp.single_eq_zero] using hy
  · intro p
    exact hB _ _ _ _ _ _ _ (d_coeff K (p + 1)) (d_coeff K p) ((hZ (p + 1)).2.2 p (Nat.lt_succ_self p))
