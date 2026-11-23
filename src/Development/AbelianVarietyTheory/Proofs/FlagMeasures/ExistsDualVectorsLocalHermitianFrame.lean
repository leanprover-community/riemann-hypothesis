module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocDual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

private lemma h_add_right (H : HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm y x, ← H.h_herm y' x]

private lemma h_smul_right (H : HermSp M V) (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

private lemma h_neg_left (H : HermSp M V) (x y : V) : H.h (-x) y = - H.h x y := by
  have := H.h_smul_left (-1) x y
  simpa using this

private lemma h_sub_left (H : HermSp M V) (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [sub_eq_add_neg, H.h_add_left, h_neg_left, ← sub_eq_add_neg]

private lemma h_sub_right (H : HermSp M V) (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, h_sub_left, map_sub, ← H.h_herm y x, ← H.h_herm y' x]

private lemma h_sum_left (H : HermSp M V) {ι : Type} (s : Finset ι) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun a b => H.h_add_left a b y)
  exact map_sum φ v s

private lemma h_sum_right (H : HermSp M V) {ι : Type} (s : Finset ι) (v : ι → V) (x : V) :
    H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by
  let φ : V →+ E := AddMonoidHom.mk' (fun y => H.h x y) (fun a b => h_add_right H x a b)
  exact map_sum φ v s

end GlobalTheory.LocDual


open GlobalTheory.LocDual in
theorem GlobalTheory.LocDual.frameD_exists : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (f : Fin (r + 1) → V) (T : F), T ≠ 0 → (∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f a) (f b) = 0) → H.h (f (Fin.last r)) (f (Fin.last r)) = -(algebraMap F E T) → (∃ y : Fin r → V, ∀ i j : Fin r, H.h (f i.castSucc) (y j) = if i = j then 1 else 0) → ∃ Fr : FrameD H r, Fr.f = f ∧ Fr.T = T := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r f T hT hiso hzz hy
  obtain ⟨y, hy⟩ := hy
  haveI := hM.char0
  set z := f (Fin.last r) with hz
  set e : Fin r → V := fun i => f i.castSucc with he
  have hez : ∀ k, H.h (e k) z = 0 := fun k => hiso _ _ (Or.inl (Fin.castSucc_ne_last k))
  have hze : ∀ k, H.h z (e k) = 0 := fun k => hiso _ _ (Or.inr (Fin.castSucc_ne_last k))
  have hee : ∀ k l, H.h (e k) (e l) = 0 := fun k l => hiso _ _ (Or.inl (Fin.castSucc_ne_last k))
  let y' : Fin r → V := fun j => y j + (H.h (y j) z * algebraMap F E T⁻¹) • z
  have hy'z : ∀ j, H.h (y' j) z = 0 := by
    intro j
    simp only [y', H.h_add_left, H.h_smul_left, hzz]
    rw [show H.h (y j) z * algebraMap F E T⁻¹ * -algebraMap F E T
        = - (H.h (y j) z * algebraMap F E (T⁻¹ * T)) by rw [map_mul]; ring]
    rw [inv_mul_cancel₀ hT, map_one, mul_one, add_neg_cancel]
  have hey' : ∀ k j, H.h (e k) (y' j) = if k = j then 1 else 0 := by
    intro k j
    simp only [y', h_add_right, h_smul_right, hez, mul_zero, add_zero, e]
    exact hy k j
  let half : E := algebraMap F E (1 / 2)
  have hhalf : M.L.cj half = half := M.L.cj.commutes _
  have hhalf2 : half + half = 1 := by
    simp only [half, ← map_add (f := _), add_halves, map_one]
  let b : Fin r → Fin r → E := fun j k => half * H.h (y' j) (y' k)
  let es : Fin r → V := fun j => y' j - ∑ k, b j k • e k
  have hesL : ∀ i v, H.h (es i) v = H.h (y' i) v - ∑ k, b i k * H.h (e k) v := by
    intro i v
    simp only [es, h_sub_left, h_sum_left, H.h_smul_left]
  have hesR : ∀ v j, H.h v (es j) = H.h v (y' j) - ∑ k, M.L.cj (b j k) * H.h v (e k) := by
    intro v j
    simp only [es, h_sub_right, h_sum_right, h_smul_right]
  have hy'e : ∀ i k, H.h (y' i) (e k) = if k = i then 1 else 0 := by
    intro i k
    rw [H.h_herm, hey' k i]
    split_ifs <;> simp
  refine ⟨⟨f, es, T, hiso, hzz, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro i j
    rw [hesR]
    simp only [hesL, hey', hy'e, hee, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [b, map_mul, hhalf]
    rw [← H.h_herm (y' j) (y' i)]
    linear_combination (-H.h (y' i) (y' j)) * hhalf2
  · intro i j
    show H.h (e i) (es j) = _
    rw [hesR]
    simp only [hey', hee, mul_zero, Finset.sum_const_zero, sub_zero]
  · intro i
    show H.h (es i) z = 0
    rw [hesL]
    simp only [hy'z, hez, mul_zero, Finset.sum_const_zero, sub_zero]
