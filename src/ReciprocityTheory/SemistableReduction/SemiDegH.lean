module

public import ReciprocityTheory.SemistableReduction.SemiDegR
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem isIntegralElt_add {K : Type} [Field K] [NumberField K] {x y : K} (hx : IsIntegralElt x)
    (hy : IsIntegralElt y) : IsIntegralElt (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

theorem isIntegralElt_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) {x : K}
    (hx : IsIntegralElt x) : IsIntegralElt (S.c x) := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨RingOfIntegers.mapRingHom S.c z, rfl⟩

theorem norm_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (z : K) :
    Algebra.norm ℚ (S.c z) = Algebra.norm ℚ z := by
  have hs : Function.Surjective S.c := fun x => ⟨S.c x, S.c_invol x⟩
  let e : K ≃+* K := RingEquiv.ofBijective S.c ⟨S.c.injective, hs⟩
  let e' : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := e) (fun q => by simp [e])
  exact Algebra.norm_eq_of_algEquiv e' z

def projLt (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x i := if (i : ℕ) < e then x i else 0
  map_add' x y := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]

theorem spanIdx_pair {K : Type} [Field K] [NumberField K] {r : ℕ} (j p : Fin r)
    (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K)) (hj : ∀ x ∈ Gj, IsAt j x)
    (hp : ∀ x ∈ Gp, IsAt p x) (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hy : y ∈ Gp) :
    spanIdx (Gj ⊔ Gp) ![x0, y] = spanIdx Gj ![x0] * spanIdx Gp ![y] := by
  unfold spanIdx
  have hspan : Submodule.span (𝓞 K) (Set.range ![x0, y]) =
      Submodule.span (𝓞 K) {x0} ⊔ Submodule.span (𝓞 K) {y} := by
    rw [Matrix.range_cons_cons_empty, Submodule.span_insert]
  have h1 : Set.range ![x0] = {x0} := Matrix.range_cons_empty _ _
  have h2 : Set.range ![y] = {y} := Matrix.range_cons_empty _ _
  rw [hspan, h1, h2, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup]
  set X0 := (Submodule.span (𝓞 K) {x0}).toAddSubgroup
  set Y := (Submodule.span (𝓞 K) {y}).toAddSubgroup
  have hX0 : X0 ≤ Gj.toAddSubgroup := by
    show Submodule.span (𝓞 K) {x0} ≤ Gj
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx0
  have hY : Y ≤ Gp.toAddSubgroup := by
    show Submodule.span (𝓞 K) {y} ≤ Gp
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hy
  have key := AddSubgroup.relIndex_mul_relIndex _ _ _ (sup_le_sup_left hY X0)
    (sup_le_sup_right hX0 Gp.toAddSubgroup)
  rw [← key, mul_comm (X0.relIndex _)]
  congr 1
  · refine relIndex_sup_proj (projGe K r p).toAddMonoidHom X0 Y Gp.toAddSubgroup hY ?_ ?_
    · intro a ha
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 ha
      show projGe K r p (t • x0) = 0
      rw [map_smul]
      have : projGe K r p x0 = 0 := by
        funext i
        show (if (p : ℕ) ≤ i then x0 i else 0) = 0
        split_ifs with h
        · exact hj x0 hx0 i (fun hi => by rw [hi] at h; omega)
        · rfl
      rw [this, smul_zero]
    · intro x hx
      show projGe K r p x = x
      funext i
      show (if (p : ℕ) ≤ i then x i else 0) = x i
      split_ifs with h
      · rfl
      · exact (hp x hx i (fun hi => by rw [hi] at h; omega)).symm
  · rw [sup_comm X0, sup_comm Gj.toAddSubgroup]
    refine relIndex_sup_proj (projLt K r p).toAddMonoidHom Gp.toAddSubgroup X0 Gj.toAddSubgroup
      hX0 ?_ ?_
    · intro x hx
      show projLt K r p x = 0
      funext i
      show (if (i : ℕ) < p then x i else 0) = 0
      split_ifs with h
      · exact hp x hx i (fun hi => by rw [hi] at h; omega)
      · rfl
    · intro x hx
      show projLt K r p x = x
      funext i
      show (if (i : ℕ) < p then x i else 0) = x i
      split_ifs with h
      · rfl
      · exact (hj x hx i (fun hi => by rw [hi] at h; omega)).symm

end ReciprocityTheory.MultiplicativeHeights.SemiPt
