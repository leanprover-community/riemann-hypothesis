module

public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsIbp
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section

namespace ReciprocityTheory.AnForm.A

theorem parts_thm : PartsStatement := mulVec_one_sub_idempotent_of_split_sum_identity

theorem hessCRestrict_thm : HessCRestrictStatement := by
  intro n φ U j hU hφ y hy
  obtain ⟨Lc, hLc⟩ : ∃ Lc : (Fin n → ℂ) →L[ℝ] (Fin (n + 1) → ℂ),
      ∀ y, Lc y = Fin.insertNth (α := fun _ => ℂ) j 0 y := by
    refine ⟨ContinuousLinearMap.pi fun i => Fin.insertNth
      (α := fun _ => (Fin n → ℂ) →L[ℝ] ℂ) j 0
      (fun k => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k) i, ?_⟩
    intro y
    funext m
    by_cases hm : m = j
    · rw [hm]; simp
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hm
      simp
  have hs : ∀ (c : ℂ) (i : Fin n), Lc (c • Pi.single i 1) = c • Pi.single (j.succAbove i) 1 := by
    intro c i
    rw [hLc]
    funext m
    by_cases hm : m = j
    · rw [hm]; simp [Pi.single_apply, (Fin.succAbove_ne j i).symm]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hm
      simp [Pi.single_apply]
  have hs1 : ∀ i : Fin n, Lc (Pi.single i 1) = Pi.single (j.succAbove i) 1 := by
    intro i; simpa using hs 1 i
  have hfun : (fun y' => φ (Fin.insertNth (α := fun _ => ℂ) j 0 y')) = φ ∘ Lc := by
    funext y'; simp only [Function.comp_apply, hLc]
  rw [hfun, ← hLc y]
  rw [← hLc y] at hy
  have hφa : ∀ x ∈ U, ContDiffAt ℝ 2 φ x := fun x hx => hφ.contDiffAt (hU.mem_nhds hx)
  have hev : fderiv ℝ (φ ∘ Lc) =ᶠ[nhds y] fun y' => (fderiv ℝ φ (Lc y')).comp Lc := by
    have hU' : ∀ᶠ y' in nhds y, Lc y' ∈ U :=
      Lc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hy)
    filter_upwards [hU'] with y' hy'
    rw [fderiv_comp y' ((hφa _ hy').differentiableAt
      (by first | exact one_le_two | exact two_ne_zero | norm_num)) Lc.differentiableAt,
      Lc.fderiv]
  have hd1 : DifferentiableAt ℝ (fderiv ℝ φ) (Lc y) :=
    ((hφa _ hy).fderiv_right (m := 1)
      (by first | exact le_rfl | exact one_add_one_eq_two.le | norm_num)).differentiableAt
      (by first | exact le_rfl | exact one_ne_zero)
  have hc : DifferentiableAt ℝ (fun y' => fderiv ℝ φ (Lc y')) y :=
    hd1.comp y Lc.differentiableAt
  have hH : ∀ v w, fderiv ℝ (fderiv ℝ (φ ∘ Lc)) y v w =
      fderiv ℝ (fderiv ℝ φ) (Lc y) (Lc v) (Lc w) := by
    intro v w
    rw [hev.fderiv_eq, fderiv_clm_comp (c := fun y' => fderiv ℝ φ (Lc y')) (d := fun _ => Lc) hc
      (differentiableAt_const Lc), fderiv_comp' y hd1 Lc.differentiableAt, Lc.fderiv]
    simp
  refine Matrix.ext fun a b => ?_
  simp only [hessC, Matrix.submatrix_apply, hH, hs, hs1]

end ReciprocityTheory.AnForm.A
