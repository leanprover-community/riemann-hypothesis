module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem smul_mem_spanForms_of_mul_mem {K : Type} [Field K] {M M' : Set K} {H : Set Ω[K⁄ℤ]} {a : ℕ} (g : K)
    (hg : ∀ c ∈ M, g * c ∈ M') {η : abelian₂ K} (hη : η ∈ spanForms M H a) :
    g • η ∈ spanForms M' H a := by
  induction hη using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨g * c, hg c hc, v, hv, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_logAt_add_iff {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (G D : CartierDiv X) (a : ℕ)
    (y : X) (g : X.functionFieldˣ) (η : abelian₂ X.functionField) (hD : D.IsEqn y g) :
    η ∈ logAt Z (G + D) a y ↔ (g : X.functionField) • η ∈ logAt Z G a y := by
  obtain ⟨e, hG⟩ := G.exists_isEqn y
  have hGD := hG.add hD
  constructor
  · intro h
    refine smul_mem_spanForms_of_mul_mem _ (fun c hc => ?_) h
    change G.RegularAt y _
    change (G + D).RegularAt y c at hc
    rw [hG.regularAt_iff]
    rw [hGD.regularAt_iff, Units.val_mul] at hc
    convert hc using 1
    ring
  · intro h
    have h' := smul_mem_spanForms_of_mul_mem (M' := {c | (G + D).RegularAt y c}) (g : X.functionField)⁻¹
      (fun c hc => ?_) h
    · rwa [inv_smul_smul₀ g.ne_zero] at h'
    · change (G + D).RegularAt y _
      change G.RegularAt y c at hc
      rw [hGD.regularAt_iff, Units.val_mul]
      rw [hG.regularAt_iff] at hc
      convert hc using 1
      field_simp

theorem logtwist : ∀ (X : Scheme.{0}) [IsIntegral X] (Z : Set X) (G D : CartierDiv X) (a : ℕ) (y : X)
    (g : X.functionFieldˣ) (η : abelian₂ X.functionField), D.IsEqn y g →
    (η ∈ logAt Z (G + D) a y ↔ (g : X.functionField) • η ∈ logAt Z G a y) :=
  fun X _ Z G D a y g η hD => mem_logAt_add_iff Z G D a y g η hD

end GlobalTheory.LogDR
