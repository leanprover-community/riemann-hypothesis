module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD in
private theorem UpperTheory.Reformulated.B.Ue6.herm_smul_right {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem UpperTheory.Reformulated.B.Ue6.even_im_hermitian_sub :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.DataX E r) (w0 : NumberField.RingOfIntegers E),
      ReciprocityTheory.ChartRestriction.G.FD.cc (↑w0 : E) = (1 : E) - (↑w0 : E) →
        ∀ u ∈ X.Λ,
          ∀ v ∈ X.Λ,
            ∃ (k : ℤ),
              (Algebra.trace ℚ E : E → ℚ)
                    (X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u (((↑w0 : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (↑w0 : E)) • v)) -
                  (Algebra.trace ℚ E : E → ℚ) (X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) =
                (2 : ℚ) * (↑k : ℚ) := by
  intro E _ _ _ r X w0 hw u hu v hv
  have hwv : (w0 : E) • v ∈ X.Λ := X.Λ.smul_mem w0 hv
  obtain ⟨a, ha⟩ := X.EF_int u hu _ hwv
  obtain ⟨b, hb⟩ := X.EF_int u hu v hv
  have hc : ReciprocityTheory.ChartRestriction.G.FD.cc ((w0 : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) = 1 - 2 * (w0 : E) := by
    have h1 : ReciprocityTheory.ChartRestriction.G.FD.cc ((w0 : E) - (1 - (w0 : E))) =
        ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E) - (1 - ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_sub, map_one]
    rw [hw, h1, hw]
    ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.EFf at ha hb
  rw [UpperTheory.Reformulated.B.Ue6.herm_smul_right, hw] at ha
  refine ⟨b - a, ?_⟩
  rw [UpperTheory.Reformulated.B.Ue6.herm_smul_right, hc, Int.cast_sub, ← ha, ← hb, ← map_sub, ← map_sub,
    two_mul ((Algebra.trace ℚ E) _), ← map_add]
  congr 1
  ring
