module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
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
import Mathlib.Tactic.ENatToNat
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

namespace GlobalTheory.SmulMemOfSpan

open NumberField

theorem exists_smul_mem_of_span {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin r → E)) (v : Fin r → E)
    (hv : v ∈ Submodule.span E (L : Set (Fin r → E))) :
    ∃ c : RingOfIntegers E, c ≠ 0 ∧ (c : E) • v ∈ L := by
  have hL : ∀ (n : RingOfIntegers E) (w : Fin r → E), w ∈ L → (n : E) • w ∈ L := by
    intro n w hw
    rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
    exact L.smul_mem n hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [RingOfIntegers.coe_eq_algebraMap, map_one, one_smul]
    exact hx
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    have e : ((c * d : RingOfIntegers E) : E) • (x + y) =
        (d : E) • ((c : E) • x) + (c : E) • ((d : E) • y) := by
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
      ring
    rw [e]
    exact L.add_mem (hL d _ hcx) (hL c _ hdy)
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨n, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) a
    have hy0 : algebraMap (RingOfIntegers E) E y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    refine ⟨y * c, mul_ne_zero (nonZeroDivisors.ne_zero hy) hc, ?_⟩
    have e : ((y * c : RingOfIntegers E) : E) •
        ((algebraMap (RingOfIntegers E) E n / algebraMap (RingOfIntegers E) E y) • x) =
        (n : E) • ((c : E) • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
      field_simp
    rw [e]
    exact hL n _ hcx

theorem exists_smul_mem_lattice : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E), ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ (↑c : E) • v ∈ ReciprocityTheory.ChartRestriction.G.FD.Data.Λ X := by
  intro E _ _ _ r X v
  refine exists_smul_mem_of_span X.Λ v ?_
  rw [X.Λ_span]
  exact Submodule.mem_top

end GlobalTheory.SmulMemOfSpan
