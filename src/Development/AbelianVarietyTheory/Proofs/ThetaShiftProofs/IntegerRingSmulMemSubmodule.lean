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

namespace GlobalTheory.SubmoduleScalarClosure

open NumberField

theorem int_smul_mem_submodule {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (𝓞 E) (Fin r → E)) {x : Fin r → E} (hx : x ∈ L) (m : ℤ) :
    (m : E) • x ∈ L := by
  have h := L.smul_mem (m : 𝓞 E) hx
  rwa [← algebraMap_smul E (m : 𝓞 E) x, map_intCast] at h

theorem integer_ring_smul_mem_submodule {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (𝓞 E) (Fin r → E)) {x : Fin r → E} (hx : x ∈ L) (a : 𝓞 E) :
    (a : E) • x ∈ L := by
  have h := L.smul_mem a hx
  rwa [← algebraMap_smul E a x] at h

theorem main {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E) :
    ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ (↑n : E) • v ∈ ReciprocityTheory.ChartRestriction.G.FD.Data.Λ X := by

  let S : Submodule E (Fin r → E) :=
    { carrier := {w | ∃ n : ℤ, n ≠ 0 ∧ (n : E) • w ∈ X.Λ}
      add_mem' := by
        rintro a b ⟨n, hn, ha⟩ ⟨k, hk, hb⟩
        refine ⟨n * k, mul_ne_zero hn hk, ?_⟩
        have h := X.Λ.add_mem (int_smul_mem_submodule X.Λ ha k) (int_smul_mem_submodule X.Λ hb n)
        convert h using 1
        rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (k : E) (n : E)]
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro c w ⟨n, hn, hw⟩

        have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ c)
        obtain ⟨d, hd, hint⟩ := hc.exists_integral_multiple
        refine ⟨d * n, mul_ne_zero hd hn, ?_⟩
        have h := integer_ring_smul_mem_submodule X.Λ hw ⟨d • c, hint⟩
        convert h using 1
        show _ = (d • c) • ((n : E) • w)
        rw [smul_smul, smul_smul, zsmul_eq_mul]
        congr 1
        push_cast
        ring }
  have hle : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ S :=
    Submodule.span_le.mpr fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩
  rw [X.Λ_span] at hle
  obtain ⟨n, hn, h⟩ := hle (Submodule.mem_top : v ∈ ⊤)
  exact ⟨n, hn, h⟩

end GlobalTheory.SubmoduleScalarClosure
