module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC


open Polynomial in
theorem prim_of_strictlyHenselian : ∀ (q : ℕ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → Nonempty (Prim q A) := by
  intro q A _ hSH hq
  obtain ⟨hH, hsep⟩ := hSH
  let k := IsLocalRing.ResidueField A
  have hqk : IsUnit ((q : ℕ) : k) := by
    have := hq.map (IsLocalRing.residue A)
    rwa [map_natCast] at this
  haveI : NeZero ((q : ℕ) : k) := ⟨hqk.ne_zero⟩
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hqk
    · exact h
  have hsepk : (cyclotomic q k).Separable := separable_cyclotomic q k
  obtain ⟨a₀, ha₀⟩ := IsSepClosed.exists_root (cyclotomic q k)
    (degree_cyclotomic_pos q k hq0).ne' hsepk
  have hmap : (cyclotomic q A).map (algebraMap A k) = cyclotomic q k := map_cyclotomic q _
  have h1 : aeval a₀ (cyclotomic q A) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hmap]; exact ha₀
  have h2 : aeval a₀ (derivative (cyclotomic q A)) ≠ 0 := by
    rw [aeval_def, eval₂_eq_eval_map, ← derivative_map, hmap]
    have := hsepk.aeval_derivative_ne_zero (x := a₀) (by simpa [aeval_def] using ha₀)
    simpa [aeval_def] using this
  have hT := (HenselianLocalRing.TFAE A).out 1 2
  obtain ⟨a, ha, -⟩ := hT.mp hH (cyclotomic q A) (cyclotomic.monic q A) a₀ h1 h2
  refine ⟨⟨a, hq, ?_⟩⟩
  have : (cyclotomic q ℤ).map (Int.castRingHom A) = cyclotomic q A := map_cyclotomic q _
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, this]
  exact ha

end GlobalTheory.EtC
