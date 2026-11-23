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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem UpperTheory.nonempty_primitive_root_of_strictly_henselian :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O], SH O → IsUnit (q : O) → Nonempty (Prim q O) := by
  intro q _ O _ hO hq
  obtain ⟨hH, hsep⟩ := hO
  have key : ∀ (p : Polynomial O) (x : O), IsLocalRing.residue O (p.eval x) =
      (p.map (IsLocalRing.residue O)).eval (IsLocalRing.residue O x) := by
    intro p x
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have hqk : ((q : ℕ) : IsLocalRing.ResidueField O) ≠ 0 := by
    have := (IsLocalRing.residue_ne_zero_iff_isUnit (q : O)).2 hq
    simpa using this
  haveI : NeZero ((q : ℕ) : IsLocalRing.ResidueField O) := ⟨hqk⟩
  have hdeg : (Polynomial.cyclotomic q (IsLocalRing.ResidueField O)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root _ hdeg
    (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O))
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective r
  have h1 : (Polynomial.cyclotomic q O).eval a₀ ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, key, Polynomial.map_cyclotomic]
    exact hr
  have h2 : IsUnit ((Polynomial.derivative (Polynomial.cyclotomic q O)).eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, key, ← Polynomial.derivative_map,
      Polynomial.map_cyclotomic]
    have h0 := (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O)).aeval_derivative_ne_zero
      (x := IsLocalRing.residue O a₀) (by simpa [Polynomial.coe_aeval_eq_eval] using hr)
    simpa [Polynomial.coe_aeval_eq_eval] using h0
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (Polynomial.cyclotomic q O)
    (Polynomial.cyclotomic.monic q O) a₀ h1 h2
  refine ⟨⟨a, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ha
