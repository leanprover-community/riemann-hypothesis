module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Weier
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

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.oneVar :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Field K] (ι : O →+* K), Function.Injective ι → ∀ (g : PowerSeries O) (Z : Set K), Z.Infinite → (∀ z ∈ Z, ∃ y : PowerSeries O →+* K, (∀ a, y (PowerSeries.C a) = ι a) ∧ y PowerSeries.X = z ∧ y g = 0) → g = 0 := by
  intro O K _ _ _ _ _ ι hι g Z hZ h
  by_contra hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, P, U, -, hP, -, hU, hfac⟩ := UpperTheory.V.abelian₂.weier O ϖ hϖ g hg
  have hmon : (P.map ι).Monic := hP.monic.map ι
  have hϖ0 : ι ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hι (by rw [h0, map_zero]))
  refine hmon.ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ (hZ.mono ?_))
  intro z hz
  obtain ⟨y, hyC, hyX, hy0⟩ := h z hz
  have hyP : y (P : PowerSeries O) = (P.map ι).eval z := by
    have e : y.comp Polynomial.coeToPowerSeries.ringHom = Polynomial.eval₂RingHom ι z := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [hyC]
      · simp [hyX]
    have := RingHom.congr_fun e P
    simpa [Polynomial.eval_map] using this
  rw [hfac, map_mul, map_mul, map_pow, hyC, hyP] at hy0
  have hyU : y U ≠ 0 := (hU.map y).ne_zero
  show (P.map ι).IsRoot z
  rcases mul_eq_zero.1 hy0 with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero m hϖ0)
    · exact h2
  · exact absurd h1 hyU
