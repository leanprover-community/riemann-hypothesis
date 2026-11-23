module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralImagQuadraticHalfInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[reducible] noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be :
    Formalism.BasicNotions.D7 → ℂ :=
    fun (D : Formalism.BasicNotions.D7) ↦ Complex.I * (↑√(↑D.host.d : ℝ) : ℂ)

noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.OKc :
    Formalism.BasicNotions.D7 → ℂ → Prop :=
    fun (D : Formalism.BasicNotions.D7) (z : ℂ) ↦
      ∃ (x : ℤ) (y : ℤ), Even (x - y) ∧ z = ((↑x : ℂ) + (↑y : ℂ) * UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be D) / (2 : ℂ)

theorem UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.okc_of :
    ∀ (D : Formalism.BasicNotions.D7) (u : NumberField.RingOfIntegers ↥D.host.K),
      UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.OKc D ((D.host.φ₀ : D.host.E → ℂ) (↑(↑u : ↥D.host.K) : D.host.E)) := by
  intro D u
  have hd : Nat.Prime D.host.d := D.host.hyp.2.1
  have hint : IsIntegral ℤ ((u : D.host.K) : D.host.E) :=
    (NumberField.RingOfIntegers.isIntegral_coe u).map (D.host.K.val.toRingHom.toIntAlgHom)
  obtain ⟨x, y, hxy, hz⟩ := UpperTheory.integral_imag_quadratic_half_int D.host.E D.host.d D.host.sqd hd.squarefree
    D.host.sqd_sq _ (u : D.host.K).2 hint
  have hs : D.host.φ₀ D.host.sqd = UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be D := D.host.φ₀_mem
  refine ⟨x, y, hxy, ?_⟩
  rw [hz, map_div₀, map_add (f := _), map_mul, map_intCast, map_intCast, hs, map_ofNat]
