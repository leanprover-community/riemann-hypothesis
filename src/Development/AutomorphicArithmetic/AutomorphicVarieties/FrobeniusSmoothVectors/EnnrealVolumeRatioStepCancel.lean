module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.ClChain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.ClComp
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ennreal_volume_ratio_step_cancel (a h : ℕ) (x : WithBot ℕ∞) (H : ((a + h : ℕ) : WithBot ℕ∞) ≤ x + h) :
    (a : WithBot ℕ∞) ≤ x := by
  induction x using WithBot.recBotCoe with
  | bot =>
    exfalso
    have h1 : ((a + h : ℕ) : WithBot ℕ∞) ≤ ⊥ := by simpa using H
    exact absurd h1 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      have h2 : ((a + h : ℕ) : WithBot ℕ∞) ≤ ((n + h : ℕ) : WithBot ℕ∞) := by
        simpa using H
      have h3 : a + h ≤ n + h := by exact_mod_cast h2
      have h4 : a ≤ n := by omega
      exact_mod_cast h4

theorem UpperTheory.V.Fr.c1ch :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (h D : ℕ) (f : Fin h → R), (nilradical R).IsPrime → (∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : IsAdicComplete (maximalIdeal O) O) (_ : Algebra O R), IsCO O R) → (∀ i, f i ∈ maximalIdeal R) → ((D + 1 + h : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R → Chained (Ideal.span (Set.range f)) D := by
  intro R _ _ _ _ h D f hnil hO hf hdim
  obtain ⟨O, _, _, _, _, _, hCO⟩ := hO
  haveI : IrreducibleSpace (PrimeSpectrum R) :=
    (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical).2 hnil
  have hCL : UpperTheory.V.CA.IsCL O R := UpperTheory.V.CA.IsCL.of_isCO O R
  set a : Ideal R := Ideal.span (Set.range f) with ha_def
  have hara : ReciprocityTheory.CA.AraLE a h := by
    classical
    refine ⟨Finset.univ.image f, ?_, ?_⟩
    · exact (Finset.card_image_le).trans (by rw [Finset.card_univ, Fintype.card_fin])
    · rw [ha_def, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hne : a ≠ ⊤ := by
    intro htop
    have hle : a ≤ maximalIdeal R := by
      rw [ha_def, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hf i
    exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (htop ▸ hle))
  refine ⟨fun P hP => ?_, fun P hP Q hQ => ?_⟩
  · have hc := UpperTheory.V.AlgebraTools.Conn.clComp hCL a P h hara hP
    exact ennreal_volume_ratio_step_cancel (D + 1) h _ (hdim.trans hc)
  · have hdim' : ((D + h + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R := by
      have he : D + h + 1 = D + 1 + h := by omega
      rw [he]
      exact hdim
    exact UpperTheory.V.AlgebraTools.Conn.clChain hCL a h D hne hara hdim' P hP Q hQ
