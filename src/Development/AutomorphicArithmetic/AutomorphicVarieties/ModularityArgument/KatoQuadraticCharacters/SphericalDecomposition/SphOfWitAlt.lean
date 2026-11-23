module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.PowEqOneOfKills
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.sphOfWit :
    TwWit → LocQ → SphOfWit := by
  intro hT hL l _ hl2 Ω _ _ _ ι e he W hWc hWi hWd hwit M φ hM hφ A w κ hA hlw hfl hk π hreg hatt
  obtain ⟨N, hN, hWk⟩ := hWd
  have hMN : 0 < N * M := Nat.mul_pos hN hM
  have hVc : Continuous (tw W φ) := GlobalTheory.Ord2.TwDet.tw_cont hWc (GlobalTheory.Ord2.SrcForm.cont_of_kills hM hφ)
  have hVi : IsIrr (tw W φ) :=
    ⟨hWi.1, fun _ _ _ => trivial, fun U hU hi =>
      hWi.2.2 U hU fun g v hv => (GlobalTheory.Ord2.SrcForm.isInv_tw W φ U).1 hi g v hv⟩
  have hVd : ∃ K : ℕ, 1 ≤ K ∧ KillsMu K (GlobalTheory.Ord2.dt (tw W φ)) := by
    refine ⟨N * M, hMN, ?_⟩
    rw [GlobalTheory.Ord2.TwDet.dt_tw, pow_two]
    exact GlobalTheory.Ord2.TwDet.killsMu_mul
      (GlobalTheory.Ord2.TwDet.killsMu_mul (GlobalTheory.Ord2.TwDet.killsMu_dvd hφ (dvd_mul_left M N)) (GlobalTheory.Ord2.TwDet.killsMu_dvd hφ (dvd_mul_left M N)))
      (GlobalTheory.Ord2.TwDet.killsMu_dvd hWk (dvd_mul_right N M))
  exact (hL l hl2 Ω ι e he (tw W φ) π hVc hVi hVd hreg hatt w A κ hlw hA ⟨hfl, hk⟩
    (Or.inl (hT l Ω ι 2 W M φ hM hφ hwit))).1
