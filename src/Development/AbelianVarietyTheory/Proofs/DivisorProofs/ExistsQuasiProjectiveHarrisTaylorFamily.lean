module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepresentingFamilyOfAuxiliaryRepresentatioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorAuxiliarySymplecticLevelRepresentablStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKernelBoundedRepresentableOfCoprimeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem exists_repFam_qproj : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∃ F : RepFam b N, IsQProjOver F.s := by
  intro p _ D R _ _ b N hN hNp
  obtain ⟨e, hep, he⟩ := D.perfP
  have hp := (Fact.out : p.Prime)
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      rw [Nat.coprime_zero_left] at hep
      exact absurd hep hp.one_lt.ne'
    · exact h
  obtain ⟨M, hMge, hMp⟩ := Nat.exists_infinite_primes (p + e + 3)
  have hM3 : 3 ≤ M := by omega
  have hModd : Odd M := hMp.odd_of_ne_two (by omega)
  have hMcp : M.Coprime p := (Nat.coprime_primes hMp hp).2 (by omega)
  have hMe : M.Coprime e := (Nat.Prime.coprime_iff_not_dvd hMp).2 fun h => by
    have := Nat.le_of_dvd he0 h
    omega
  have hg : 1 ≤ Module.finrank ℤ D.La / 2 := by
    have := D.two_le_finrank_La
    omega
  exact GlobalTheory.T.exists_representingFamily_of_auxiliaryRepresentation p D R b N M e hN hNp hM3 hModd hMcp hep hMe he
    (GlobalTheory.T.harrisTaylor_auxiliary_symplectic_level_representable p D R b N M e hN hNp hM3 hModd hMcp hep hMe he
      (GlobalTheory.T.siegelKernelBoundedRepresentable_of_coprime _ M e hg hM3 hModd he0 hMe))

end GlobalTheory.UPel.HT
