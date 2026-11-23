module

public import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsStdStatement
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Irreducible
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.RationalFiniteIdeleFactorization
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

noncomputable section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.VacLoc.ModelLine

theorem cyclic_and_line : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (S : Sys W (SB (κ → R)))
    (Γ : AddSubgroup W) (al : W → ℂ) (φ φ' : SB (κ → R)), GoodChar ψ O u → IsModel ψ d μ S →
    (φ ≠ 0 → Cyclic S φ) ∧
      (SelfDual S Γ → IsSemi S al Γ → Law S al Γ φ → Law S al Γ φ' → φ ≠ 0 → ∃ a : ℂ, φ' = a • φ) := by
  intro R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ S Γ al φ φ' hg hm
  obtain ⟨Γ₀, al₀, φ₀, h1, h2, h3, h4, _⟩ := GlobalTheory.T.schrodinger_model_selfDual_lattice ψ O u d μ S hg hm
  have hcyc : φ ≠ 0 → Cyclic S φ := fun h =>
    (GlobalTheory.CompanionTheory.FinHeis.Irred.irreducible S al₀ Γ₀ φ₀ h1 h2 h3 h4).2 φ h
  refine ⟨hcyc, fun hΓ hal hφ hφ' h0 => ?_⟩
  exact GlobalTheory.CompanionTheory.FinHeis.LawLine.law_line S al Γ φ φ' hΓ hal hφ (hcyc h0) hφ'

end GlobalTheory.CompanionTheory.VacLoc.ModelLine
