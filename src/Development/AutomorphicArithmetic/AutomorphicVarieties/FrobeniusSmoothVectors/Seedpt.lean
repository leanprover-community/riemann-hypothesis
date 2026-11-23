module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerLiftTwoToThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocDim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MonMemPow
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

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.seedpt :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (p : Ideal S.B) (ξ : Ideal S.A), p.IsPrime → ξ.IsPrime → S.u.TI ξ → p ≤ S.π ξ → ∃ x : PrimeSpectrum S.A, x.asIdeal.IsMaximal ∧ x ∈ S.BB ∧ ∀ L : S.Loc x.asIdeal, ∃ P : Ideal L.R, P.IsPrime ∧ L.ρ.TI P ∧ L.π P = p ∧ ringKrullDim (L.R ⧸ P) = ringKrullDim (S.B ⧸ p) + 1 := by
  intro l _ O _ _ _ _ F C₀ n hF hn S p ξ hp hξ hTI hpξ
  obtain ⟨η, hηp, hhom, hπ, hTIη, htd⟩ := frobenius_corner_lift_two_to_three hF hn S p ξ hp hξ hTI hpξ
  have hTIη' := hTIη
  unfold NRep.TI NRep.OffTri at hTIη'
  obtain ⟨x, hxmax, hxBB, hηx⟩ := l41 hF hn S η hηp hhom hTIη'.1.1
  refine ⟨x, hxmax, hxBB, fun L => ?_⟩
  have htd' : S.td η = ((1 : ℕ) : _) := by
    rw [htd]
    rfl
  obtain ⟨P, hP, himP, hdim⟩ := (loc_dim hF hn S x.asIdeal L).2 η hηp hηx 1 htd'
  have hloc := (loc_rho hF hn S x.asIdeal L).2.2.1 P
  rw [himP] at hloc
  refine ⟨P, hP, ?_, ?_, ?_⟩
  · unfold NRep.TI NRep.OffTri
    exact ⟨⟨fun h => hTIη'.1.1 (hloc.1.mp h), fun h => hTIη'.1.2 (hloc.2.1.mp h)⟩,
      fun h3 h => hTIη'.2 h3 (hloc.2.2.mp h)⟩
  · show S.π (L.im P) = p
    rw [himP, hπ]
  · rw [hdim, hπ]
    norm_num
