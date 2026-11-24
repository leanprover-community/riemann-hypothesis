module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
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
public import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem aux {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    (h1 : DirectSum.IsInternal 𝒜) (h2 : SetLike.GradedMonoid 𝒜) (η : Ideal A) (hη : η ∈ minimalPrimes A) :
    η = Ideal.span {x | x ∈ η ∧ ∃ j, x ∈ 𝒜 j} := by
  classical
  letI : DirectSum.Decomposition 𝒜 := h1.chooseDecomposition
  letI : GradedRing 𝒜 := { }
  have hp : η.IsPrime := hη.1.1
  have hc : (η.homogeneousCore 𝒜).toIdeal.IsPrime := Ideal.IsPrime.homogeneousCore hp
  have hle : (η.homogeneousCore 𝒜).toIdeal ≤ η := Ideal.toIdeal_homogeneousCore_le 𝒜 η
  have hge : η ≤ (η.homogeneousCore 𝒜).toIdeal := hη.2 ⟨hc, bot_le⟩ hle
  apply le_antisymm
  · refine hge.trans ?_
    show Ideal.homogeneousCore' 𝒜 η ≤ _
    unfold Ideal.homogeneousCore'
    apply Ideal.span_mono
    rintro _ ⟨⟨x, hx⟩, hx', rfl⟩
    exact ⟨hx', hx⟩
  · exact Ideal.span_le.2 fun x hx => hx.1

theorem UpperTheory.V.Fr.min_hom :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ η ∈ minimalPrimes S.A, S.IsHom η := by
  intro l _ O _ _ _ _ F C₀ n hF hn S η hη
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.Fr.gr_A hF hn S
  exact aux S.gr h1 h2 η hη
