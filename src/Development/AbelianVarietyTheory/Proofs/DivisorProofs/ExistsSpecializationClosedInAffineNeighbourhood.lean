module

public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ClosedPt

lemma exists_max_specializes {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) (x : Y)
    (hx : x ∈ V) : ∃ N : PrimeSpectrum Γ(Y, V), N.asIdeal.IsMaximal ∧
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≤ N.asIdeal ∧ x ⤳ hV.fromSpec N := by
  obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal (hV.primeIdealOf ⟨x, hx⟩).asIdeal
    (hV.primeIdealOf ⟨x, hx⟩).isPrime.ne_top
  refine ⟨⟨N, hN.isPrime⟩, hN, hle, ?_⟩
  have h1 : (hV.primeIdealOf ⟨x, hx⟩) ⤳ (⟨N, hN.isPrime⟩ : PrimeSpectrum Γ(Y, V)) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have h2 := Specializes.map (f := hV.fromSpec) h1 hV.fromSpec.continuous
  rwa [hV.fromSpec_primeIdealOf] at h2

lemma fromSpec_mem {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V)
    (N : PrimeSpectrum Γ(Y, V)) : hV.fromSpec N ∈ V := by
  have : hV.fromSpec N ∈ Set.range hV.fromSpec := ⟨N, rfl⟩
  rwa [hV.range_fromSpec] at this

theorem exists_closed_point : ∀ (Y : Scheme.{0}) (x : Y), ∃ V : Y.Opens, IsAffineOpen V ∧ ∃ y ∈ V, x ⤳ y ∧ ∀ V₂ : Y.Opens, V₂ ≤ V → IsAffineOpen V₂ → y ∈ V₂ → (∀ y₁ ∈ V₂, y ⤳ y₁ → y₁ = y) ∧ ∃ M : Ideal Γ(Y, V₂), M.IsMaximal ∧ ∀ a : Γ(Y, V₂), a ∈ M ↔ y ∉ Y.basicOpen a := by
  intro Y x
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := ⊤) trivial
  obtain ⟨N, hN, -, hxN⟩ := exists_max_specializes hV x hx
  refine ⟨V, hV, hV.fromSpec N, fromSpec_mem hV N, hxN, ?_⟩
  intro V₂ hle hV₂ hy
  have hcl : ∀ y₁ ∈ V₂, hV.fromSpec N ⤳ y₁ → y₁ = hV.fromSpec N := by
    intro y₁ hy₁ hs
    have e := hV.fromSpec_primeIdealOf ⟨y₁, hle hy₁⟩
    have hs' : hV.fromSpec N ⤳ hV.fromSpec (hV.primeIdealOf ⟨y₁, hle hy₁⟩) := by
      rw [e]; exact hs
    have h3 : N ⤳ hV.primeIdealOf ⟨y₁, hle hy₁⟩ :=
      (hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp hs'
    have h4 : N ≤ hV.primeIdealOf ⟨y₁, hle hy₁⟩ := (PrimeSpectrum.le_iff_specializes _ _).mpr h3
    have h5 : N = hV.primeIdealOf ⟨y₁, hle hy₁⟩ :=
      PrimeSpectrum.ext (hN.eq_of_le (hV.primeIdealOf ⟨y₁, hle hy₁⟩).isPrime.ne_top h4)
    rw [h5]; exact e.symm
  refine ⟨hcl, (hV₂.primeIdealOf ⟨_, hy⟩).asIdeal, ?_, ?_⟩
  · obtain ⟨N₂, hN₂, -, hs⟩ := exists_max_specializes hV₂ _ hy
    have e := hcl _ (fromSpec_mem hV₂ N₂) hs
    have e2 := hV₂.fromSpec_primeIdealOf ⟨_, hy⟩
    have : N₂ = hV₂.primeIdealOf ⟨_, hy⟩ :=
      hV₂.fromSpec.isOpenEmbedding.injective (e.trans e2.symm)
    rw [← this]; exact hN₂
  · intro a
    have e2 := hV₂.fromSpec_primeIdealOf ⟨_, hy⟩
    have h := hV₂.fromSpec_preimage_basicOpen a
    have h' : hV₂.fromSpec (hV₂.primeIdealOf ⟨_, hy⟩) ∈ Y.basicOpen a ↔
        hV₂.primeIdealOf ⟨_, hy⟩ ∈ PrimeSpectrum.basicOpen a := by
      rw [← h]; rfl
    rw [e2, PrimeSpectrum.mem_basicOpen] at h'
    exact (not_iff_comm.mp h'.symm).symm

end GlobalTheory.ClosedPt
