module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_index_of_isPreconnected : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)), IsOpen B → IsPreconnected B → B.Nonempty → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ∃ i : Fin FU.n, ∀ b₀ ∈ B, ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b := by
  intro E _ _ _ H D l Xo σ g ty FU m B y hB hpre hne hs hy
  let S : Fin FU.n → Set (Fin m → ℂ) := fun i => {b₀ | ∃ (B' : Set (Fin m → ℂ))
    (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧
      IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b}
  have hopen : ∀ i, IsOpen (S i) := by
    intro i
    refine isOpen_iff_forall_mem_open.2 ?_
    rintro b₀ ⟨B', P, hB', hb₀, hsub, hP, hu⟩
    exact ⟨B', fun b hb => ⟨B', P, hB', hb, hsub, hP, hu⟩, hB', hb₀⟩
  have hcover : ∀ b ∈ B, ∃ i, b ∈ S i := by
    intro b hb
    obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := FU.lift m B y hB hs hy b hb
    exact ⟨i, B', P, hB', hb', hsub, hP, hu⟩
  have hdisj : ∀ i j b, b ∈ S i → b ∈ S j → i = j := by
    rintro i j b ⟨B₁, P₁, -, hb₁, -, hP₁, hu₁⟩ ⟨B₂, P₂, -, hb₂, -, hP₂, hu₂⟩
    exact FU.disj i j (P₁ b) (P₂ b) (hP₁.1 b hb₁) (hP₂.1 b hb₂) ((hu₁ b hb₁).trans (hu₂ b hb₂).symm)
  obtain ⟨b₁, hb₁⟩ := hne
  obtain ⟨i, hi⟩ := hcover b₁ hb₁
  have hsub : B ⊆ S i := by
    refine IsPreconnected.subset_left_of_subset_union (v := ⋃ j ∈ {j | j ≠ i}, S j) (hopen i)
      (isOpen_biUnion fun j _ => hopen j) ?_ ?_ ⟨b₁, hb₁, hi⟩ hpre
    · refine Set.disjoint_left.2 fun b hbi hbT => ?_
      obtain ⟨j, hj, hbj⟩ := Set.mem_iUnion₂.1 hbT
      exact hj (hdisj i j b hbi hbj).symm
    · intro b hb
      obtain ⟨j, hj⟩ := hcover b hb
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, hj⟩)
  exact ⟨i, fun b₀ hb₀ => hsub hb₀⟩

end GlobalTheory.CompanionTheory.Ar.Flat
