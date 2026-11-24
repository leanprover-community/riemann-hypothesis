module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ZH

theorem mul_inv_apply_mem_of_span_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {b B c : Matrix J J Ω}
    (h : Submodule.span R (Set.range b) ≤ Submodule.span R (Set.range B)) (hc : B * c = 1) (i j : J) :
    (b * c) i j ∈ R := by
  have h1 : ∀ i, ∃ n : J → R, ∑ k, n k • B k = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  choose n hn using h1
  have e : b = (Matrix.of fun i k => (n i k : Ω)) * B := by
    ext i k
    rw [← hn i, Matrix.mul_apply, Finset.sum_apply]
    rfl
  rw [e, Matrix.mul_assoc, hc, Matrix.mul_one]
  exact (n i j).2

theorem exists_mul_eq_one_of_span_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {b B c : Matrix J J Ω}
    (h : Submodule.span R (Set.range B) ≤ Submodule.span R (Set.range b)) (hc : c * B = 1) :
    ∃ d : Matrix J J Ω, b * d = 1 := by
  have h1 : ∀ i, ∃ n : J → R, ∑ k, n k • b k = B i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  choose n hn using h1
  have e : B = (Matrix.of fun i k => (n i k : Ω)) * b := by
    ext i k
    rw [← hn i, Matrix.mul_apply, Finset.sum_apply]
    rfl
  refine ⟨c * Matrix.of fun i k => (n i k : Ω), mul_eq_one_comm.1 ?_⟩
  rw [Matrix.mul_assoc, ← e, hc]

theorem RatModel.exists_matrix_map_valF {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {J : Type} {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) (n : Matrix J J Ω)
    (h : ∀ z ∈ U, ∀ i j, n i j ∈ M.O z) : ∃ m : Matrix J J Γ(M.Z, U), m.map (M.res U hU) = n := by
  choose m hm using fun i j =>
    (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => h z hz i j)
  refine ⟨Matrix.of m, ?_⟩
  ext i j
  exact (M.res_apply U hU _).trans (hm i j)

theorem exists_matrix_mul_eq_one_of_span_eq : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) [Fintype J] [DecidableEq J] (W W' : M.Z.Opens) (b B : Matrix J J Ω) (c : Matrix J J Γ(M.Z, W')), (∀ z ∈ W ⊓ W', Submodule.span (M.O z) (Set.range b) = Submodule.span (M.O z) (Set.range B)) → c.map (valF M.pt W') * B = 1 → ∃ m m' : Matrix J J Γ(M.Z, W ⊓ W'), m * m' = 1 ∧ (((W ⊓ W' : M.Z.Opens) : Set M.Z).Nonempty → m.map (valF M.pt (W ⊓ W')) = b * c.map (valF M.pt W')) := by
  intro o Ω _ _ _ M J _ _ W W' b B c h hc
  by_cases hne : ((W ⊓ W' : M.Z.Opens) : Set M.Z).Nonempty
  swap
  · exact ⟨1, 1, Matrix.mul_one _, fun h' => absurd h' hne⟩
  obtain ⟨z₀, hz₀⟩ := id hne
  have hc' : B * c.map (valF M.pt W') = 1 := mul_eq_one_comm.1 hc
  obtain ⟨d, hd⟩ := exists_mul_eq_one_of_span_le (M.O z₀) (h z₀ hz₀).ge hc
  obtain ⟨m, hm⟩ := M.exists_matrix_map_valF hne (b * c.map (valF M.pt W')) fun z hz =>
    mul_inv_apply_mem_of_span_le (M.O z) (h z hz).le hc'
  obtain ⟨m', hm'⟩ := M.exists_matrix_map_valF hne (B * d) fun z hz =>
    mul_inv_apply_mem_of_span_le (M.O z) (h z hz).ge hd
  refine ⟨m, m', ?_, fun _ => ?_⟩
  · apply Matrix.map_injective (M.res_injective _ hne)
    dsimp only
    rw [Matrix.map_mul, hm, hm', Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_assoc,
      ← Matrix.mul_assoc _ B, hc, Matrix.one_mul, hd]
  · rw [← hm]
    ext i j
    exact (M.res_apply _ hne _).symm

end GlobalTheory.ZH
