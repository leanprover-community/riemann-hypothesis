module

public import Mathlib.LinearAlgebra.Dimension.Basic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.algebraMap_range_span_eq_top_of_finite_generators :
    ∀ {k G M : Type} [Field k] [AddCommGroup M] [Module k M] (Y : Submodule k (G → k)) (C : ℕ) (a : G → M), Module.rank k Y ≤ C → (∀ f : M →ₗ[k] k, (fun g => f (a g)) ∈ Y) → ∃ T : Finset M, T.card ≤ C ∧ ∀ g, a g ∈ Submodule.span k (T : Set M) := by
  intro k G M _ _ _ Y C a hY ha
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent k (Set.range a)
  have hli' : LinearIndepOn k id b := hli
  let B := Module.Basis.extend hli'
  have hmem : ∀ x : b, (x : M) ∈ hli'.extend (Set.subset_univ b) :=
    fun x => hli'.subset_extend (Set.subset_univ b) x.2
  have hB : ∀ x : b, B ⟨x, hmem x⟩ = x := fun x => by
    simp only [B, Module.Basis.coe_extend]
  have hco : ∀ x y : b, B.coord ⟨x, hmem x⟩ (y : M) = if y = x then 1 else 0 := by
    intro x y
    rw [← hB y, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : y = x
    · subst h
      simp
    · have h' : (⟨(y : M), hmem y⟩ : hli'.extend (Set.subset_univ b)) ≠ ⟨x, hmem x⟩ := by
        intro e
        apply h
        apply Subtype.ext
        exact Subtype.mk.inj e
      simp [h, h']
  choose gx hgx using fun x : b => hbs x.2
  let φ : b → Y := fun x => ⟨fun g => B.coord ⟨x, hmem x⟩ (a g), ha (B.coord ⟨x, hmem x⟩)⟩
  have hφ : LinearIndependent k φ := by
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have h1 := congrArg (fun y : Y => (y : G → k) (gx i)) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ZeroMemClass.coe_zero, Pi.zero_apply, φ, hgx] at h1
    simpa [hco, hi] using h1
  have hcard : Cardinal.mk b ≤ C := hφ.cardinal_le_rank.trans hY
  have hfin : b.Finite := Cardinal.lt_aleph0_iff_set_finite.mp (hcard.trans_lt (Cardinal.natCast_lt_aleph0 (n := C)))
  haveI := hfin.fintype
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.card_toFinset]
    rw [Cardinal.mk_fintype] at hcard
    exact_mod_cast hcard
  · intro g
    rw [Set.Finite.coe_toFinset, hspan]
    exact Submodule.subset_span ⟨g, rfl⟩
