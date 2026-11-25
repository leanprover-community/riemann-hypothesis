module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Statement
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Matrix.StdBasis
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

open scoped Pointwise in
private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_mul {H : Type} [Group H]
    {K : Type} [Field K] (r : H →* M4 K) {x y : M4 K}
    (hx : x ∈ Submodule.span K (Set.range r)) (hy : y ∈ Submodule.span K (Set.range r)) :
    x * y ∈ Submodule.span K (Set.range r) := by
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨g', rfl⟩, rfl⟩
  exact ⟨g * g', map_mul r g g'⟩

private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_top {K : Type} [Field K]
    {n : Type} [Fintype n] [DecidableEq n]
    (S : Submodule K (Matrix n n K)) (h : ∀ i j, Matrix.single i j (1 : K) ∈ S) : S = ⊤ :=
  eq_top_iff.2 <| (Matrix.stdBasis K n n).span_eq ▸ Submodule.span_le.2 <| by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    rw [SetLike.mem_coe, Matrix.stdBasis_eq_single]
    exact h i j

private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_iff {H : Type} [Group H] {K : Type} [Field K] (r : H →* M4 K)
    (he : ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r)) (i j : Fin 4) :
    Ge r i j ↔ Matrix.single i j (1 : K) ∈ Submodule.span K (Set.range r) := by
  constructor
  · rintro ⟨g, hg⟩
    have h1 := geAlg_mul r (geAlg_mul r (he i) (Submodule.subset_span ⟨g, rfl⟩)) (he j)
    have h2 := Submodule.smul_mem _ (r g i j)⁻¹ h1
    rw [Matrix.single_mul_mul_single, Matrix.smul_single] at h2
    simpa [hg] using h2
  · intro h
    by_contra hn
    have key : Submodule.span K (Set.range r) ≤ LinearMap.ker (Matrix.entryLinearMap K K i j) :=
      Submodule.span_le.2 <| by
        rintro _ ⟨g, rfl⟩
        show r g i j = 0
        by_contra h'
        exact hn ⟨g, h'⟩
    simpa using key h

theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg :
    ∀ {H : Type} [Group H] (K : Type) [Field K] (r : H →* M4 K) (ν : H → K), (∀ g, IsGSp (ν g) (r g)) → (∀ i, Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r)) → (∀ i j, Ge r i j ↔ Matrix.single i j (1 : K) ∈ Submodule.span K (Set.range r)) ∧ (∀ i, Ge r i i) ∧ (∀ i j k, Ge r i j → Ge r j k → Ge r i k) ∧ (∀ i j, Ge r i j → Ge r j.rev i.rev) ∧ (Irr r ↔ ∀ i j, Ge r i j) ∧ (Ge r 0 2 → Ge r 2 0 → (∀ g, IsBlock (r g)) → Submodule.span K (Set.range fun g => (r g).submatrix ixA ixA) = ⊤) := by
  intro H _ K _ r ν hν he
  have hiff := geAlg_iff r he
  refine ⟨hiff, fun i => (hiff i i).2 (he i), ?_, ?_, ?_, ?_⟩
  · intro i j k hij hjk
    have := geAlg_mul r ((hiff i j).1 hij) ((hiff j k).1 hjk)
    rw [Matrix.single_mul_single_same, mul_one] at this
    exact (hiff i k).2 this
  · rintro i j ⟨g, hg⟩
    refine ⟨g⁻¹, fun h0 => hg ?_⟩
    have h1 : adj (r g) = ν g • r g⁻¹ := by
      have h2 : adj (r g) * r g * r g⁻¹ = ν g • (1 : M4 K) * r g⁻¹ := by rw [hν g]
      rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one, smul_mul_assoc, one_mul] at h2
    have h3 := congrFun (congrFun h1 j.rev) i.rev
    rw [adj_apply, Fin.rev_rev, Fin.rev_rev, Matrix.smul_apply, h0, smul_zero] at h3
    have h4 : ∀ a b : Fin 4, sgn a * sgn b = 1 ∨ sgn a * sgn b = -1 := by decide
    rcases h4 j.rev i.rev with h | h <;> rw [h] at h3 <;> simpa using h3
  · constructor
    · intro h i j
      rw [hiff, h]
      trivial
    · intro h
      exact geAlg_top _ fun i j => (hiff i j).1 (h i j)
  · intro h02 h20 _
    let f : M4 K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
      { toFun := fun x => x.submatrix ixA ixA
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hm : ∀ x ∈ Submodule.span K (Set.range r),
        f x ∈ Submodule.span K (Set.range fun g => (r g).submatrix ixA ixA) := by
      intro x hx
      have := Submodule.mem_map_of_mem (f := f) hx
      rwa [Submodule.map_span, ← Set.range_comp] at this
    have hs : ∀ a b : Fin 2, f (Matrix.single (ixA a) (ixA b) (1 : K)) = Matrix.single a b 1 := by
      intro a b
      ext c d
      have hinj : ∀ a b : Fin 2, ixA a = ixA b ↔ a = b := by decide
      show Matrix.single (ixA a) (ixA b) (1 : K) (ixA c) (ixA d) = _
      simp only [Matrix.single_apply, hinj]
    refine geAlg_top _ fun a b => ?_
    rw [← hs]
    apply hm
    fin_cases a <;> fin_cases b
    · exact he 0
    · exact (hiff 0 2).1 h02
    · exact (hiff 2 0).1 h20
    · exact he 2
