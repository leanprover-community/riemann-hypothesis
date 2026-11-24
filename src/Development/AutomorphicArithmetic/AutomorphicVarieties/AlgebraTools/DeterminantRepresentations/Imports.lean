module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.DescendLam
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.glue :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [CompactSpace A] [TopologicalSpace G] {A' : Type} [CommRing A'] [TopologicalSpace A'] [T2Space A']
    (ι : A →+* A') (D' : GDet n A' G) (S : Set G), Continuous ι → Function.Injective ι → Dense S →
    (∀ i ≤ n, Continuous fun g : G => D'.lam i (MonoidAlgebra.single g 1)) →
    (∀ g ∈ S, ∀ i ≤ n, D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range) →
    ∃ D : GDet n A G, D.map ι = D' ∧ ∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ A' _ _ _ ι D' S hι hinj hS hcont hmem
  have hemb := hι.isClosedEmbedding hinj
  have hall : ∀ i ≤ n, ∀ g : G, D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range := by
    intro i hi g
    have hcl : IsClosed {g : G | D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range} := by
      have hr : IsClosed (Set.range ι) := hemb.isClosed_range
      rw [← RingHom.coe_range] at hr
      exact hr.preimage (hcont i hi)
    have hsub : S ⊆ {g : G | D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range} :=
      fun g hg => hmem g hg i hi
    have h1 := closure_minimal hsub hcl
    rw [hS.closure_eq] at h1
    exact h1 (Set.mem_univ g)
  obtain ⟨D, hD, -⟩ := UpperTheory.V.AlgebraTools.Det.descendLam ι D' hinj hall
  refine ⟨D, hD, fun i hi => ?_⟩
  rw [hemb.isEmbedding.continuous_iff]
  have heq : (⇑ι ∘ fun g : G => D.lam i (MonoidAlgebra.single g 1)) =
      fun g => D'.lam i (MonoidAlgebra.single g 1) := by
    funext g
    simp only [Function.comp]
    have hchi : ∀ y, (D.map ι).chi (MonoidAlgebra.mapRingHom G ι y) = (D.chi y).map ι := by
      intro y
      have e : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.mapRingHom G ι y) =
          MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom ι) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y) := by
        rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
          ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
          ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
      show (D.map ι).D A'[X] _ = _
      rw [e]
      have hφ : ∀ a, Polynomial.mapRingHom ι (algebraMap A A[X] a) = algebraMap A' A'[X] (ι a) := by
        intro a
        simp
      let : Algebra A A'[X] := ((algebraMap A' A'[X]).comp ι).toAlgebra
      exact D.nat A[X] A'[X] { Polynomial.mapRingHom ι with commutes' := hφ } _
    have hlam : ∀ i y, (D.map ι).lam i (MonoidAlgebra.mapRingHom G ι y) = ι (D.lam i y) := by
      intro i y
      simp only [GDet.lam, hchi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
    have hs : (D.map ι).lam i (MonoidAlgebra.single g 1) = ι (D.lam i (MonoidAlgebra.single g 1)) := by
      simpa using hlam i (MonoidAlgebra.single g 1)
    rw [← hs, hD]
  rw [heq]
  exact hcont i hi
