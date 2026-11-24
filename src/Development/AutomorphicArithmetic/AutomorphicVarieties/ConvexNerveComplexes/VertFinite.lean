module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.vert_finite :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ}, LocFin q → ∀ K : Set E, IsCompact K → K ⊆ poly q → {h | h ∈ K ∧ IsVert q h}.Finite := by
  intro E Y _ _ q hq K hK hKp
  choose S hSf hSU using fun x (hx : x ∈ K) => hq x (hKp hx)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx => {h' : E | ∀ y ∉ S x hx, 1 < q y h'})
    (fun x hx => hSU x hx)
  have hfin : (⋃ x ∈ (t : Set K), S x.1 x.2).Finite :=
    t.finite_toSet.biUnion fun x _ => hSf x.1 x.2
  refine Set.Finite.of_finite_image (f := fun v : E => {y : Y | q y v = 1}) ?_ ?_
  · refine hfin.finite_subsets.subset ?_
    rintro _ ⟨v, ⟨hvK, hvV⟩, rfl⟩
    have hv := ht hvK
    simp only [Set.mem_iUnion] at hv
    obtain ⟨x, hxt, hvx⟩ := hv
    show {y : Y | q y v = 1} ⊆ _
    intro y hy
    simp only [Set.mem_iUnion, Finset.mem_coe]
    refine ⟨x, hxt, ?_⟩
    by_contra hyS
    have h1 := (hvx : ∀ y ∉ S x.1 x.2, 1 < q y v) y hyS
    simp only [Set.mem_setOf_eq] at hy
    linarith
  · rintro v ⟨_, hvV⟩ w ⟨_, hwV⟩ hvw
    have key : w - v = 0 := by
      refine hvV.2 (w - v) fun y hy => ?_
      have hy' : y ∈ {y : Y | q y w = 1} := by
        have e : {y : Y | q y v = 1} = {y : Y | q y w = 1} := hvw
        rw [← e]
        exact hy
      simp only [Set.mem_setOf_eq] at hy'
      simp [map_sub, hy, hy']
    exact (sub_eq_zero.1 key).symm
