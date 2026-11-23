module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.Cz

namespace TF

theorem monic_lprod (L : List ℂ) : (L.map fun c => Polynomial.X - Polynomial.C c).prod.Monic := by
  induction L with
  | nil => simp
  | cons c L ih =>
    rw [List.map_cons, List.prod_cons]
    exact (Polynomial.monic_X_sub_C c).mul ih

theorem fin_adjoin {A : Type*} [Ring A] [Algebra ℂ A] {ι : Type*} [Finite ι] (x : ι → A)
    (hc : ∀ i j, Commute (x i) (x j)) (hL : ∀ i, ∃ L : List ℂ, (L.map fun c => x i - algebraMap ℂ A c).prod = 0) :
    FiniteDimensional ℂ (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range x))) := by
  classical
  have hcomm : (Set.range x).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hc i j
  letI : IsMulCommutative (Algebra.adjoin ℂ (Set.range x)) := Algebra.isMulCommutative_adjoin ℂ hcomm
  letI : CommRing (Algebra.adjoin ℂ (Set.range x)) := by
    open scoped IsMulCommutative in
      exact inferInstance
  have hint : ∀ i, IsIntegral ℂ (x i) := by
    intro i
    obtain ⟨L, hL⟩ := hL i
    refine ⟨(L.map fun c => Polynomial.X - Polynomial.C c).prod, monic_lprod L, ?_⟩
    rw [← Polynomial.aeval_def, map_list_prod, List.map_map]
    have hf : (⇑(Polynomial.aeval (x i)) ∘ fun c => Polynomial.X - Polynomial.C c) =
        fun c => x i - algebraMap ℂ A c := by
      funext c
      simp [Polynomial.aeval_X, Polynomial.aeval_C]
    rw [hf]
    exact hL
  let y : ι → Algebra.adjoin ℂ (Set.range x) := fun i => ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have hyint : ∀ z ∈ Set.range y, IsIntegral ℂ z := by
    rintro _ ⟨i, rfl⟩
    exact (isIntegral_algHom_iff (Algebra.adjoin ℂ (Set.range x)).val Subtype.val_injective).1 (hint i)
  have hfin := Algebra.finite_adjoin_of_finite_of_isIntegral (R := ℂ) (Set.finite_range y) hyint
  have hset : Set.range y = Subtype.val ⁻¹' (Set.range x) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  have htop : Algebra.adjoin ℂ (Set.range y) = ⊤ := by
    rw [hset]
    exact Algebra.adjoin_adjoin_coe_preimage
  rw [htop] at hfin
  have hS : Module.Finite ℂ (Algebra.adjoin ℂ (Set.range x)) :=
    Module.Finite.equiv Subalgebra.topEquiv.toLinearEquiv
  exact Subalgebra.finiteDimensional_toSubmodule.2 hS

end TF

end PositivityTheory.Rg.Cz
