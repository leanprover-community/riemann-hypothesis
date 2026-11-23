module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

@[expose] public section

namespace GlobalTheory

theorem exists_pow_eq_one_of_posDef_form (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (b : LinearMap.BilinForm ℤ Y) (hs : ∀ y z, b y z = b z y) (hp : ∀ y, y ≠ 0 → 0 < b y y)
    (σ : Y ≃ₗ[ℤ] Y) (hσ : ∀ y z, b (σ y) (σ z) = b y z) : ∃ n : ℕ, 0 < n ∧ σ ^ n = 1 := by
  classical
  rw [← isOfFinOrder_iff_pow_eq_one]
  by_contra hfin
  have hinj := injective_pow_iff_not_isOfFinOrder.mpr hfin
  let e := Module.Free.chooseBasis ℤ Y
  have h0 : ∀ y, 0 ≤ b y y := fun y => by
    by_cases h : y = 0
    · simp [h]
    · exact (hp y h).le
  have hpow : ∀ (n : ℕ) y, b ((σ ^ n) y) ((σ ^ n) y) = b y y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih => intro y; rw [pow_succ', LinearEquiv.mul_apply, hσ, ih]
  have hnd : ∀ y, (∀ j, b y (e j) = 0) → y = 0 := by
    intro y hy
    by_contra h
    have : b y = 0 := e.ext fun j => by simpa using hy j
    have h2 := hp y h
    simp [this] at h2
  let f : ℕ → (_ → _ → ℤ) := fun n i j => b ((σ ^ n) (e i)) (e j)
  have hf : Function.Injective f := by
    intro m n h
    apply hinj
    apply LinearEquiv.toLinearMap_injective
    refine e.ext fun i => ?_
    rw [← sub_eq_zero]
    apply hnd
    intro j
    have := congrFun (congrFun h i) j
    simp only [f] at this
    simp [this]
  let C : _ → _ → ℤ := fun i j => b (e i) (e i) * b (e j) (e j)
  have hS : (Set.univ.pi fun i => Set.univ.pi fun j => Set.Icc (-C i j) (C i j)).Finite :=
    Set.Finite.pi fun i => Set.Finite.pi fun j => Set.finite_Icc _ _
  refine Set.infinite_of_injective_forall_mem hf (fun n => ?_) hS
  intro i _ j _
  have h1 := LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le b h0 ((σ ^ n) (e i)) (e j)
  rw [hpow, hs (e j), hs (e j)] at h1
  have h2 : f n i j ^ 2 ≤ C i j := by
    simp only [f, C]; nlinarith [h1]
  constructor <;> nlinarith [h2, sq_nonneg (f n i j - 1), sq_nonneg (f n i j + 1), Int.le_self_sq (f n i j), Int.le_self_sq (-f n i j)]

theorem latFinOrdSt : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LatFinOrdSt :=
  fun Y _ _ _ b hs hp σ hσ => exists_pow_eq_one_of_posDef_form Y b hs hp σ hσ

end GlobalTheory
