module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Module.ZLattice.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem lattice_hom_finite_image_of_trivial_on_multiples :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (G : Type) [Group G] (e : (Fin g → ℂ) → G) (N : ℕ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z w, e (z + w) = e z * e w) → 0 < N →
    (∀ l ∈ Λ, e ((N : ℂ) • l) = 1) → (e '' (Λ : Set (Fin g → ℂ))).Finite := by
  intro g Λ G _ e N hd hspan hadd hN hker
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let f : (Module.Free.ChooseBasisIndex ℤ Λ → Fin N) → G :=
    fun a => e (∑ i, ((a i : ℕ) : ℤ) • ((b i : Λ) : Fin g → ℂ))
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨l, hl, rfl⟩
  set x : Λ := ⟨l, hl⟩ with hxdef
  let c : Module.Free.ChooseBasisIndex ℤ Λ → ℤ := fun i => b.repr x i
  let q : Λ := ∑ i, (c i / N) • b i
  have hc : ∀ i, 0 ≤ c i % (N : ℤ) := fun i => Int.emod_nonneg _ (by exact_mod_cast hN.ne')
  refine ⟨fun i => ⟨(c i % (N : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 := Int.emod_lt_of_pos (c i) (by exact_mod_cast hN : (0 : ℤ) < N)
    omega
  · have hl' : l = (N : ℂ) • ((q : Λ) : Fin g → ℂ) +
        ∑ i, (((c i % (N : ℤ)).toNat : ℕ) : ℤ) • ((b i : Λ) : Fin g → ℂ) := by
      have hx : l = ((∑ i, c i • b i : Λ) : Fin g → ℂ) := by
        rw [b.sum_repr x]
      rw [hx]
      simp only [q, Submodule.coe_sum, Submodule.coe_smul, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.toNat_of_nonneg (hc i)]
      have hN' : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_cast
      rw [hN', Int.cast_smul_eq_zsmul, smul_smul, ← add_smul]
      have h2 := Int.mul_ediv_add_emod (c i) (N : ℤ)
      congr 1
      linarith
    refine Eq.trans ?_ (congrArg e hl').symm
    rw [hadd, hker _ q.2, one_mul]

end GlobalTheory
