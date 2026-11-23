module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabEqStabilizer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open GlobalTheory.LKCount

namespace GlobalTheory.LKCount

variable {Γ G : Type} [Group Γ] [Group G]

noncomputable def doubleCosetToOrbit (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) :
    DoubleCoset.Quotient ((H.map ι : Subgroup G) : Set G) (K : Set G) →
      MulAction.orbitRel.Quotient H (LeftCosets ι K) :=
  Quotient.lift (fun x => (Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K x))) (by
    intro a b hab
    obtain ⟨_, ⟨h, hh, rfl⟩, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hab
    refine (Quotient.sound ?_).symm
    refine ⟨⟨h, hh⟩, ?_⟩
    show LeftCosets.mk ι K (ι h * a) = LeftCosets.mk ι K (ι h * a * k)
    rw [LeftCosets.mk_eq_mk]
    convert hk using 1
    group)

theorem doubleCosetToOrbit_mk (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) (x : G) :
    doubleCosetToOrbit ι H K (DoubleCoset.mk _ _ x) =
      Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K x) := rfl

theorem doubleCosetToOrbit_bijective (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) :
    Function.Bijective (doubleCosetToOrbit ι H K) := by
  constructor
  · intro p q hpq
    rw [← DoubleCoset.out_eq' p, ← DoubleCoset.out_eq' q] at hpq ⊢
    rw [doubleCosetToOrbit_mk, doubleCosetToOrbit_mk] at hpq
    obtain ⟨h, hh⟩ := Quotient.exact hpq
    have hh' : LeftCosets.mk ι K (ι (h : Γ) * q.out) = LeftCosets.mk ι K p.out := hh
    rw [LeftCosets.mk_eq_mk] at hh'
    refine ((@DoubleCoset.eq _ _ _ _ _ _).2 ⟨ι h, Subgroup.mem_map_of_mem ι h.2, _, hh', ?_⟩).symm
    group
  · intro o
    induction o using Quotient.inductionOn with
    | h y =>
      refine ⟨DoubleCoset.mk _ _ (LeftCosets.rep ι K y), ?_⟩
      rw [doubleCosetToOrbit_mk, LeftCosets.mk_rep]

theorem finsum_doubleCoset_eq_finsum_orbit {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (H : Subgroup Γ)
    (K : Subgroup G) (g : LeftCosets ι K → ℂ) (hg : ∀ h ∈ H, ∀ y : LeftCosets ι K, g (h • y) = g y) :
    ∑ᶠ q : DoubleCoset.Quotient ((H.map ι : Subgroup G) : Set G) (K : Set G), g (LeftCosets.mk ι K (Quotient.out q)) =
      ∑ᶠ o : MulAction.orbitRel.Quotient H (LeftCosets ι K), g (Quotient.out o) := by
  let e := Equiv.ofBijective _ (doubleCosetToOrbit_bijective ι H K)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  have hq : e q = Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K q.out) := by
    show doubleCosetToOrbit ι H K q = _
    conv_lhs => rw [← DoubleCoset.out_eq' q]
    rfl
  rw [hq]
  obtain ⟨h, hh⟩ := Quotient.exact (Quotient.out_eq
    (Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K q.out)))
  rw [← hh]
  exact (hg h h.2 _).symm

end GlobalTheory.LKCount
