module

public import Formalism.SatakeDualWeyl.Statement
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

@[expose] public section

namespace GlobalTheory.FinsetConjugateRepresentatives

theorem mem_map_conj {G : Type} [Group G] (K : Subgroup G) (g y : G) :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have : g⁻¹ * (MulAut.conj g).toMonoidHom z * g = z := by
      simp [mul_assoc]
    rw [this]
    exact hz
  · intro h
    refine ⟨g⁻¹ * y * g, h, ?_⟩
    simp [mul_assoc]

theorem exists_finset_reps : ∀ {G : Type} [inst : Group G] {K : Subgroup G},
    Formalism.UG.IsCommensurated K → ∀ (g : G), ∃ (R : Finset G),
      (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
      ∀ (x : G), (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ : G, γ ∈ R ∧ γ⁻¹ * x ∈ K := by
  intro G _ K hK g
  classical
  set H : Subgroup K := (K.map (MulAut.conj g).toMonoidHom).subgroupOf K with hH
  have hidx : H.index ≠ 0 := hK g
  haveI : Finite (K ⧸ H) := Nat.finite_of_card_ne_zero hidx
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have key : ∀ (q : K ⧸ H) (a : K) (b : G), b ∈ K →
      ((((q.out : K) : G) * g)⁻¹ * ((a : G) * g * b) ∈ K ↔ q = (a : K ⧸ H)) := by
    intro q a b hb
    have e : (((q.out : K) : G) * g)⁻¹ * ((a : G) * g * b)
        = (g⁻¹ * (((q.out)⁻¹ * a : K) : G) * g) * b := by
      simp [mul_assoc]
    rw [e, K.mul_mem_cancel_right hb, ← mem_map_conj, ← Subgroup.mem_subgroupOf, ← hH,
      ← QuotientGroup.eq, QuotientGroup.out_eq']
  refine ⟨Finset.univ.image (fun q : K ⧸ H => ((q.out : K) : G) * g), ?_, ?_⟩
  · intro γ hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hγ
    exact ⟨_, (q.out).2, 1, K.one_mem, by simp⟩
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    refine ⟨((((⟨k₁, hk₁⟩ : K) : K ⧸ H).out : K) : G) * g,
      ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, (key _ ⟨k₁, hk₁⟩ k₂ hk₂).mpr rfl⟩, ?_⟩
    rintro γ ⟨hγ, hx⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hγ
    rw [(key q ⟨k₁, hk₁⟩ k₂ hk₂).mp hx]

end GlobalTheory.FinsetConjugateRepresentatives
