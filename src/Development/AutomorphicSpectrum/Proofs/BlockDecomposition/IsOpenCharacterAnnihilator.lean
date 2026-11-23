module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Matrix Topology

namespace GlobalTheory.CompanionTheory.AnnihOpen

theorem isOpen_annihilator_of_isCompact :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)),
      IsCompact (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  intro k _ _ _ _ ψ hψ n A hA
  let H : AddSubgroup (Fin n → k) :=
    { carrier := {ξ | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1}
      zero_mem' := by
        intro a _
        simp
      add_mem' := by
        intro x y hx hy a ha
        rw [add_dotProduct, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
      neg_mem' := by
        intro x hx a ha
        rw [neg_dotProduct, AddChar.map_neg_eq_inv, hx a ha, inv_one] }
  have hdot : Continuous fun p : (Fin n → k) × (Fin n → k) => p.1 ⬝ᵥ p.2 :=
    continuous_fst.dotProduct continuous_snd
  have hcoe : Continuous fun z : Circle => (z : ℂ) := continuous_iff_le_induced.mpr fun U a ↦ a
  have hcont : Continuous fun p : (Fin n → k) × (Fin n → k) =>
      ‖((ψ (p.1 ⬝ᵥ p.2) : Circle) : ℂ) - 1‖ :=
    ((hcoe.comp (hψ.comp hdot)).sub continuous_const).norm
  have hU : IsOpen {p : (Fin n → k) × (Fin n → k) | ‖((ψ (p.1 ⬝ᵥ p.2) : Circle) : ℂ) - 1‖ < 1} :=
    isOpen_lt hcont continuous_const
  have hsub : ({0} : Set (Fin n → k)) ×ˢ (A : Set (Fin n → k)) ⊆
      {p : (Fin n → k) × (Fin n → k) | ‖((ψ (p.1 ⬝ᵥ p.2) : Circle) : ℂ) - 1‖ < 1} := by
    rintro ⟨x, a⟩ ⟨hx, -⟩
    have hx0 : x = 0 := hx
    subst hx0
    simp
  obtain ⟨V, W, hV, -, h0V, hAW, hVW⟩ := generalized_tube_lemma isCompact_singleton hA hU hsub
  have hmem : (H : Set (Fin n → k)) ∈ 𝓝 (0 : Fin n → k) := by
    refine Filter.mem_of_superset (hV.mem_nhds (h0V rfl)) ?_
    intro ξ hξ a ha
    apply GlobalTheory.CharDualMat.circle_eq_one_of_pow_near
    intro m
    have hma : m • a ∈ (A : Set (Fin n → k)) := SetLike.mem_coe.mpr (A.nsmul_mem ha m)
    have h1 := hVW (Set.mk_mem_prod hξ (hAW hma))
    rw [Set.mem_setOf_eq, dotProduct_smul, AddChar.map_nsmul_eq_pow, Circle.coe_pow] at h1
    exact h1
  exact AddSubgroup.isOpen_of_mem_nhds H hmem

end GlobalTheory.CompanionTheory.AnnihOpen
