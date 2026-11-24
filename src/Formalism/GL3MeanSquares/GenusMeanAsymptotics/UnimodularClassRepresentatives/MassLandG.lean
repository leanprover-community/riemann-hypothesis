module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace GramDeterminantPositive

section

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem exists_ortho_ne_zero [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {k : ℕ}
    (v : Fin k → V) (hk : k < finrank K V) : ∃ x : V, x ≠ 0 ∧ ∀ i, h (v i) x = 0 := by
  let f : V →ₗ[K] (Fin k → K) := LinearMap.pi fun i => h (v i)
  have hlt : finrank K (Fin k → K) < finrank K V := by
    rw [Module.finrank_fin_fun]; exact hk
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
  exact ⟨x, hx0, fun i => congrFun (LinearMap.mem_ker.1 hx) i⟩

theorem exists_basis_of_ortho [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {k : ℕ}
    (v : Fin k → V) (hk : finrank K V = k) (ho : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (hne : ∀ i, h (v i) (v i) ≠ 0) : ∃ e : Basis (Fin k) K V, ∀ i, e i = v i := by
  have hli : LinearIndependent K v :=
    LinearMap.linearIndependent_of_isOrthoᵢ (B := h) (fun i j hij => ho i j hij) (fun i => hne i)
  have htop : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hk])
  exact ⟨Basis.mk hli htop.ge, fun i => Basis.mk_apply hli htop.ge i⟩

theorem exists_ortho_family [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) :
    ∀ k : ℕ, k ≤ finrank K V →
      ∃ v : Fin k → V, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, v i ≠ 0 := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, ho, hne⟩ := ih (by omega)
    obtain ⟨x, hx0, hx⟩ := exists_ortho_ne_zero h v (by omega)
    refine ⟨Fin.snoc v x, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hs.isRefl _ _ (hx j)
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hx i
      · intro hij
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact ho i j (fun e => hij (by rw [e]))
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.snoc_last]; exact hx0
      · rw [Fin.snoc_castSucc]; exact hne i

end

end GramDeterminantPositive

theorem orthBasisPos_holds : OrthBasisPos := by
  intro K _ _ _ hK V _ _ _ _ _ h hs hpos
  have hne0 : ∀ x : V, x ≠ 0 → h x x ≠ 0 := by
    intro x hx h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpos x hx φ
    rw [h0, map_zero] at this
    simp at this
  obtain ⟨v, ho, hne⟩ := GramDeterminantPositive.exists_ortho_family h hs (finrank K V) le_rfl
  obtain ⟨e, he⟩ := GramDeterminantPositive.exists_basis_of_ortho h v rfl ho (fun i => hne0 _ (hne i))
  refine ⟨e, fun i j hij => by rw [he, he]; exact ho i j hij, fun i => ⟨?_, ?_⟩⟩
  · exact hs.eq (e i) (e i)
  · exact hpos (e i) (e.ne_zero i)

section

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

end

namespace GramDeterminantPositive

end GramDeterminantPositive

end Formalism.HermitianLattices.Ext.L3
