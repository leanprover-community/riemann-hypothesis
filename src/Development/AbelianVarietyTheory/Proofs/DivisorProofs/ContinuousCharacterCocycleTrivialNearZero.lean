module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerMore
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CocycleChar

theorem pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.InductiveNormBound.main
  | exact _root_.GlobalTheory.InductiveNormBound.main
  | (apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InductiveNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InductiveNormBound.main ..)

theorem cocycle_char_trivial_near_zero :
    ∀ {A V : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A]
    [NonarchimedeanAddGroup A] [AddCommGroup V] [TopologicalSpace V] [T2Space V] (lam : A →+ V), Continuous lam →
    ∀ (ε : V → V → ℂ), (∃ N ∈ nhds (0 : V), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1) → (∀ x, ε x 0 = 1) →
    ∀ (χ : A → ℂ), Continuous χ → (∀ a, lam a = 0 → χ a = 1) →
    (∀ a b, χ (a + b) = χ a * χ b * ε (lam a) (lam b)) → ∃ U ∈ nhds (0 : V), ∀ a, lam a ∈ U → χ a = 1 := by
  intro A V _ _ _ _ _ _ _ _ lam hlam ε ⟨N, hN, hεN⟩ hε0 χ hχ hker hmul
  have hχ0 : χ 0 = 1 := hker 0 (map_zero lam)

  have hW : lam ⁻¹' N ∩ {a : A | ‖χ a - 1‖ < 1 / 2} ∈ nhds (0 : A) := by
    refine Filter.inter_mem ?_ ?_
    · exact hlam.continuousAt.preimage_mem_nhds (by simpa using hN)
    · exact (isOpen_lt (hχ.sub continuous_const).norm continuous_const).mem_nhds (by simp [hχ0])
  obtain ⟨K₀, hK₀⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hW
  have hpow : ∀ a ∈ K₀, ∀ n : ℕ, χ (n • a) = χ a ^ n := by
    intro a ha n
    induction n with
    | zero => simp [hχ0]
    | succ n ih =>
      have h1 : n • a ∈ K₀ := K₀.toAddSubgroup.nsmul_mem ha n
      rw [succ_nsmul, hmul, ih, hεN _ (hK₀ h1).1 _ (hK₀ ha).1, pow_succ, mul_one]
  have hK₀one : ∀ a ∈ K₀, χ a = 1 := by
    intro a ha
    refine pow_near_one fun n => ?_
    rw [← hpow a ha n]
    exact (hK₀ (K₀.toAddSubgroup.nsmul_mem ha n)).2

  set S : AddSubgroup A := K₀.toAddSubgroup ⊔ lam.ker with hSdef
  have hSopen : IsOpen (S : Set A) :=
    AddSubgroup.isOpen_mono (le_sup_left : K₀.toAddSubgroup ≤ S) K₀.isOpen
  set C : Set A := (S : Set A)ᶜ
  have hCc : IsCompact C := hSopen.isClosed_compl.isCompact
  have hLc : IsClosed (lam '' C) := (hCc.image hlam).isClosed
  have h0 : (0 : V) ∉ lam '' C := by
    rintro ⟨c, hc, hc0⟩
    exact hc (le_sup_right (a := K₀.toAddSubgroup) (AddMonoidHom.mem_ker.2 hc0))
  refine ⟨(lam '' C)ᶜ, hLc.isOpen_compl.mem_nhds h0, fun a ha => ?_⟩
  have haS : a ∈ S := by
    by_contra h
    exact ha ⟨a, h, rfl⟩
  obtain ⟨k, hk, n, hn, rfl⟩ := AddSubgroup.mem_sup.1 haS
  rw [AddMonoidHom.mem_ker] at hn
  rw [hmul, hK₀one k hk, hker n hn, hn, hε0, mul_one, mul_one]

end GlobalTheory.CocycleChar
