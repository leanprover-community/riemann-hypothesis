module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonVEqZeroIffMemRangeCrisIncl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

theorem UpperTheory.weil_deligne_span_crystalline :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsPst P ρ → IsCrys (P.PD K) ρ → Submodule.span ℂ {z : WDSpace P ι ρ | ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD K) ρ ∧ (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x ∧ z = wdMk P ι ρ y} = ⊤ := by
  intro l _ P ι K LL V _ _ _ _ _ ρ hV hc
  have hk := mem_Dst_and_monV_eq_zero_iff l P K LL V ρ
  set S := Submodule.span ℂ {z : WDSpace P ι ρ | ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD K) ρ ∧ (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x ∧ z = wdMk P ι ρ y} with hS
  have key : ∀ (x : V ⊗[ℚ_[l]] Bst P), x ∈ Dpst P ρ → ∃ h : x ∈ Dpst P ρ, wdMk P ι ρ ⟨x, h⟩ ∈ S := by
    intro x hx
    refine AddSubgroup.closure_induction
      (p := fun y _ => ∃ h : y ∈ Dpst P ρ, wdMk P ι ρ ⟨y, h⟩ ∈ S) ?_ ?_ ?_ ?_
      (GlobalTheory.PstLaws.mem_closure_of_isCrys P ρ hV hc x hx)
    · rintro _ ⟨c, s, hs, rfl⟩
      have hsD : s ∈ Dpst P ρ := Dst_resTo_le P ρ le_rfl ((hk s).mpr hs).1
      obtain ⟨x₀, hx₀, e⟩ := hs
      refine ⟨mulV_mem_Dpst P ρ c s hsD, ?_⟩
      have h1 : wdMk P ι ρ ⟨s, hsD⟩ ∈ S := Submodule.subset_span ⟨x₀, ⟨s, hsD⟩, hx₀, e.symm, rfl⟩
      have h2 := S.smul_mem (ι (c : Om l)) h1
      rw [← wdMk_mul] at h2
      exact h2
    · refine ⟨zero_mem _, ?_⟩
      have h1 : wdMk P ι ρ 0 ∈ S := by rw [wdMk_zero]; exact zero_mem _
      exact h1
    · rintro y z _ _ ⟨hy, h1⟩ ⟨hz, h2⟩
      refine ⟨add_mem hy hz, ?_⟩
      have h3 := S.add_mem h1 h2
      rw [← wdMk_add] at h3
      exact h3
    · rintro y _ ⟨hy, h1⟩
      refine ⟨neg_mem hy, ?_⟩
      have heq : wdMk P ι ρ ⟨-y, neg_mem hy⟩ = -wdMk P ι ρ ⟨y, hy⟩ := by
        apply eq_neg_of_add_eq_zero_left
        rw [← wdMk_add]
        have hz : (⟨-y, neg_mem hy⟩ : ↥(Dpst P ρ)) + ⟨y, hy⟩ = 0 := by
          ext
          simp
        rw [hz, wdMk_zero]
      rw [heq]
      exact S.neg_mem h1
  rw [eq_top_iff, ← span_wdMk P ι ρ, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact (key x.1 x.2).2
