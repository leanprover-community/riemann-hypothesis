module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.eq_one_of_irreducible_pi_abelian_fixed_ne_bot :
    ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)], (∀ a (x y : Γ a), x * y = y * x) →
    ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (∀ a, Γ a) Y) (H : ∀ a, Subgroup (Γ a)), τ.IsIrreducible →
    (∀ a, fixed (τ.comp (MonoidHom.mulSingle Γ a) : Representation ℂ (Γ a) Y) (H a) ≠ ⊥) → ∀ g : ∀ a, Γ a, (∀ a, g a ∈ H a) → τ g = 1 := by
  intro α _ _ Γ _ hcomm Y _ _ τ H hirr hne g hg
  have hfixall : ∀ a (h : H a) (y : Y), τ (Pi.mulSingle a (h : Γ a)) y = y := by
    intro a
    have hc : ∀ (x : Γ a) (g' : ∀ b, Γ b), Pi.mulSingle a x * g' = g' * Pi.mulSingle a x := by
      intro x g'
      funext b
      simp only [Pi.mul_apply]
      exact hcomm b _ _
    let R : Subrepresentation τ :=
      { toSubmodule := fixed (τ.comp (MonoidHom.mulSingle Γ a) : Representation ℂ (Γ a) Y) (H a)
        apply_mem_toSubmodule := by
          intro g' y hy h
          have hy' := hy h
          simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply,
            MonoidHom.mulSingle_apply] at hy' ⊢
          rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hy'] }
    have hR : R = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top R with h | h
      · exfalso
        apply hne a
        have := congrArg Subrepresentation.toSubmodule h
        exact this
      · exact h
    intro h y
    have hy : y ∈ R.toSubmodule := by
      rw [hR]
      exact Submodule.mem_top
    have := hy h
    simpa using this
  letI : ∀ a, CommGroup (Γ a) := fun a => { (inferInstance : Group (Γ a)) with mul_comm := hcomm a }
  have hs : ∀ (s : Finset α) (y : Y), τ (∏ a ∈ s, Pi.mulSingle a (g a)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y
      rw [Finset.prod_empty, map_one, Module.End.one_apply]
    | insert a s ha ih =>
      intro y
      rw [Finset.prod_insert ha, map_mul, Module.End.mul_apply, ih]
      exact hfixall a ⟨g a, hg a⟩ y
  have hg' : g = ∏ a, Pi.mulSingle a (g a) := (Finset.univ_prod_mulSingle g).symm
  ext y
  rw [Module.End.one_apply]
  conv_lhs => rw [hg']
  exact hs Finset.univ y
