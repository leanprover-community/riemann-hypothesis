module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HBBump

theorem exists_bump : ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (B : Subgroup G),
    IsOpen (B : Set G) → IsCompact (B : Set G) → ∀ z : Z, (∀ h : H, (h : G) ∈ B → ρ h z = z) →
    ∃ b : cIndSpace H ρ, (∀ (h : H) (β : G), β ∈ B → b.1.1.1 ((h : G) * β) = ρ h z) ∧
      ∀ p : G, (¬ ∃ h : H, ∃ β ∈ B, p = (h : G) * β) → b.1.1.1 p = 0 := by
  intro G Z _ _ _ _ _ H ρ B hBo hBc z hz
  classical

  have hwell : ∀ (h h' : H) (β β' : G), β ∈ B → β' ∈ B → (h : G) * β = (h' : G) * β' →
      ρ h z = ρ h' z := by
    intro h h' β β' hβ hβ' e
    have ha : ((h'⁻¹ * h : H) : G) ∈ B := by
      have : ((h'⁻¹ * h : H) : G) = β' * β⁻¹ := by
        push_cast
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]
        group
      rw [this]
      exact B.mul_mem hβ' (B.inv_mem hβ)
    have h1 := hz _ ha
    have h2 : h = h' * (h'⁻¹ * h) := by group
    rw [h2, map_mul, Module.End.mul_apply, h1]
  let P : G → Prop := fun p => ∃ h : H, ∃ β ∈ B, p = (h : G) * β
  let f : G → Z := fun p => if hp : P p then ρ hp.choose z else 0
  have hval : ∀ (h : H) (β : G), β ∈ B → f ((h : G) * β) = ρ h z := by
    intro h β hβ
    have hp : P ((h : G) * β) := ⟨h, β, hβ, rfl⟩
    obtain ⟨β', hβ', e⟩ := hp.choose_spec
    simp only [f, dif_pos hp]
    exact hwell _ _ _ _ hβ' hβ e.symm
  have hzero : ∀ p, ¬ P p → f p = 0 := fun p hp => by simp only [f, dif_neg hp]
  have hleft : ∀ (h : H) (g : G), f ((h : G) * g) = ρ h (f g) := by
    intro h g
    by_cases hg : P g
    · obtain ⟨h', β, hβ, rfl⟩ := hg
      have : (h : G) * ((h' : G) * β) = ((h * h' : H) : G) * β := by push_cast; group
      rw [this, hval _ _ hβ, hval _ _ hβ, map_mul, Module.End.mul_apply]
    · have hn : ¬ P ((h : G) * g) := by
        rintro ⟨h', β, hβ, e⟩
        refine hg ⟨h⁻¹ * h', β, hβ, ?_⟩
        push_cast
        rw [mul_assoc, ← e]
        group
      rw [hzero _ hn, hzero _ hg, map_zero]
  have hright : ∀ (p : G), ∀ x ∈ B, f (p * x) = f p := by
    intro p x hx
    by_cases hp : P p
    · obtain ⟨h, β, hβ, rfl⟩ := hp
      rw [mul_assoc, hval _ _ (B.mul_mem hβ hx), hval _ _ hβ]
    · have hn : ¬ P (p * x) := by
        rintro ⟨h, β, hβ, e⟩
        refine hp ⟨h, β * x⁻¹, B.mul_mem hβ (B.inv_mem hx), ?_⟩
        rw [← mul_assoc, ← e]
        group
      rw [hzero _ hn, hzero _ hp]
  let F : indSpace H ρ := ⟨f, hleft⟩
  have hsm : F ∈ smoothPart (ind H ρ) := by
    let T : Subgroup G :=
      { carrier := {g | ind H ρ g F = F}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have hBT : (B : Set G) ⊆ T := by
      intro x hx
      show ind H ρ x F = F
      apply Subtype.ext
      funext p
      exact hright p x hx
    exact T.isOpen_of_mem_nhds (g := 1)
      (Filter.mem_of_superset (hBo.mem_nhds B.one_mem) hBT)
  refine ⟨⟨⟨F, hsm⟩, ⟨(B : Set G), hBc, ?_⟩⟩, hval, hzero⟩
  intro g hg
  by_contra hc
  refine hg (hzero g ?_)
  rintro ⟨h, β, hβ, e⟩
  exact hc ⟨h, h.2, β, hβ, e⟩

end GlobalTheory.CompanionTheory.HBBump
