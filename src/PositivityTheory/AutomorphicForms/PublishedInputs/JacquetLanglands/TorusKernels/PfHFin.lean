module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc

namespace UpperTheory.Esk.FiniteLevelGroupLemmas

def Gm (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) :
    (X (InfinitePlace F) × GF F → ℂ) →ₗ[ℂ] (GA F 2 → ℂ) where
  toFun f := Classical.choose ((h F k).1 f)
  map_add' f f' := by
    have e := (h F k).2.2.2.1 f f' _ _ 1 (Classical.choose_spec ((h F k).1 f)) (Classical.choose_spec ((h F k).1 f'))
    simp only [one_smul] at e
    exact (h F k).2.1 _ _ _ (Classical.choose_spec ((h F k).1 (f + f'))) e
  map_smul' s f := by
    have e := (h F k).2.2.2.1 0 f 0 _ s (h F k).2.2.2.2.1 (Classical.choose_spec ((h F k).1 f))
    simp only [zero_add] at e
    exact (h F k).2.1 _ _ _ (Classical.choose_spec ((h F k).1 (s • f))) e

theorem rel (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ)
    (f : X (InfinitePlace F) × GF F → ℂ) : Rel k f (Gm h F k f) :=
  Classical.choose_spec ((h F k).1 f)

theorem inj (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) :
    Function.Injective (Gm h F k) := by
  intro f f' e
  have h2 := rel h F k f'
  rw [← e] at h2
  exact (h F k).2.2.1 f f' _ (rel h F k f) h2

end UpperTheory.Esk.FiniteLevelGroupLemmas

theorem UpperTheory.Esk.pf_HFin : UpperTheory.Esk.HRel → UpperTheory.Esk.H2a → UpperTheory.Esk.H2d → UpperTheory.Esk.H2e → UpperTheory.Esk.HFinC → UpperTheory.Esk.HFin := by
  intro hR h2a h2d h2e hC F _ _ _ k c hc ω χ hω hχ hS hk
  classical
  let S : Set (TR.Sm F 2) := {φ | IsHolV k c ω φ ∧ TR.IsCuspForm φ}
  have : FiniteDimensional ℂ (Submodule.span ℂ S) := hC F k c hc ω hω
  let W : Submodule ℂ (GA F 2 → ℂ) := (Submodule.span ℂ S).map (TR.Sm F 2).subtype
  have : FiniteDimensional ℂ W := inferInstance
  let p := Submodule.span ℂ {f | (mkDat c χ).IsForm k f}
  have hle : p.map (FiniteLevelGroupLemmas.Gm hR F k) ≤ W := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hrel := FiniteLevelGroupLemmas.rel hR F k f
    obtain ⟨hs, hhol⟩ := h2d F k c hc ω χ hω hχ hS hk f _ hf hrel
    have hb := (h2a F k c hc ω χ hω hχ hS hk f _ hf hrel).2.2.2
    have hcusp := h2e F k c ω ⟨_, hs⟩ hω hk hhol hb
    exact ⟨⟨_, hs⟩, Submodule.subset_span ⟨hhol, hcusp⟩, rfl⟩
  have : FiniteDimensional ℂ (p.map (FiniteLevelGroupLemmas.Gm hR F k)) := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (FiniteLevelGroupLemmas.inj hR F k) p).symm
