module

public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC

namespace GlobalTheory.Cong

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def NonSplitSet (T : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ w ∈ T, ¬ IsSplitAt w

structure MatchOffT (U : Submodule ℂ (UA E a → ℂ)) (π : CuspSub E a) (T : Finset (HeightOneSpectrum (𝓞 E))) : Prop where
  aut : IsAutRepU U
  unram : ∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w
  split : ∀ w, IsSplitAt w → ∀ σ, π.IsLocComp w σ → IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ
  inf : ∀ τ lam, HasWeightAt U τ lam → (CG.mk π).infChar τ = infOfWeight lam

def DescOffT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), l.Prime → 1 ≤ a → ∀ π : CuspSub E a,
    InScope .csd l π (quadChar E ^ a) → ∀ Z : Finset (HeightOneSpectrum (𝓞 E)),
    ∃ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T ∧ Disjoint T Z ∧
      ∃ U : Submodule ℂ (UA E a → ℂ), MatchOffT U π T

theorem nonSplitSet_empty : NonSplitSet (∅ : Finset (HeightOneSpectrum (𝓞 E))) := by
  intro w hw
  simp at hw

theorem matchOffT_of_match {U : Submodule ℂ (UA E a → ℂ)} {π : CuspSub E a} (h : Match U π)
    (T : Finset (HeightOneSpectrum (𝓞 E))) : MatchOffT U π T :=
  ⟨h.aut, fun w hw _ => h.unram w hw, h.split, h.inf⟩

theorem descOffT_of_desc (h : Desc) : DescOffT := by
  intro E _ _ _ l a hl ha π hπ Z
  obtain ⟨U, hU⟩ := h E l a hl ha π hπ
  exact ⟨∅, nonSplitSet_empty, Finset.disjoint_empty_left Z, U, matchOffT_of_match hU ∅⟩

end GlobalTheory.Cong

end
