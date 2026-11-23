module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColsWPart

theorem wpart_mem_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (u : Fin S.rank → D.host.E) (m₀ : Y) (c₀ : k), IntIn q S F L → valuation k c₀ = 1 → (∀ r, F.β r m₀ = c₀ * (ofSplit q).pr (u r)) → ∀ a : AE D, ((fun r => q.e * (a * incA D (u r))) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ q.pr a ∈ 𝒪[k]) := by
  intro D k _ _ _ _ q S L Y _ _ F u m₀ c₀ hI hc hcol a
  have hc0 : c₀ ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact zero_ne_one hc
  have heq : (fun i => q.sec ((F.β *ᵥ Pi.single m₀ (q.pr a / c₀)) i)) = fun r => q.e * (a * incA D (u r)) := by
    funext r
    have h1 : (F.β *ᵥ Pi.single m₀ (q.pr a / c₀)) r = F.β r m₀ * (q.pr a / c₀) := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h1, hcol r, ← q.sec_pr, map_mul q.pr]
    congr 1
    show c₀ * q.pr (incA D (u r)) * (q.pr a / c₀) = q.pr a * q.pr (incA D (u r))
    field_simp
  rw [← heq, ← hI (Pi.single m₀ (q.pr a / c₀))]
  have hdiv : q.pr a / c₀ ∈ 𝒪[k] ↔ q.pr a ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_div₀, hc, div_one]
  constructor
  · intro h
    have := h m₀
    rw [Pi.single_eq_same] at this
    exact hdiv.1 this
  · intro h i
    by_cases hi : i = m₀
    · subst hi; rw [Pi.single_eq_same]; exact hdiv.2 h
    · rw [Pi.single_eq_of_ne hi]; exact zero_mem _

end GlobalTheory.ColsWPart
