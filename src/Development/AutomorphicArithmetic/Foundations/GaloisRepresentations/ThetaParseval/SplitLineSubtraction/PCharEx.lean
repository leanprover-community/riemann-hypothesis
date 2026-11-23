module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charEx_holds :
    GlobalTheory.Published.HeckeLAdicCharacter → CharFrob → CharAbove → CharInj → CharEx := by
  classical
  intro H hF hA hI E Ω _ _ _ _ _ l _ ι
  obtain ⟨art, hart, hex⟩ := H E Ω
  have hL : ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n →
      ∃ r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r :=
    fun χ n h => (hex l ι χ n h).exists
  let L : HChar E → ((E →+* ℂ) → ℤ) → (G E Ω →* (Qbar l)ˣ) :=
    fun χ n => if h : IsAlgPos χ n then (hL χ n h).choose else 1
  have hspec : ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n →
      Continuous (L χ n) ∧ IsLAdicOf art ι χ n (L χ n) := by
    intro χ n h
    have e : L χ n = (hL χ n h).choose := dif_pos h
    rw [e]
    exact (hL χ n h).choose_spec
  refine ⟨L, fun χ n h => ⟨(hspec χ n h).1, fun w hw => ⟨fun hl => ?_, ?_⟩⟩, fun χ n χ' n' h h' e => ?_⟩
  · exact hF E Ω l ι art hart χ n (L χ n) (hspec χ n h).2 w hl hw
  · exact hA E Ω l ι art hart χ n (L χ n) h (hspec χ n h).1 (hspec χ n h).2 w hw
  · exact hI E Ω l ι art hart χ χ' n n' (L χ n) (hspec χ n h).2 (e ▸ (hspec χ' n' h').2)
