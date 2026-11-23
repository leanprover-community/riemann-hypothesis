module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aTrans : ATrans := by
  intro F _ _ _
  classical
  let b := mixedEmbedding.latticeBasis F
  refine ⟨(∑ i, ‖b i‖) + 1, by positivity, fun x => ?_⟩
  let p : mixedEmbedding.mixedSpace F := (fun w => x w.1, 0)
  have hm : (ZSpan.floor b p : mixedEmbedding.mixedSpace F) ∈
      Submodule.span ℤ (Set.range b) := (ZSpan.floor b p).2
  rw [mixedEmbedding.mem_span_latticeBasis] at hm
  obtain ⟨s, hs⟩ := hm
  refine ⟨-(s : F), (RingOfIntegers.isIntegral_coe s).neg, fun v => ?_⟩
  have h1 := ZSpan.norm_fract_le b p
  have h2 : (ZSpan.fract b p).1 ⟨v, IsTotallyReal.isReal v⟩ = x v + sg v (-(s : F)) := by
    rw [ZSpan.fract_apply, ← hs]
    simp [p, sg, sub_eq_add_neg]
  have h3 : ‖(ZSpan.fract b p).1 ⟨v, IsTotallyReal.isReal v⟩‖ ≤ ‖ZSpan.fract b p‖ :=
    (norm_le_pi_norm _ _).trans (norm_fst_le _)
  rw [h2, Real.norm_eq_abs] at h3
  linarith

end UpperTheory.Esk
