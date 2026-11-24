module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

variable {F : Type} [Field F] [NumberField F]

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

theorem unrWhitX_of_parts (hC : LocC) (hA : AlmostGood) : UnrWhitX := by
  intro F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d bs ψ hψ
  refine ⟨(n : ℝ) ^ 2, ?_⟩
  filter_upwards [hA F E σ hσ M J hJ n T hT hdet d bs ψ hψ] with v hv
  obtain ⟨S, σS, ϖ, ε, hε, hG⟩ := hv
  intro μv νv lam L hμ hν hlam hL z hz
  rw [← hε]
  exact hC F E σ M n d J T hT bs v (psiV F ψ v) S σS ϖ ε hG μv νv lam L hμ hν hlam hL z hz

theorem eSp_eq (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : ℤˣ, ((e : ℤ) : ℂ) = eSp E v := by
  unfold eSp
  split_ifs
  · exact ⟨-1, by simp⟩
  · exact ⟨1, by simp⟩

theorem unrWhitAll_of_X (h : UnrWhitX) : UnrWhitAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d bs ψ hψ
  obtain ⟨t, ht⟩ := h F E σ hσ M J hJ n T hT hdet d bs ψ hψ
  refine ⟨t, ?_⟩
  filter_upwards [ht] with v hv
  obtain ⟨e, he⟩ := eSp_eq E v
  exact ⟨e, fun μv νv lam L hμ hν hlam hL z hz => by rw [he]; exact hv μv νv lam L hμ hν hlam hL z hz⟩

theorem unrWhitAll_of_parts (hC : LocC) (hA : AlmostGood) : UnrWhitAll := unrWhitAll_of_X (unrWhitX_of_parts hC hA)

theorem unrWhit_of_all (h : UnrWhitAll) : UnrWhit :=
  fun F E _ _ _ _ _ σ hσ M J hJ n _ T hT hdet d bs ψ hψ => h F E σ hσ M J hJ n T hT hdet d bs ψ hψ

theorem unrWhit_of_parts (hC : LocC) (hA : AlmostGood) : UnrWhit := unrWhit_of_all (unrWhitAll_of_parts hC hA)

end PositivityTheory.SiegelWeilFormula.Gunr

end
