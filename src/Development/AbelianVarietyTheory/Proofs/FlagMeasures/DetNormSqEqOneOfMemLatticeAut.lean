module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlVolEqTsumSlabVol
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.OrbitTerm


open MeasureTheory NumberField Matrix Finset in
open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL : ∀ (E : Type) [Field E] [NumberField E],
    IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ →
      ∀ γ ∈ _root_.GlobalTheory.FlagMeas.autGL E j Λ, _root_.GlobalTheory.FlagMeas.detNorm E j γ = 1 := by
  intro E _ _ hE j Λ hΛ γ hγ
  obtain ⟨κ, hκ, hcov⟩ := (_root_.GlobalTheory.LatFacts.lattice_facts E hE j).1 Λ hΛ
  have hpos := _root_.GlobalTheory.OrbitTerm.detNorm_pos_of_mem_autGL hγ
  have h1 := (hcov γ hpos).2.1
  have h2 := (hcov (_root_.GlobalTheory.OrbitTerm.oneInf E j) (by
    rw [_root_.GlobalTheory.OrbitTerm.detNorm_oneInf]; exact one_pos)).2.1
  rw [_root_.GlobalTheory.OrbitTerm.detNorm_oneInf, div_one] at h2
  have hmul := _root_.GlobalTheory.FlagBase.Test.latAt_aut_mul E j Λ hγ (_root_.GlobalTheory.OrbitTerm.oneInf E j)
  rw [_root_.GlobalTheory.OrbitTerm.mul_oneInf] at hmul
  rw [hmul, h2] at h1
  field_simp at h1
  linarith

end GlobalTheory.OrbitTerm
