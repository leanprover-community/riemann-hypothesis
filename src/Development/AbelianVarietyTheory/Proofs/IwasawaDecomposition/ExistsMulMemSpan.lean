module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.LevLaws

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


omit [StarRing E] in
theorem exists_mul_mem_span (P : HeightOneSpectrum (𝓞 E)) {q : 𝓞 E} (hq : q ∈ P.asIdeal)
    (hq2 : q ∉ P.asIdeal ^ 2) : ∃ s ∉ P.asIdeal, ∀ r ∈ P.asIdeal, ∃ t, s * r = q * t := by
  have h1 : P.asIdeal ∣ Ideal.span {q} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hq)
  obtain ⟨J, hJ⟩ := h1
  have h2 : ¬ J ≤ P.asIdeal := by
    intro h
    apply hq2
    have : q ∈ P.asIdeal * J := hJ ▸ Ideal.mem_span_singleton_self q
    rw [sq]
    exact Ideal.mul_mono_right h this
  obtain ⟨s, hs, hsP⟩ := SetLike.not_le_iff_exists.1 h2
  refine ⟨s, hsP, fun r hr => ?_⟩
  have : r * s ∈ Ideal.span {q} := hJ ▸ Ideal.mul_mem_mul hr hs
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨t, by rw [mul_comm s r, ← ht, mul_comm]⟩

end Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

end GlobalTheory.Mem.Col2.LevLaws
