module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedGLEqOneOfLqPrinc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.AdT.PlaceUnder

theorem exists_star_ne {X : Fields} (hX : X.Ok) : ∃ x : X.E, star x ≠ x := by
  by_contra H
  push Not at H
  have := hX.cplxE
  obtain ⟨φ⟩ : Nonempty (X.E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal φ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, ← hX.conjE, H]

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : SBof I a), P.1 ∈ I.Q a → ∃ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∀ P' : SBof I a, P' ≠ P → ¬ Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P'.1) := by
  classical
  intro B X I hI _ l Z a P _
  have hseam : ∀ Q : HeightOneSpectrum (𝓞 B.fields.E), GlobalTheory.TwU.seamP (sm I l Z) Q = Q := by
    intro Q
    ext x
    exact GlobalTheory.TwU.mem_seamP (sm I l Z) Q x
  obtain ⟨hX, -, -⟩ := base_fields_primes_ok B X
  have hc := (GlobalTheory.TopStepPrimes.primes_top_ok hI B.u₀ a).2.1
  refine ⟨HeightOneSpectrum.under (𝓞 (I.rec7 l Z).host.F) (GlobalTheory.TwU.seamP (sm I l Z) P.1), rfl, fun P' hne hov => ?_⟩
  rw [hseam, hseam] at hov
  have hu : P'.1.under (𝓞 B.fields.F) = P.1.under (𝓞 B.fields.F) := HeightOneSpectrum.ext (Eq.symm hov)
  rcases (GlobalTheory.NormOneUnit.under_eq_iff hX.star_F hX.rankE (exists_star_ne hX) P.1 P'.1).1 hu with h | h
  · exact hne (Subtype.ext h)
  · exact hc P.1 (Finset.mem_union_right _ P.2) (h ▸ Finset.mem_union_right _ P'.2)

end GlobalTheory.Mem.Col2.AdT.PlaceUnder
