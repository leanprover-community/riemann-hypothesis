module

import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.DiagDifferent

theorem trace_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (a : E) :
    Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem conj_rt {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : cc (H.rt : E) = -(H.rt : E) := by
  apply GlobalTheory.OneSpace.cc_rt <;> assumption

theorem cmField_host_element_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h1 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  have h2 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h1
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    exact this
  rw [conj_rt] at h2
  have : (2 : E) * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1 := by linear_combination h1 + h2
  exact mul_left_cancel₀ two_ne_zero this

theorem trace_even_real_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (∀ a ∈ I, cc a ∈ I) → cc x = x → ((∀ s ∈ I, cc s = s → ∃ n : ℤ, Algebra.trace ℚ E (x * s) = 2 * n) ↔ ∀ s ∈ I, ∃ n : ℤ, Algebra.trace ℚ E (x * s) = n) := by
  intro E _ _ _ H I x hI hx
  have hmul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => map_mul _ a b
  have hadd : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => map_add _ a b
  have hcc : ∀ a : E, cc (cc a) = a := fun a => IsCMField.complexConj_apply_apply E a
  constructor
  · intro h s hs
    have hm : s + cc s ∈ I := Submodule.add_mem (I : Submodule (𝓞 E) E) hs (hI s hs)
    obtain ⟨n, hn⟩ := h (s + cc s) hm (by rw [hadd, hcc, add_comm])
    refine ⟨n, ?_⟩
    have e : x * cc s = cc (x * s) := by rw [hmul, hx]
    rw [mul_add, map_add (f := _), e, trace_conj] at hn
    linarith
  · intro h s hs hcs
    have hm : (H.w0 : E) * s ∈ I := Submodule.smul_mem (I : Submodule (𝓞 E) E) H.w0 hs
    obtain ⟨n, hn⟩ := h _ hm
    refine ⟨n, ?_⟩
    have e : x * s = x * ((H.w0 : E) * s) + cc (x * ((H.w0 : E) * s)) := by
      rw [hmul, hmul, hx, hcs]
      linear_combination (-(x * s)) * cmField_host_element_add_conj_eq_one H
    rw [e, map_add (f := _), trace_conj, hn]
    ring

end GlobalTheory.DiagDifferent
