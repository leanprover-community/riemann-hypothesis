module

public import Formalism.LocalRingCardinality.DataForced
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped BigOperators
open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace SumOrbCW

theorem plGG_bijective (D : D7) :
    Function.Bijective (fun z : Bool × HH D => (⟨plGG D z, plGG_mem_Psi D z⟩ : D.R.Psi)) := by
  have hi := D.R.toFrame.iota_bijective
  constructor
  · rintro ⟨b, t⟩ ⟨b', t'⟩ h
    have h' := congrArg Subtype.val h
    cases b <;> cases b' <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h' <;> simp [hi.1 h']
  · rintro ⟨⟨⟨s, c⟩, h⟩, hg⟩
    have hc : c = 1 := hg
    subst hc
    obtain ⟨t, ht⟩ := hi.2 h
    rcases Int.units_eq_one_or s with hs | hs
    · exact ⟨(false, t), by subst hs; simp [plGG, Formalism.HC.Frame.tau1, ht]⟩
    · exact ⟨(true, t), by subst hs; simp [plGG, Formalism.HC.Frame.tau2, ht]⟩

theorem tauPl_bijective (D : D7) : Function.Bijective (tauPl D) :=
  D.eTau.symm.bijective.comp (plGG_bijective D)

theorem sum_wPl (D : D7) (j : ℕ) : (∑ z : Bool × HH D, wPl D j z) = ∑ τ : D.what₂.Tau, wj D j τ :=
  (tauPl_bijective D).sum_comp (wj D j)

end SumOrbCW

end
