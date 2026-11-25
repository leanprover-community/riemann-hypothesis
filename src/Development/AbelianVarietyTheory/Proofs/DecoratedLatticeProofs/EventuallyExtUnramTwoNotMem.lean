module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter IsDedekindDomain

namespace GlobalTheory.FinPl

theorem eventually_extUnram_two_notMem : ∀ D : D7, ∀ᶠ v : Pl D in cofinite, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v ∧ (2 : 𝓞 D.host.F) ∉ v.asIdeal := by
  intro D
  rw [Filter.eventually_cofinite]
  have h2 : (2 : 𝓞 D.host.F) ≠ 0 := two_ne_zero
  have hB : (Ideal.span {(2 : 𝓞 D.host.F)}) ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using h2
  have hfin2 := Ideal.finite_factors hB
  have hfinD := Ideal.finite_factors
    (differentIdeal_ne_bot (A := 𝓞 D.host.F) (B := 𝓞 D.host.E))
  have hfinU : ((fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.asIdeal.under (𝓞 D.host.F)) ''
      {Q | Q.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E)}).Finite := hfinD.image _
  have hfinA : {v : Pl D | v.asIdeal ∈ (fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.asIdeal.under (𝓞 D.host.F)) ''
      {Q | Q.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E)}}.Finite :=
    hfinU.preimage (f := fun v : Pl D => v.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
  refine (hfinA.union hfin2).subset fun v hv => ?_
  by_cases h : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · right
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h)
  · left
    have hE : ¬ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v := fun hu => hv ⟨hu, h⟩
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt at hE
    push_neg at hE
    obtain ⟨P, hP, hL, hU⟩ := hE
    have hover : v.asIdeal = P.under (𝓞 D.host.F) := hL.over
    have hPb : P ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [hover, Ideal.under_bot]
    refine ⟨⟨P, hP, hPb⟩, ?_, hover.symm⟩
    by_contra hd
    exact hU (not_dvd_differentIdeal_iff.1 hd)

end GlobalTheory.FinPl
