module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExtCContract
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.WithBotEqOfAddOne

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem map_int_comp :
    (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) := by
  apply RingHom.ext
  intro p
  rw [RingHom.comp_apply, MvPolynomial.map_map]
  congr 1

theorem pC_eq_extC_extQ (P : Ideal (MRing ι)) : pC P = extC (extQ P) := by
  unfold pC extC extQ
  rw [Ideal.map_map, map_int_comp]
  rfl

theorem horizontal_spec {P : Ideal (MRing ι)} (h : IsHorizontal P) :
    ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := by
  intro m hm
  have h1 : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
  unfold IsHorizontal at h
  rw [h] at h1
  exact Ideal.mem_bot.mp h1

theorem pcEquidim : PCEquidimStatement := by
  intro K _ ι _ P e hP Q hQ
  obtain ⟨_, hMP, hH, hdim⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨hpr, _, hd⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  rw [pC_eq_extC_extQ] at hQ
  rw [ringKrullDim_of_mem_minimalPrimes_extC (extQ P) Q hQ]
  apply withBot_eq_of_add_one
  rw [hd, hdim, show e + 1 + Fintype.card K = e + Fintype.card K + 1 by omega]

theorem pcMinContract : PCMinContractStatement := by
  intro K _ ι _ P e hP Q hQ
  obtain ⟨_, hMP, hH, _⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨hpr, hcomap, _⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  rw [pC_eq_extC_extQ] at hQ
  rw [← map_int_comp, ← Ideal.comap_comap, comap_of_mem_minimalPrimes_extC (extQ P) Q hQ, hcomap]

theorem pcContract : PCContractStatement := by
  intro K _ ι _ P e hP f hf
  obtain ⟨_, hMP, hH, _⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨_, hcomap, _⟩ := extQ_spec P (horizontal_spec hH)
  rw [pC_eq_extC_extQ] at hf
  have h1 : f ∈ (extC (extQ P)).comap (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) := hf
  rw [← map_int_comp, ← Ideal.comap_comap, comap_extC, hcomap] at h1
  exact h1

end ReciprocityTheory.ChartRestriction.G.Geo
