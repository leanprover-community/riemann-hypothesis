module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime]

theorem projective_La_int (D : Datum p) :
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    Module.Projective (𝓞 D.F) D.La := by
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := D.freeLa
  haveI := D.finLa
  have htor : Submodule.torsion (𝓞 D.F) D.La = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : (a : 𝓞 D.F) ≠ 0 := nonZeroDivisors.ne_zero a.2
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) ha0 (Ideal.mem_span_singleton_self (a : 𝓞 D.F))
      (Algebra.IsIntegral.isIntegral (R := ℤ) (a : 𝓞 D.F))
    obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at he
    obtain ⟨d, hd⟩ := he
    have h1 : e • x = 0 := by
      have : (algebraMap ℤ (𝓞 D.F) e) • x = e • x := by
        rw [algebraMap_smul]
      rw [← this, ← hd, mul_smul]
      change d • (a • x) = 0
      rw [hax, smul_zero]
    rcases smul_eq_zero.1 h1 with h | h
    · exact absurd h he0
    · exact (Submodule.mem_bot _).2 h
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 D.F) D.La
  have : Module.Flat (𝓞 D.F) D.La := (IsDedekindDomain.flat_iff_torsion_eq_bot).2 htor
  have := Module.finitePresentation_of_finite (𝓞 D.F) D.La
  exact Module.Flat.projective_of_finitePresentation

end GlobalTheory.UPel.HT.EtLev
