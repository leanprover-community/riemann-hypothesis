module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.DatExOf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL GlobalTheory.UnitaryBC

theorem UpperTheory.Gal.G1.pBarAdj :
    DiscInt → BarAdj := by
  intro h E _ _ _ A y hy
  obtain ⟨a, b, hab⟩ := h E A y hy
  have hD : (((A.tr ^ 2 - 4 * A.nm : ℤ)) : E) ≠ 0 := by
    exact_mod_cast ne_of_lt A.disc_neg
  have hb : A.bar A.ω = (A.tr : 𝓞 E) - A.ω := by
    rw [← A.tr_eq]; ring
  have h1 := congrArg A.bar hab
  simp only [map_mul, map_add (f := _), map_intCast] at h1
  rw [hb] at h1
  have h2 : (((A.tr ^ 2 - 4 * A.nm : ℤ)) : E) * ((A.bar y : 𝓞 E) : E)
      = (a : E) + (b : E) * ((A.tr : E) - (A.ω : E)) := by
    have h3 := congrArg (algebraMap (𝓞 E) E) h1
    simpa only [map_mul, map_add (f := _), map_sub, map_intCast] using h3
  have e : ((A.bar y : 𝓞 E) : E)
      = ((a : E) + (b : E) * ((A.tr : E) - (A.ω : E))) / (((A.tr ^ 2 - 4 * A.nm : ℤ)) : E) := by
    rw [← h2, mul_div_cancel_left₀ _ hD]
  rw [e]
  exact div_mem (add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _)
    (sub_mem (intCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ _)))) (intCast_mem _ _)
