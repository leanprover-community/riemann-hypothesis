module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
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
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
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

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pZUnitNorm :
    PadicUnitNorm → ZUnitNorm := by
  intro hP v D hv u hu
  haveI : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hint : ∀ z : v.adicCompletion ℚ, Valued.v z ≤ 1 →
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v z‖ ≤ 1 := by
    intro z hz
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo
      ((HeightOneSpectrum.mem_adicCompletionIntegers ℤ ℚ v).2 hz)
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hn : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ = 1 := by
    apply le_antisymm (hint u hu.le)
    have h1 := hint u⁻¹ (by rw [map_inv₀, hu, inv_one])
    rw [map_inv₀, norm_inv] at h1
    have hne : Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u ≠ 0 := fun h =>
      hu0 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
        (h.trans (map_zero _).symm))
    exact (inv_le_one₀ (norm_pos_iff.2 hne)).1 h1
  have hdiv : ¬ ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ) ∣ 2 * D := by
    intro hd
    apply hv
    have hm : 2 * D ∈ Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ)} :=
      Ideal.mem_span_singleton.2 hd
    rw [Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_map_of_equiv] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    have hid : Rat.IsIntegralClosure.intEquiv ℤ x = x := by
      simpa using eq_intCast (Rat.IsIntegralClosure.intEquiv ℤ : ℤ →+* ℤ) x
    rw [hid] at hxe
    rw [← hxe]
    exact hx
  obtain ⟨x, y, hxy⟩ := hP _ D hdiv _ hn
  refine ⟨(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x,
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm y, ?_⟩
  have h2 := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm hxy
  simpa using h2
