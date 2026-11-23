module

public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FnFGFnTrdeg
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.FlagDim

theorem finrank_host_div_two (D : D7) : Module.finrank ℚ D.host.E / 2 = D.R.f := by
  have h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    push_cast
    ring
  have h' : Module.finrank ℚ D.host.E = 2 * D.R.f := by exact_mod_cast h
  omega

theorem fnFG_fnTrdeg_record : ∀ (D : D7) (Q : Par D), Q.PinDat → ∀ j, InR D j → FnFG (Q.Xo j) Q.c ∧ FnTrdeg (Q.Xo j) Q.c (WeightFamilies.dimY D j) := by
  intro D Q hP j hj
  obtain ⟨hp, hq, -⟩ := hP j hj
  have h := fnFG_fnTrdeg D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c
  rw [finrank_host_div_two] at h
  have e : WeightFamilies.dimY D j = D.R.f * ((Q.Dw j).p * (Q.Dw j).q + (Q.Dw j).p * ((Q.Dw j).p - 1) / 2 +
      (Q.Dw j).q * ((Q.Dw j).q - 1) / 2) := by
    rw [hp, hq]; rfl
  rw [e]
  exact h

end GlobalTheory.FlagDim
