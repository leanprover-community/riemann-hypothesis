module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

theorem UpperTheory.V.Pr.coefIs :
    UpperTheory.V.Pr.CoefIs := by
  intro l hl c
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, ?_⟩
  have h0 : (l : IsLocalRing.ResidueField c.O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  exact (CharP.charP_iff_prime_eq_zero hl.out).2 h0
