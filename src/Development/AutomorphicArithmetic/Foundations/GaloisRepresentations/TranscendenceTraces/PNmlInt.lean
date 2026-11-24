module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem normal_affineOpen_integrallyClosed (S : Scheme.{0}) (hN : Nml S) (U : S.Opens) (hU : IsAffineOpen U)
    [IsDomain Γ(S, U)] : IsIntegrallyClosed Γ(S, U) := by
  refine IsIntegrallyClosed.of_localization_maximal ?_
  intro p _ _
  let y : PrimeSpectrum Γ(S, U) := ⟨p, inferInstance⟩
  have hmem : hU.fromSpec y ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  letI := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨hU.fromSpec y, hmem⟩
  haveI : IsLocalization.AtPrime (S.presheaf.stalk (hU.fromSpec y)) p := hU.isLocalization_stalk' y hmem
  obtain ⟨_, hint⟩ := hN (hU.fromSpec y)
  haveI := hint
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (S.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)).toRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.nmlInt_of :
    NmlInt := by
  intro S _ hN s
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨s, hs⟩⟩
  haveI : IsDomain Γ(S, U) := IsIntegral.component_integral U
  exact ⟨U, hU, hs, inferInstance, normal_affineOpen_integrallyClosed S hN U hU⟩
