module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIff
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

theorem UpperTheory.Gal.TranscendenceTraces.sHSec_of :
    SHSec := by
  intro T C _ _ _ _ _ hSH
  obtain ⟨hH, hS⟩ := hSH
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := C)
    (⟨IsLocalRing.maximalIdeal T, inferInstance⟩ : PrimeSpectrum T)
  have hq' : (PrimeSpectrum.asIdeal q).comap (algebraMap T C) = IsLocalRing.maximalIdeal T :=
    congrArg PrimeSpectrum.asIdeal hq
  haveI : (PrimeSpectrum.asIdeal q).IsPrime := PrimeSpectrum.isPrime q
  obtain ⟨s, -⟩ := (GlobalTheory.StrictHensel.strictlyHenselian_iff T).2 ⟨inferInstance, inferInstance⟩
    C (PrimeSpectrum.asIdeal q) hq'
  exact ⟨s⟩
