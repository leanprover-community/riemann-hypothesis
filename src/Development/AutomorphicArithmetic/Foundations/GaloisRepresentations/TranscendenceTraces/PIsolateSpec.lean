module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
public import Mathlib.RingTheory.Etale.QuasiFinite
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

theorem UpperTheory.Gal.TranscendenceTraces.isolateSpec_of :
    IsolateSpec := by
  intro R B _ _ _ _ z
  let z' : PrimeSpectrum B := z
  haveI : z'.asIdeal.IsPrime := z'.isPrime
  haveI : Algebra.QuasiFiniteAt R z'.asIdeal := inferInstance
  obtain ⟨R', _, _, hEt, P, _, _, e, he, P', hP', hlo, hq, heP, -, -, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (z'.asIdeal.under R) z'.asIdeal
  have pb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R R' B)).flip
  refine ⟨⟨Spec (CommRingCat.of R'), Spec (CommRingCat.of (TensorProduct R R' B)), _, _, _, pb⟩,
    ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum (TensorProduct R R' B))) :
      Set (PrimeSpectrum (TensorProduct R R' B))),
    (⟨P', hP'⟩ : PrimeSpectrum (TensorProduct R R' B)), ?_, ?_, ?_, ?_, ?_⟩
  · exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hEt)
  · exact PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  · exact heP
  · apply PrimeSpectrum.ext
    exact hq
  · intro v' hv' hr
    have h1 : (v' : PrimeSpectrum (TensorProduct R R' B)).asIdeal.LiesOver P := by
      constructor
      have h2 : Ideal.comap (algebraMap R' (TensorProduct R R' B))
          (v' : PrimeSpectrum (TensorProduct R R' B)).asIdeal =
          Ideal.comap (algebraMap R' (TensorProduct R R' B)) P' :=
        congrArg PrimeSpectrum.asIdeal hr
      rw [Ideal.under, h2]
      exact hlo.over
    apply PrimeSpectrum.ext
    exact huniq _ (PrimeSpectrum.isPrime _) h1 hv'
