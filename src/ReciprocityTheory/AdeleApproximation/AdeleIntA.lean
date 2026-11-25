module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.AdeleApproximation.AdeleIntA
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

noncomputable section

open IsDedekindDomain WithZero

namespace ReciprocityTheory.UG.AdeleIntA

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def IsInt (y : FiniteAdeleRing R K) : Prop := ∀ v : HeightOneSpectrum R, y v ∈ v.adicCompletionIntegers K

theorem val_R (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r :=
  ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.val_R v r

theorem isInt_R (r : R) : IsInt (algebraMap K (FiniteAdeleRing R K) (algebraMap R K r)) :=
  fun v => ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.int_R v r

theorem exists_approx (y : FiniteAdeleRing R K) (hy : ∀ v : HeightOneSpectrum R, y v ∈ v.adicCompletionIntegers K)
    (m : R) (hm : m ≠ 0) : ∃ a : R, ∀ v : HeightOneSpectrum R,
      Valued.v (y v - algebraMap K (v.adicCompletion K) (algebraMap R K a)) ≤ v.intValuation m :=
  ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx y hy m hm

theorem exists_approx_adele (α : FiniteAdeleRing R K) : ∃ u : K, IsInt (α - algebraMap K (FiniteAdeleRing R K) u) :=
  ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx_adele α

end ReciprocityTheory.UG.AdeleIntA
