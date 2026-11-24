module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RingHom.Flat
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.flatHt :
    ∀ (A R : Type) [CommRing A] [CommRing R] [IsNoetherianRing A] [IsNoetherianRing R] (ι : A →+* R), ι.Flat → ∀ (q : Ideal A) (Q : Ideal R),
        Q.IsPrime → Q.comap ι = q → Q ∈ (q.map ι).minimalPrimes → Q.height = q.height := by
  intro A R _ _ _ _ ι hι q Q hQ hcomap hmin
  letI : Algebra A R := ι.toAlgebra
  haveI : Module.Flat A R := hι
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : q.IsPrime := hcomap ▸ Ideal.comap_isPrime ι Q
  haveI : Q.LiesOver q := ⟨hcomap.symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q]
  suffices h0 : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).height = 0 by
    rw [h0, add_zero]
  have hJQ : q.map (algebraMap A R) ≤ Q := hmin.1.2
  have hker : RingHom.ker (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q := by
    rw [Ideal.mk_ker]
    exact hJQ
  haveI : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  rw [Ideal.height_eq_zero_iff]
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  rintro K ⟨hK, -⟩ hKQ
  have hle : K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hKQ hx)
    have hd : y - x ∈ q.map (algebraMap A R) := Ideal.Quotient.eq.mp hxy
    have hx' : x = y - (y - x) := by ring
    rw [hx']
    exact Q.sub_mem hy (hJQ hd)
  have hc : Q ≤ K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) := by
    refine hmin.2 ⟨Ideal.comap_isPrime _ K, ?_⟩ hle
    intro x hx
    have hx2 : x ∈ q.map (algebraMap A R) := hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx2]
    exact K.zero_mem
  exact Ideal.map_le_iff_le_comap.mpr hc
