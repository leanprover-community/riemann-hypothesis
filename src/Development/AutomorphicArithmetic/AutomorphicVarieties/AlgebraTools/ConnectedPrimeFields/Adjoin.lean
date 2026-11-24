module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CmFree
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
import Mathlib.RingTheory.PicardGroup
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
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.adjoin :
    ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra A R] [Module.Finite A R] [FaithfulSMul A R], IsBase A → ∀ f : R,
      ∃ _ : IsLocalRing (Algebra.adjoin A {f}), ReciprocityTheory.CA.IsCM (Algebra.adjoin A {f}) := by
  intro A R _ _ _ _ _ _ _ _ _ hA f
  have hf : IsIntegral A f := Algebra.IsIntegral.isIntegral f
  haveI : IsIntegrallyClosed A := hA.normal
  haveI : Algebra.IsIntegral (Algebra.adjoin A {f}) R := Algebra.IsIntegral.tower_top A
  haveI : IsLocalRing (Algebra.adjoin A {f}) :=
    RingHom.domain_isLocalRing (algebraMap (Algebra.adjoin A {f}) R)
  refine ⟨inferInstance, ?_⟩
  haveI : Module.Free A (Algebra.adjoin A {f}) := .of_basis (Algebra.adjoin.powerBasis' hf).basis
  haveI : Module.Finite A (Algebra.adjoin A {f}) := .of_basis (Algebra.adjoin.powerBasis' hf).basis
  exact cmFree hA.cm
