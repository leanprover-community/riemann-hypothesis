module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem comm_of_conj {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (A G G' : M →ₗ[R] M)
    (h : G ∘ₗ A ∘ₗ G' = A) (hid : G' ∘ₗ G = LinearMap.id) : A ∘ₗ G = G ∘ₗ A := by
  calc A ∘ₗ G = (G ∘ₗ A ∘ₗ G') ∘ₗ G := by rw [h]
    _ = G ∘ₗ A ∘ₗ (G' ∘ₗ G) := by simp only [LinearMap.comp_assoc]
    _ = G ∘ₗ A := by rw [hid, LinearMap.comp_id]

theorem UpperTheory.Gal.Int.Geo.hopGal_of :
    G3.HopSpec → OpConj → OpUniq → HopGal := by
  intro hS hC hU l _ k _ hl H Ω _ _ g d hd σ
  refine comm_of_conj _ _ (galTot l Ω H.q σ⁻¹)
    (hU l k hl H Ω g d hd _ (hC l k H Ω g _ σ (hS l hl H Ω g d hd).1)) ?_
  rw [← GlobalTheory.GalV.galTot_mul, inv_mul_cancel, GlobalTheory.GalV.galTot_one]
