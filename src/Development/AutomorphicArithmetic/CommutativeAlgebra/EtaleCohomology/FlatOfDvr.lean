module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhiAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCorrPull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtIdBC
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry

private lemma flat_of_dvr {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
    (φ : O →+* O') (ϖ : O) (hϖ : Irreducible ϖ) (h0 : φ ϖ ≠ 0) : φ.Flat := by
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
    rw [map_mul, map_pow] at ha
    rcases mul_eq_zero.1 ha with h | h
    · exact (u.isUnit.map φ).ne_zero h
    · exact pow_ne_zero k h0 h
  algebraize [φ]
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').2 hinj
  have : Module.IsTorsionFree O O' := inferInstance
  exact (inferInstance : Module.Flat O O')

theorem UpperTheory.Ru.crystallineComparison.ptIdBC :
    UpperTheory.Ru.crystallineComparison.PtIdBC := by
  intro l q n O O' _ _ _ _ _ _ φ ϖ hϖ hϖ' hq Y Y' p p' g hpb T hT hId
  have hflat : φ.Flat := flat_of_dvr φ ϖ hϖ hϖ'.ne_zero
  choose T' κ h1 h2 h3 _ using fun j => UpperTheory.Gal.crystallineComparison.corrPull_of l _ _ Y Y' _ p p' g hpb (T j) (hT j)
  refine ⟨T', κ, fun j => ⟨(h1 j).flip, (h2 j).symm, h3 j⟩, ?_⟩
  exact UpperTheory.Gal.crystallineComparison.ptIdBC_of l q n O O' φ hflat ϖ (φ ϖ) (fun _ _ => Iff.rfl)
    (fun a => Ideal.mem_span_singleton.2 (hq a)) Y Y' p p' g hpb T T' κ h1 h2 h3 hId
