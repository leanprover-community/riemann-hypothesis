module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Operations
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystalOfDualAbelianScheme
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffineStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBidualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness, Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIsotropicLiftModIdeal, Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfForallMem

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic\nimport Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw GlobalTheory.Published GlobalTheory.CatCoh

noncomputable section

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIsotropicLiftModIdeal =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIsotropicLiftModIdeal", "h": "module\n\npublic import Mathlib.Algebra.Algebra.Operations\npublic import Mathlib.Algebra.Module.Projective\npublic import Mathlib.RingTheory.Finiteness.Defs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.LinearAlgebra.Projection\npublic import Mathlib.RingTheory.Finiteness.Cardinality\npublic import Mathlib.RingTheory.Ideal.Operations\n\n"}
section -- clump:auto
@[expose] public section

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIsotropicLiftModIdeal =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfForallMem =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfForallMem", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystalOfDualAbelianScheme\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowers\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffineStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness\npublic import Mathlib.Algebra.Algebra.Operations\npublic import Mathlib.Algebra.Module.Projective\npublic import Mathlib.RingTheory.Finiteness.Defs\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIsotropicLiftModIdeal\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBidualityStatement\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne\nimport Mathlib.Algebra.Azumaya.Basic\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Mum
open GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual

namespace GlobalTheory.BirigLift

theorem mem_smul_top_of_forall_mem {R : Type} [CommRing R] (I : Ideal R) {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] (x : Module.Dual R P) (hx : ∀ c, x c ∈ I) :
    x ∈ I • (⊤ : Submodule R (Module.Dual R P)) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have e : x = ∑ i, x (f (Pi.single i 1)) • ((LinearMap.proj i : (Fin n → R) →ₗ[R] R) ∘ₗ s) := by
    ext c
    have hc : c = f (s c) := (LinearMap.congr_fun hs c).symm
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, smul_eq_mul]

    conv_lhs => rw [hc, pi_eq_sum_univ (s c), map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
    congr 3
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [e]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hx _) trivial

theorem apply_mem_of_mem_smul_top {R : Type} [CommRing R] (I : Ideal R) {P : Type*} [AddCommGroup P] [Module R P]
    {x : Module.Dual R P} (hx : x ∈ I • (⊤ : Submodule R (Module.Dual R P))) (c : P) : x c ∈ I := by
  refine Submodule.smul_induction_on (p := fun y : Module.Dual R P ↦ y c ∈ I) hx (fun r hr y _ ↦ ?_) fun y z hy hz ↦ ?_
  · rw [LinearMap.smul_apply, smul_eq_mul]; exact I.mul_mem_right _ hr
  · rw [LinearMap.add_apply]; exact I.add_mem hy hz

theorem exists_perfect_mod {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) {D H : Type*}
    [AddCommGroup D] [Module R D] [AddCommGroup H] [Module R₀ H] (red : D →ₛₗ[π] H)
    (φ : D →ₗ[R] D →ₗ[R] R) (ψ : H →ₗ[R₀] H →ₗ[R₀] R₀) (hπ : Function.Surjective π)
    (hψ : Function.Surjective ψ.flip) (hred : Function.Surjective red)
    (hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule R D))
    (hrel : ∀ x y, ψ (red x) (red y) = π (φ x y)) (l : D →ₗ[R] R) :
    ∃ z, ∀ x, l x - φ x z ∈ RingHom.ker π := by
  have hl : ∀ x, x ∈ (RingHom.ker π) • (⊤ : Submodule R D) → π (l x) = 0 := by
    intro x hx
    refine Submodule.smul_induction_on (p := fun y : D ↦ π (l y) = 0) hx (fun r hr y _ ↦ ?_) fun y z hy hz ↦ ?_
    · rw [map_smul, smul_eq_mul, map_mul, RingHom.mem_ker.1 hr, zero_mul]
    · rw [map_add (f := _), map_add (f := _), hy, hz, add_zero]
  let s := Function.surjInv hred
  have hs : ∀ h, red (s h) = h := Function.surjInv_eq hred
  have key : ∀ x x', red x = red x' → π (l x) = π (l x') := fun x x' e ↦ by
    have := hl (x - x') (hker _ (by rw [map_sub, e, sub_self]))
    rwa [map_sub, map_sub, sub_eq_zero] at this
  let l₀ : H →ₗ[R₀] R₀ :=
    { toFun h := π (l (s h))
      map_add' a b := by
        rw [key (s (a + b)) (s a + s b) (by rw [map_add (f := _), hs, hs, hs]), map_add (f := _), map_add (f := _)]
      map_smul' r h := by
        obtain ⟨r', rfl⟩ := hπ r
        rw [key (s (π r' • h)) (r' • s h) (by rw [map_smulₛₗ, hs, hs]), map_smul, smul_eq_mul, map_mul]
        rfl }
  obtain ⟨w, hw⟩ := hψ l₀
  obtain ⟨z, rfl⟩ := hred w
  refine ⟨z, fun x ↦ RingHom.mem_ker.2 ?_⟩
  have e := LinearMap.congr_fun hw (red x)
  rw [LinearMap.flip_apply, hrel] at e
  rw [map_sub, e, sub_eq_zero]
  exact key _ _ (hs _).symm

end GlobalTheory.BirigLift

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfForallMem =====
