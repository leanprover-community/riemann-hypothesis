module

public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityDegreeZero
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.UZGen
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

@[expose] public section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.graded_quotient_isomorphism {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (F G : GMod B R k) (f : F.M →ₗ[R] G.M) (hf : Function.Surjective f)
    (hg : ∀ m, G.gr m = (F.gr m).map (f.restrictScalars B)) (N : Submodule R F.M)
    (hN : N = LinearMap.ker f) : Nonempty (GIso G (F.quo N)) := by
  subst hN
  refine ⟨⟨(f.quotKerEquivOfSurjective hf).symm, fun m => ?_⟩⟩
  rw [hg m, ← Submodule.map_comp]
  show _ = (F.gr m).map ((LinearMap.ker f).mkQ.restrictScalars B)
  congr 1
  ext x
  exact (f.quotKerEquivOfSurjective hf).symm_apply_eq.2 rfl

theorem UpperTheory.V.Alg.M.qi_holds :
    ∀ (k : ℕ) (B R : Type) [CommRing B] [CommRing R] [Algebra B R] (𝒜 : Deg k → Submodule B R) (J : Ideal R)
      (us : List (Deg k × R)), Nonempty (GIso (((GMod.self 𝒜).quo J).quots us) ((GMod.self 𝒜).quo (J ⊔ secs us))) := by
  intro k B R _ _ _ 𝒜 J us
  let q : (GMod.self 𝒜).M →ₗ[R] ((GMod.self 𝒜).quo J).M := Submodule.mkQ J
  refine UpperTheory.V.Alg.M.graded_quotient_isomorphism (GMod.self 𝒜) _ ((GMod.quotsMk us ((GMod.self 𝒜).quo J)).comp q)
    ((GMod.quotsMk_surjective us _).comp (Submodule.mkQ_surjective J)) (fun m => ?_) _ ?_
  · rw [GMod.quots_gr]
    exact (Submodule.map_comp (q.restrictScalars B)
      ((GMod.quotsMk us ((GMod.self 𝒜).quo J)).restrictScalars B) ((GMod.self 𝒜).gr m)).symm
  · rw [LinearMap.ker_comp, GMod.ker_quotsMk]
    have h2 : (secs us • (⊤ : Submodule R (R ⧸ J))) =
        (secs us • (⊤ : Submodule R R)).map (Submodule.mkQ J) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    have h3 : J ⊔ secs us = (secs us • (⊤ : Submodule R (R ⧸ J))).comap (Submodule.mkQ J) := by
      rw [h2, Submodule.comap_map_mkQ, smul_eq_mul, Ideal.mul_top]
    exact h3
