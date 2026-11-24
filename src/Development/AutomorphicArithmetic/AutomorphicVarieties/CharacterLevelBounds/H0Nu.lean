module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.RestrictScalarsTwistInvOver
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.h0Nu :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e : ℕ) (ψ : G k Ω →* Oˣ) (U : Subgroup (G k Ω)),
          (∀ U' : Subgroup (G k Ω), U' ≤ U → h0 l e ψ U ≤ h0 l e ψ U') ∧
          (U ≤ ψ.ker → h0 l e ψ U ≤ KStar.TotallyRealRoots.nu l (U.map (cycZ k Ω l)) e * eO l O) := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ e ψ U
  refine ⟨fun U' h => ?_, fun h => ?_⟩
  · have hle : H0U (rho l e ψ) U ≤ H0U (rho l e ψ) U' := fun m hm =>
      (mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm ⟨g.1, h g.2⟩
    exact Module.length_le_of_injective _ (Submodule.inclusion_injective hle)
  · obtain ⟨-, -, -, -, -, h0', -, hval, -⟩ := dvrFacts l O
    by_cases ht : KStar.TotallyRealRoots.nu l (U.map (cycZ k Ω l)) e = ⊤
    · rw [ht, ENat.top_mul h0']
      exact le_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ht
    have hle : H0U (rho l e ψ) U ≤
        LinearMap.ker (((l : O) ^ n) • (LinearMap.id : QO l O →ₗ[O] QO l O)) := by
      intro m hm
      have h1 : m ∈ KStar.TotallyRealRoots.twistInvOver l O (QO l O) (U.map (cycZ k Ω l)) e := by
        rw [KStar.TotallyRealRoots.mem_twistInvOver]
        rintro u ⟨g, hg, rfl⟩
        have h2 : rho l e ψ g⁻¹ m = m := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm ⟨g⁻¹, U.inv_mem hg⟩
        have h3 : ψ g = 1 := h hg
        rw [rho_eq, scalRep_apply, MonoidHom.inv_apply, map_inv, inv_inv, Psi, MonoidHom.mul_apply, h3, mul_one,
          zpow_natCast, MonoidHom.pow_apply, Units.val_pow_eq_pow_val] at h2
        exact h2
      rw [KStar.TotallyRealRoots.twistInvOver_eq_torsionBy _ hn.symm, Submodule.mem_torsionBy_iff] at h1
      exact h1
    refine (Module.length_le_of_injective _ (Submodule.inclusion_injective hle)).trans ?_
    rw [(qoFacts l O).2.2.2, IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, ← hn, hval]
