module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Mathlib.RingTheory.Trace.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensorStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIntegralOfLocalPresentationPowStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTorsionPointFrobeniusLocalStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLocalPresentationSmoothGroupStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_algHom_localization_augmentation (O : Type) [CommRing O] [IsLocalRing O]
    (H : Type) [CommRing H] [Algebra O H] (ε : H →ₐ[O] O) :
    ∃ εT : Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε) →ₐ[O] O,
      ∀ h, εT (algebraMap H _ h) = ε h := by

  have hunit : ∀ s : ((IsLocalRing.maximalIdeal O).comap ε).primeCompl, IsUnit (ε s) := by
    intro s
    by_contra hs
    apply s.2
    show ε s ∈ IsLocalRing.maximalIdeal O
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hs
  refine ⟨IsLocalization.liftAlgHom (M := ((IsLocalRing.maximalIdeal O).comap ε).primeCompl)
    (S := Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) hunit, fun h => ?_⟩
  rw [IsLocalization.liftAlgHom_apply]
  exact IsLocalization.lift_eq hunit h

theorem pow_dvd_trace_torsion :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G) (g : ℕ), SmoothOfRelativeDimension g G.hom → y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ h : H, (n : O) ^ g ∣ Algebra.trace O H h := by
  intro O _ _ G _ _ n H _ _ _ _ y g hsm hy huniv h

  obtain ⟨ε, hε, -⟩ := huniv O 1 (one_pow n)
  obtain ⟨εT, hεT⟩ := exists_algHom_localization_augmentation O H ε

  obtain ⟨S, _, _, π, x, a, ρ, hπ, hker, hkerε, ha, hρ, hρm⟩ :=
    GlobalTheory.T.torsion_local_presentation_smooth_group O G n H y g hsm hy huniv ε hε
      (Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) εT hεT

  obtain ⟨l, hl, hdvd, hlm⟩ :=
    GlobalTheory.T.exists_integral_of_local_presentation_pow O H ε g n (Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) εT hεT
      S π x a ρ hπ hker hkerε ha hρ hρm

  obtain ⟨Θ, hΘ⟩ := GlobalTheory.T.exists_diagonal_element_lmul_eq_nonzero_geometric_points O G n H y hy huniv ε l (ε l) hε hl rfl hlm
  exact dvd_trans hdvd (GlobalTheory.T.dvd_trace_of_tensor_lmul_eq O H Θ (ε l) hΘ h)

end GlobalTheory
