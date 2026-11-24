module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

namespace GlobalTheory.CompanionTheory.Ar.Coords

theorem dense_point_lift (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X)
    [IsDominant ξ] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)]
    (hd : Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X')) (hU : ⊤ ≤ ξ ⁻¹ᵁ U) :
    ∃ ζ : Sp Ω ⟶ X', ζ ≫ f = ξ ∧ IsDominant ζ ∧ ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  have hr : Set.range ξ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hU (show x ∈ (⊤ : (Sp Ω).Opens) from trivial)

  let ζ₀ : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift U.ι ξ hr ≫ inv (f ∣_ U)
  have hζ₀ : ζ₀ ≫ (f ∣_ U ≫ U.ι) = ξ := by
    simp only [ζ₀, Category.assoc, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]
  have hT : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := morphismRestrict_ι f U
  have hfac : (ζ₀ ≫ (f ⁻¹ᵁ U).ι) ≫ f = ξ := by
    rw [Category.assoc, ← hT, hζ₀]
  refine ⟨ζ₀ ≫ (f ⁻¹ᵁ U).ι, hfac, ⟨?_⟩, ?_⟩
  ·
    rw [DenseRange, dense_iff_inter_open]
    intro W hW hne
    obtain ⟨v, hvW, hvU⟩ := hd.inter_open_nonempty W hW hne
    let T : (f ⁻¹ᵁ U).toScheme ⟶ X := f ∣_ U ≫ U.ι
    have hTo : IsOpenImmersion T := inferInstance
    let W' : Set (f ⁻¹ᵁ U).toScheme := (f ⁻¹ᵁ U).ι ⁻¹' W
    have hW' : IsOpen W' := hW.preimage (f ⁻¹ᵁ U).ι.continuous
    have himg : IsOpen (T '' W') := T.isOpenEmbedding.isOpenMap _ hW'
    have hne' : (T '' W').Nonempty :=
      ⟨T ⟨v, hvU⟩, ⟨v, hvU⟩, by
        change (f ⁻¹ᵁ U).ι ⟨v, hvU⟩ ∈ W
        exact hvW, rfl⟩
    obtain ⟨y, hyT, p, rfl⟩ := (ξ.denseRange).inter_open_nonempty _ himg hne'
    obtain ⟨w, hwW, hw⟩ := hyT
    have hp : T (ζ₀ p) = ξ p := by
      rw [← hζ₀]; simp [T]
    have hwp : w = ζ₀ p := T.isOpenEmbedding.injective (hw.trans hp.symm)
    refine ⟨(ζ₀ ≫ (f ⁻¹ᵁ U).ι) p, ?_, p, rfl⟩
    subst hwp
    simpa [W'] using hwW
  · intro x _
    have hx : ξ x ∈ U := hU (show x ∈ (⊤ : (Sp Ω).Opens) from trivial)
    rw [← hfac] at hx
    exact hx

end GlobalTheory.CompanionTheory.Ar.Coords
