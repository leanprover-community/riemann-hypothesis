module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Poinc

theorem resG_f_mem_comap_map_ideal (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω)
    (π : M.Z ⟶ M₁.Z) (hπ : M₁.IsHom M (AlgHom.id o Ω) π) (D : EffCartierData M.Z) (V : M₁.Z.affineOpens)
    (g : Γ(M₁.Z, V.1)) (x : M.Z) (i : D.ι) (hxV : π x ∈ V.1) (hxi : x ∈ D.U i)
    (hg : g ∈ (D.idealSheaf.map π).ideal V) (hG : valF M₁.pt V.1 g ≠ 0)
    (hO : valF M.pt (D.U i) (D.f i) / valF M₁.pt V.1 g ∈ M.O x) :
    ∃ (W : M.Z.affineOpens) (h : W.1 ≤ D.U i), x ∈ W.1 ∧
      resG M.Z h (D.f i) ∈ ((D.idealSheaf.map π).comap π).ideal W := by
  obtain ⟨U, s, hUa, hxU, hUle, hs⟩ :=
    RatModel.exists_affine_of_mem_O hO (V := D.U i ⊓ π ⁻¹ᵁ V.1) ⟨hxi, hxV⟩
  have hUi : U ≤ D.U i := hUle.trans inf_le_left
  have hUV : U ≤ π ⁻¹ᵁ V.1 := hUle.trans inf_le_right
  have hUne : (U : Set M.Z).Nonempty := ⟨x, hxU⟩
  have hmem := (GlobalTheory.Cartier.comap_le_iff (D.idealSheaf.map π) π ((D.idealSheaf.map π).comap π)).1 le_rfl
    V g hg ⟨U, hUa⟩ hUV
  refine ⟨⟨U, hUa⟩, hUi, hxU, ?_⟩
  have key : resG M.Z hUi (D.f i) = s * resG M.Z hUV ((π.app V.1).hom g) := by
    apply M.valF_injective hUne
    rw [← M.res_apply U hUne (s * _), map_mul, M.res_apply, M.res_apply, M.valF_resG hUi hUne,
      M.valF_resG hUV hUne, hs]
    have h2 := hπ.valF_app ⟨π x, hxV⟩ g
    simp only [AlgHom.coe_id, id_eq] at h2
    rw [h2, div_mul_cancel₀ _ hG]
  rw [key]
  exact Ideal.mul_mem_left _ _ hmem

end GlobalTheory.Poinc
