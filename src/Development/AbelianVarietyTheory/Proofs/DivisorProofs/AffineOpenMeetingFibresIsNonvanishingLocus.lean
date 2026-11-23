module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierLocusOverDenseOpenBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPreimageSupOfStalkKrullDimLeOneFlatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusExtendFromBigOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPicardClassExtendsAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineLocus

theorem isLocus_of_isAffineOpen_of_meets_fibres : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ c : Pic A.left, IsLocus c V := by
  intro R _ _ _ _ A _ hA V hV hfib
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hnS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.IsNormalScheme.pred (Sp R)
  obtain ⟨U, c, hU, hc⟩ := GlobalTheory.T.exists_cartier_locus_over_dense_open_base R A hA V hV hfib
  have hVW : V ≤ A.hom ⁻¹ᵁ U ⊔ V := le_sup_right
  have h0 : GlobalTheory.CechPic.pull (A.left.homOfLE hVW) c = 0 := by
    refine GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.2 _ _ _ c _ hc fun y => ?_
    show (A.left.homOfLE hVW ≫ (A.hom ⁻¹ᵁ U ⊔ V).ι) y ∈ V
    rw [Scheme.homOfLE_ι]
    exact y.2
  obtain ⟨c', hc'⟩ := GlobalTheory.T.two_smul_picardClass_extends_abelianScheme (Sp R) hnS A hA U V hU hfib c h0
  have h2 : IsLocus (GlobalTheory.CechPic.pull (A.hom ⁻¹ᵁ U ⊔ V).ι c') ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V) := by
    rw [hc', two_nsmul, ← inf_idem ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V)]
    exact hc.add hc
  have : Flat A.hom := inferInstance
  have : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have hbig := GlobalTheory.T.mem_preimage_sup_of_stalk_krullDim_le_one_flat A.left (Sp R) A.hom V U hfib hU
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : A.left.IsSeparated := by
    have : IsSeparated (terminal.from A.left) := by rw [← terminal.comp_from A.hom]; infer_instance
    exact ⟨this⟩
  have : GlobalTheory.IsNormalScheme A.left := GlobalTheory.isNormalScheme_of_smooth A.hom
  exact ⟨c', GlobalTheory.T.nonvanishingLocus_extend_from_big_open A.left (GlobalTheory.IsNormalScheme.pred _) V _ hV hVW hbig c' h2⟩

end GlobalTheory.AffineLocus
