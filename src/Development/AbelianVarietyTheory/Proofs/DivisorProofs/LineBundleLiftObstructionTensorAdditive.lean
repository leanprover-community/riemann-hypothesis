module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundleFrameOnBasisLineBundleCechTensorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionRefineFinerBasisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigOneAddMul
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
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isObL_tens : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), IsObL S α L c → IsObL S α L' c' → IsObL S α (tens L L') (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L L' c c' hL hL'
  obtain ⟨C, _, _, G, hG, hLG⟩ := hL
  obtain ⟨C', _, _, G', hG', hLG'⟩ := hL'
  obtain ⟨D, _, _, K, H, H', ⟨θ⟩, ⟨θ'⟩, hK⟩ := GlobalTheory.LBObs.common_refinement X₀ C C' G G' hG hG'
  have h₁ := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α X₀ s₀ S L c C D G K H θ hLG
  have h₂ := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α X₀ s₀ S L' c' C' D G' K H' θ' hLG'
  obtain ⟨u, hu, hU⟩ := h₁
  obtain ⟨u', hu', hU'⟩ := h₂
  refine ⟨D, inferInstance, inferInstance, K, hK, fun T T' a ↦ u T T' a * u' T T' a,
    GlobalTheory.T.isLineBundleFrameOnBasis_lineBundleCechTensor X₀ D (opOf K) (opOf_le K) L L' u u' hu hu', ?_⟩
  rw [map_add (f := _)]
  exact GlobalTheory.LBObs.isObU_mul R R₀ I hI π hπ hk R₁ α D (K ⋙ OAff s₀) ((ofSys S).restrict K) u u' _ _ hU hU'

end GlobalTheory.LBObs
