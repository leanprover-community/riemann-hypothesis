module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSabExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNonzeroLocusEqOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SS.AbAmple

open GlobalTheory.CechPic GlobalTheory.TripleExt

theorem cubeCls_eq_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (c : Pic A.left) : cubeCls (x3 A) c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have h := GlobalTheory.CubeTop.cubeTheorem S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have h₀ := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 h
  rw [cls_linComb hL, Fin.sum_univ_eight] at h₀
  have e : x3 A = ![x3 A 0, x3 A 1, x3 A 2] := by
    funext i; fin_cases i <;> rfl
  rw [e, GlobalTheory.SS.AmpCub.cubeCls_three]
  rw [← h₀]
  simp
  abel

end GlobalTheory.SS.AbAmple

namespace GlobalTheory.SS

open GlobalTheory.CechPic AbAmple

theorem exists_ampleCub_of_isAbelianScheme :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B →
      ∃ L : LB B.left, GlobalTheory.SS.AmpleCub B L := by
  intro k _ _ B _ hB
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom := geometricallyIntegral_of_smooth _
  have : IsIntegral B.left :=
    GeometricallyIntegral.geometrically_isIntegral (f := B.hom) (𝟙 _) _ _ (IsPullback.id_horiz B.hom)
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
  have hst : ∀ x : B.left, UniqueFactorizationMonoid (B.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth k B.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  obtain ⟨y⟩ : Nonempty B.left := inferInstance
  obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  obtain ⟨L, s, hL, hs⟩ := exists_nonzeroLocus_eq_of_isAffineOpen B.left hst W hW ⟨y, hy⟩
  exact AmpCub.exists_ampleCub (cubeCls_eq_zero B hB (cls L hL)) ⟨L, hL, s, rfl, hs⟩ hW ⟨y, hy⟩

end GlobalTheory.SS
