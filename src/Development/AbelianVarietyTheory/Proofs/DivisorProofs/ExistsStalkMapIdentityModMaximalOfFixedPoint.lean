module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.FixStalk

theorem fixes_stalk : ∀ (X : Scheme.{0}) [IsIntegral X] (b : X ≅ X) (x : X), X.fromSpecResidueField x ≫ b.hom = X.fromSpecResidueField x → ∃ st : X.presheaf.stalk x →+* X.presheaf.stalk x, (show Sp (X.presheaf.stalk x) ⟶ X from X.fromSpecStalk x) ≫ b.hom = spMap st ≫ X.fromSpecStalk x ∧ (∀ a, IsLocalRing.residue (X.presheaf.stalk x) (st a) = IsLocalRing.residue (X.presheaf.stalk x) a) ∧ ∀ a, GlobalTheory.functionFieldMap b.hom (algebraMap (X.presheaf.stalk x) X.functionField a) = algebraMap (X.presheaf.stalk x) X.functionField (st a) := by
  intro X _ b x hb
  have hx : b.hom x = x := by
    obtain ⟨p⟩ : Nonempty ↥(Spec (X.residueField x)) := ⟨IsLocalRing.closedPoint _⟩
    have h2 := Scheme.fromSpecResidueField_apply x p
    have h3 : b.hom (X.fromSpecResidueField x p) = X.fromSpecResidueField x p := by
      rw [← Scheme.Hom.comp_apply, hb]
    rwa [h2] at h3
  have hs : b.hom x ⤳ x := by rw [hx]
  have hs' : x ⤳ b.hom x := by rw [hx]
  let st : X.presheaf.stalk x ⟶ X.presheaf.stalk x :=
    X.presheaf.stalkSpecializes hs ≫ b.hom.stalkMap x
  have h0 : X.fromSpecStalk x ≫ b.hom = Spec.map st ≫ X.fromSpecStalk x := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have h1 : (show Sp (X.presheaf.stalk x) ⟶ X from X.fromSpecStalk x) ≫ b.hom =
      spMap st.hom ≫ X.fromSpecStalk x := by
    simpa only [spMap, CommRingCat.ofHom_hom] using h0
  haveI : IsIso (X.presheaf.stalkSpecializes hs) :=
    ⟨⟨X.presheaf.stalkSpecializes hs', by simp, by simp⟩⟩
  haveI : IsLocalHom st.hom := by
    show IsLocalHom (X.presheaf.stalkSpecializes hs ≫ b.hom.stalkMap x).hom
    rw [CommRingCat.hom_comp]
    infer_instance
  haveI : IsLocalHom (X.residue x).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue _))
  haveI : IsLocalHom (st ≫ X.residue x).hom := by
    rw [CommRingCat.hom_comp]
    infer_instance
  refine ⟨st.hom, h1, ?_, ?_⟩
  · have e : Spec.map (X.residue x) ≫ X.fromSpecStalk x =
        Spec.map (st ≫ X.residue x) ≫ X.fromSpecStalk x := by
      rw [Spec.map_comp, Category.assoc, ← h0, ← Category.assoc]
      exact hb.symm
    have e2 := (SpecToEquivOfLocalRing X (X.residueField x)).symm.injective
      (a₁ := ⟨x, ⟨X.residue x, inferInstance⟩⟩) (a₂ := ⟨x, ⟨st ≫ X.residue x, inferInstance⟩⟩) e
    obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp] at e3
    intro a
    exact (congr($e3 a)).symm
  · intro a
    have e4 : algebraMap (X.presheaf.stalk x) X.functionField a =
        algebraMap (X.presheaf.stalk (b.hom x)) X.functionField (X.presheaf.stalkSpecializes hs a) := by
      simp only [RingHom.algebraMap_toAlgebra]
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
    rw [e4, GlobalTheory.functionFieldMap_algebraMap]
    rfl

end GlobalTheory.FixStalk
