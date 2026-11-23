module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory

theorem lift_of_stalk_generic_flat : ∀ {X' W : Scheme.{0}} [IsIntegral X'] (h : W ⟶ X') [Flat h] (q : W)
    [IsDomain (W.presheaf.stalk q)] {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X') [IsOpenImmersion ℓ]
    (Ω : Type) [Field Ω] (y : Sp Ω ⟶ Spec (W.presheaf.stalk q)) (hy : ∀ x, (y x).asIdeal = ⊥), ∃ z : Sp Ω ⟶ V, y ≫ W.fromSpecStalk q ≫ h = z ≫ ℓ := by
  intro X' W _ h _ q _ V _ ℓ _ Ω _ y hy
  have hinj : Function.Injective (h.stalkMap q).hom := by
    letI := (h.stalkMap q).hom.toAlgebra
    haveI : Module.Flat (X'.presheaf.stalk (h q)) (W.presheaf.stalk q) := Flat.stalkMap h q
    haveI : IsLocalHom (algebraMap (X'.presheaf.stalk (h q)) (W.presheaf.stalk q)) :=
      (inferInstance : IsLocalHom (h.stalkMap q).hom)
    haveI : Module.FaithfullyFlat (X'.presheaf.stalk (h q)) (W.presheaf.stalk q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective _ _
  have hrange : Set.range (y ≫ W.fromSpecStalk q ≫ h) ⊆ Set.range ℓ := by
    rintro _ ⟨x, rfl⟩
    have key : (y ≫ W.fromSpecStalk q ≫ h) x =
        X'.fromSpecStalk (h q) (Spec.map (h.stalkMap q) (y x)) := by
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]; rfl
    rw [key]
    set p : Spec (X'.presheaf.stalk (h q)) := Spec.map (h.stalkMap q) (y x) with hpdef
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap (h.stalkMap q).hom (y x).asIdeal = ⊥
      rw [hy x]
      exact Ideal.comap_bot_of_injective _ hinj
    obtain ⟨s, hs⟩ : genericPoint X' ∈ Set.range (X'.fromSpecStalk (h q)) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X').specializes (Set.mem_univ _)
    have hps : p ⤳ s := (PrimeSpectrum.le_iff_specializes _ _).1 (by
      show p.asIdeal ≤ s.asIdeal
      rw [hp]; exact bot_le)
    have hgen : genericPoint X' ∈ Set.range ℓ :=
      ((genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range).2
        (by simpa using Set.range_nonempty ℓ)
    have := (hps.map (X'.fromSpecStalk (h q)).continuous).mem_open
      ℓ.isOpenEmbedding.isOpen_range (by rw [hs]; exact hgen)
    exact this
  exact ⟨IsOpenImmersion.lift ℓ _ hrange, (IsOpenImmersion.lift_fac _ _ _).symm⟩

end GlobalTheory
