module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LbSpreads
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectOfModels
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpread
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOut
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotient, Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotientStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotient =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotient", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels\npublic import Mathlib.AlgebraicGeometry.Morphisms.Proper\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOut\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LbSpreads\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectOfModels\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpread\npublic import Mathlib.AlgebraicGeometry.Morphisms.Smooth\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOut\npublic import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.PolRigid

open GlobalTheory.CechPic

theorem cls_lam_pull {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : LB B.left} (hL : L.IsLB)
    (x y : B ⟶ B) (h : ((abelian₂ B L).pull (lift x y).left).IsLB) :
    cls _ h = lam (cls L hL) x y := by
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have h₁ : cls _ hlam = lam (cls L hL) (fst B B) (snd B B) := cls_cube_two hL _ _ hlam
  rw [cls_pull hlam, h₁, pull_lam, lift_fst, lift_snd]

theorem lbIso_lam_of_quotient : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [CommRing R₀] [Nontrivial R₀] (π : R →+* R₀), Function.Surjective π → ∀ (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left), P.IsLB → (∃ t : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → ∀ (L : LB B.left) (L₀ : LB B₀.left), L.IsLB → L₀.IsLB → LBIso (L.pull i) L₀ → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → LBIso (abelian₂ B L) P := by
  intro R R₀ _ _ _ _ π hπ B _ _ B₀ _ _ i i₂ hA hpb hsq P hP hP₁ hP₂ L L₀ hL hL₀ e₀ e
  haveI : IsLocalRing R₀ := IsLocalRing.of_surjective' π hπ
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hlam₀ : (abelian₂ B₀ L₀).IsLB := LB.isLB_linComb hL₀ _ _
  have hD : (LB.div (abelian₂ B L) P).IsLB := LB.isLB_div hlam hP
  have hcD : cls _ hD = cls _ hlam - cls P hP := cls_div hlam hP hD

  have triv_of : ∀ {Y : Scheme.{0}} (f : Y ⟶ (G2 B).left), pull f (cls _ hlam) = pull f (cls P hP) →
      GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull f) := fun f hf =>
    (cls_eq_zero_iff (pull_isLB hD f)).1 (by rw [cls_pull hD, hcD, map_sub, hf, sub_self])

  have ax : ∀ (x y : B ⟶ B), (∃ t : (P.pull (lift x y).left).Gen, t.IsGen) → lam (cls L hL) x y = 0 →
      GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (lift x y).left) := fun x y hPxy hl => by
    refine triv_of _ ?_
    rw [← cls_pull hlam _ (pull_isLB hlam _), cls_lam_pull hL x y, hl, ← cls_pull hP _ (pull_isLB hP _)]
    exact ((cls_eq_zero_iff (pull_isLB hP _)).2 hPxy).symm
  have h₁ : GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (lift (𝟙 B) 1).left) := ax _ _ hP₂ (lam_one_right _ _)
  have h₂ : GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (lift 1 (𝟙 B)).left) := ax _ _ hP₁ (lam_one_left _ _)

  have hsq₀ : pull i₂ (cls _ hlam) = pull i₂ (cls P hP) := by
    have a : LBIso (abelian₂ B₀ L₀) ((abelian₂ B L).pull i₂) := GlobalTheory.ZM.SiegPull.lbIso_lam_pull hpb e₀.symm hsq
    rw [← cls_pull hlam _ (pull_isLB hlam _), ← cls_pull hP _ (pull_isLB hP _),
      ← (cls_eq_iff hlam₀ (pull_isLB hlam _)).2 a, (cls_eq_iff hlam₀ (pull_isLB hP _)).2 e]

  let k := ResidueField R₀
  let g₀ : R →+* k := (residue R₀).comp π
  have hpb₂ : IsPullback i₂ (G2 B₀).hom (G2 B).hom (spMap π) :=
    GlobalTheory.SiegelDescent.isPullback_square hpb.1 i₂ hsq
  have h₀ := (IsPullback.of_hasPullback (G2 B₀).hom (spMap (residue R₀))).paste_horiz hpb₂
  have e₁ : spMap (residue R₀) ≫ spMap π = Spec.map (CommRingCat.ofHom g₀) := by
    simp only [spMap, g₀, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [e₁] at h₀
  have ht₀ : GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (pullback.fst (G2 B₀).hom (spMap (residue R₀)) ≫ i₂)) :=
    triv_of _ (by rw [pull_comp, pull_comp, hsq₀])
  have hPf : GlobalTheory.SpreadingModels.PerfAll :=
    _root_.GlobalTheory.CompanionTheory.SpreadingModels.perfAll_of_hasModel (_root_.GlobalTheory.CompanionTheory.CubeModels.hasModel_of_spreads _root_.GlobalTheory.CompanionTheory.NoethApprox.schemeModels _root_.GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads _root_.GlobalTheory.CompanionTheory.SpreadingModels.properSpreads _root_.GlobalTheory.CompanionTheory.LBLimit.lbSpreads)
  haveI := hA.smooth
  haveI := hA.proper
  have sm : Smooth (B ⊗ B).hom := by
    change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  have pr : IsProper (B ⊗ B).hom := by
    change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  obtain ⟨r, hr, hU⟩ := GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre GlobalTheory.globalFns_holds GlobalTheory.AbLaw.Seesaw.seesaw
    (GlobalTheory.SmallExtLift.exists_gen_of_small_extension GlobalTheory.globalFns_holds GlobalTheory.KuennethOne.kuenneth_injective)
    R B hA _ hD (hPf R _ (B ⊗ B).hom sm pr _ hD) h₁ h₂ k g₀ _ _ _ h₀ ht₀

  have hru : IsUnit r := by
    by_contra hnu
    refine hr ?_
    show residue R₀ (π r) = 0
    rw [residue_eq_zero_iff]
    intro hu
    obtain ⟨s, hs⟩ := hu.exists_right_inv
    obtain ⟨t, rfl⟩ := hπ s
    have hk : r * t - 1 ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hs, map_one, sub_self]
    have hm : RingHom.ker π ≤ maximalIdeal R := le_maximalIdeal (RingHom.ker_ne_top π)
    have hunit : IsUnit (r * t) := by
      by_contra h'
      have h1 : r * t ∈ maximalIdeal R := (mem_maximalIdeal _).2 h'
      have h2 : (1 : R) ∈ maximalIdeal R := by
        have := (maximalIdeal R).sub_mem h1 (hm hk)
        simpa using this
      exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)
    exact hnu (isUnit_of_mul_isUnit_left hunit)
  let U := (B ⊗ B).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)
  have hsub : Set.range (𝟙 (B ⊗ B).left) ⊆ Set.range U.ι := by
    rintro x -
    rw [Scheme.Opens.range_ι]
    change r ∉ ((B ⊗ B).hom x).asIdeal
    exact fun hx => ((B ⊗ B).hom x).2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hru)
  have hT := GlobalTheory.AbLaw.CubeOpen.triv_comp (IsOpenImmersion.lift U.ι (𝟙 _) hsub) (IsOpenImmersion.lift_fac _ _ _) hU
  have hz : cls _ hD = 0 := by
    rw [← pull_id (cls _ hD), ← cls_pull hD _ (pull_isLB hD _)]
    exact (cls_eq_zero_iff _).2 hT
  exact (cls_eq_iff hlam hP).1 (sub_eq_zero.1 (hcD ▸ hz))

end GlobalTheory.PolRigid
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotient =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotientStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotientStatement", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotient\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

theorem _root_.GlobalTheory.T.lineBundleIso_mumfordLambda_of_local_quotient : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [CommRing R₀] [Nontrivial R₀] (π : R →+* R₀), Function.Surjective π → ∀ (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left), P.IsLB → (∃ t : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → ∀ (L : LB B.left) (L₀ : LB B₀.left), L.IsLB → L₀.IsLB → LBIso (L.pull i) L₀ → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → LBIso (abelian₂ B L) P := by
  first | exact @GlobalTheory.PolRigid.lbIso_lam_of_quotient
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotientStatement =====
