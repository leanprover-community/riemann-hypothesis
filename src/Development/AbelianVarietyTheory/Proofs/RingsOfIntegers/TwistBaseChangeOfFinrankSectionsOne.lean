module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomologyStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsMulEqSmulOneOfMulVecInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankSectionsLineBundlePowEqPow
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesDescent
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmpleStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TwistedPowTranslate
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SectionsPowerTwistBasisStableBaseChangeStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem twistBaseChange_of_finrank_sections_one :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))),
      Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
        (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1) → DVR.TwistBaseChangeStatement := by
  intro h1
  obtain ⟨hGF, -, hBC, -, -⟩ := GlobalTheory.T.abelianScheme_laws_without_cohomology
  obtain ⟨hcube, -, hgrow⟩ := GlobalTheory.T.cube_theorem_and_sections_finite_growth_abelianVariety
  obtain ⟨-, -, -, -, -, -, -, -, hmulq, hrel⟩ := GlobalTheory.T.abelianSchemeLaws_of_cubeBundleGenerator hcube
  have hproj := GlobalTheory.AbLaw.polAV_veryAmpleBy hBC
  have hmul := (GlobalTheory.MulPull.mulPull_of_cube_of_symm hcube (GlobalTheory.exists_gen_negLB hGF)).1
  have hvan := GlobalTheory.AbLaw.PowVanish.first_cohomology_vanishes_powers hproj GlobalTheory.T.serre_vanishing_very_ample.1 GlobalTheory.AbLaw.h1Zero_of_isIso hmul hmulq
    (GlobalTheory.torsion_invariant_descends hmulq)
  have h0 := GlobalTheory.FinrankGrowthBounds.finrank_sections_lineBundlePow_eq_pow
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected h1 hrel hgrow hmulq
  exact GlobalTheory.T.sections_powerTwist_basis_stable_baseChange GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj hproj hvan GlobalTheory.AbLaw.h1Zero_of_isIso
    GlobalTheory.exists_matrix_basis_ker_of_exact_at_point hBC ((GlobalTheory.secM_invariant_eq_bot_or_univ_at_geometric_point hBC).1 h0)
    (GlobalTheory.twisted_pow_translate (GlobalTheory.AbSquare.square_of_cube hcube).1 hmulq)

end GlobalTheory
