module

public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianVarietyLineBundleSectionsFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankTotalDegreeImageGrowth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmpleStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.CubeAssembly

theorem cube_gen :
    ∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen :=
  GlobalTheory.AbLaw.exists_gen_theta
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    GlobalTheory.laws_without_cohomology.1 GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj (GlobalTheory.AbLaw.polAV_veryAmpleBy GlobalTheory.laws_without_cohomology.2.2.1)
    GlobalTheory.AbLaw.isProjBy_tensor GlobalTheory.TrivLocus.isClosed_trivLocus
    (GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre GlobalTheory.laws_without_cohomology.1 GlobalTheory.AbLaw.Seesaw.seesaw
      (GlobalTheory.SmallExtLift.exists_gen_of_small_extension GlobalTheory.laws_without_cohomology.1 GlobalTheory.KuennethOne.kuenneth_injective))

theorem sections_finite :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0 :=
  GlobalTheory.T.abelianVariety_lineBundle_sections_finite GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj (GlobalTheory.AbLaw.polAV_veryAmpleBy GlobalTheory.laws_without_cohomology.2.2.1)

theorem sections_growth :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), (∀ j : ℕ, Module.Finite Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K))))) ∧ ∃ N c C : ℕ, 1 ≤ N ∧ 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ P.g ≤ c * Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ∧ Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ≤ C * t ^ P.g :=
  GlobalTheory.SecGrowth.secM_finite_and_growth
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    (GlobalTheory.AbLaw.polAV_veryAmpleBy GlobalTheory.laws_without_cohomology.2.2.1) sections_finite GlobalTheory.T.serre_vanishing_very_ample.2
    GlobalTheory.finrank_totalDegree_image_growth GlobalTheory.trdeg_eq_of_smoothOfRelativeDimension

theorem cube_and_sections :
    (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), (∀ j : ℕ, Module.Finite Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K))))) ∧ ∃ N c C : ℕ, 1 ≤ N ∧ 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ P.g ≤ c * Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ∧ Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ≤ C * t ^ P.g) :=
  ⟨cube_gen, sections_finite, sections_growth⟩

end GlobalTheory.AbLaw.CubeAssembly
