module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotPelRepOfTwoPoints, Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsPelRepIsPEL, Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotPelRepOfTwoPoints =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotPelRepOfTwoPoints", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp\npublic import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal\npublic import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

namespace DimZero
open Out.Inh GlobalTheory.ZM.Model

def zeroSieg (k : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) : SiegPre 0 k ζ s where
  A := (zeroPolAV S).A
  comm := (zeroPolAV S).isAb.comm
  ab := (zeroPolAV S).isAb
  P := trivLB _
  isLB := trivLB_isLB _
  rig₁ := (exists_gen _ (linComb_triv_g _ _)).imp fun _ h => h.1
  rig₂ := (exists_gen _ (linComb_triv_g _ _)).imp fun _ h => h.1
  symm := lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => toUnit_unique _ _
  lev_tors := fun _ => toUnit_unique _ _
  geom := fun K _ _ x β z _ _ => by
    refine ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
      fun _ _ => ⟨0, toUnit_unique _ _⟩, fun a a' => ?_⟩
    have h1 : unitOn (z ^ (2 * omegaStd a a')) = 1 := by
      have : omegaStd a a' = 0 := by simp [omegaStd]
      rw [this, mul_zero, zpow_zero]
      exact map_one _
    rw [h1]
    exact @weilIs_zero S _ (inferInstanceAs (Unique (PUnit → PUnit))) (linComb_triv_g _ _) _ _ _ _

end DimZero

end GlobalTheory.ZM
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotPelRepOfTwoPoints =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsPelRepIsPEL =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsPelRepIsPEL", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotPelRepOfTwoPoints\npublic import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional\npublic import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf\npublic import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver\nimport Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc\npublic import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul\npublic import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel\npublic import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM.SFamModel
open Out.Inh GlobalTheory.ZM.Model GlobalTheory.ZM.DimZero

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {k : ℕ}

def zeroFam (k : ℕ) (ζ : o)
    (hz : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (c : SiegPre 0 k ζ s'), IsReduced S → IsIso c.A.hom) : SFam 0 k ζ where
  X := Sp o
  s := 𝟙 _
  smooth := inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 _))
  qproj := OnePoint.isQProjOver_id o
  univ := zeroSieg k ζ _
  princ := principal_zeroSieg k ζ _
  rep := fun S s' c hS _ _ => by
    haveI := hz S s' c hS
    exact ⟨s', Category.comp_id _, siegPB_zero c ζ _ s'⟩
  inj := fun _ _ _ _ _ _ _ h _ _ => by simpa using h

def zeroFamLevel {ζ : o} (hζ : IsUnit ζ) (hku : IsUnit (k : o)) (hk : 2 ≤ k) : SFam 0 k ζ :=
  zeroFam k ζ fun _ _ c _ => isIso_of_count GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional hζ hku hk c

end GlobalTheory.ZM.SFamModel
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsPelRepIsPEL =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsPelRepIsPEL\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal\npublic import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral\npublic import Mathlib.RingTheory.AdicCompletion.LocalRing\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents\nimport Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing\nimport Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (powObj powPr powIsLimit)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LowChart

section Pull

variable {S S' : Scheme.{0}} {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}

def siegPull (c : SiegPre h M ζ s) (f : S' ⟶ S) (s' : S' ⟶ Sp B) (hs : f ≫ s = s') : SiegPre h M ζ s' where
  A := (Over.pullback f).obj c.A
  ab :=
    { comm := by have := c.ab.comm; infer_instance
      smooth := by have := c.ab.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := c.ab.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := c.ab.geomConnected
        show GeometricallyConnected (pullback.snd _ _); infer_instance }
  P := c.P.pull (Pdiv.PullbackComparison.pφ₂ f c.A)
  isLB := pull_isLB c.isLB (Pdiv.PullbackComparison.pφ₂ f c.A)
  rig₁ := by
    obtain ⟨t₁, ht₁⟩ := c.rig₁
    exact gen_chartPull (chartPullLinComb c.P _ _ _ _ (Pdiv.PullbackComparison.pφ f c.A)
      (fun _ => Pdiv.PullbackComparison.lift_one_id f c.A)) t₁ ht₁
  rig₂ := by
    obtain ⟨t₂, ht₂⟩ := c.rig₂
    exact gen_chartPull (chartPullLinComb c.P _ _ _ _ (Pdiv.PullbackComparison.pφ f c.A)
      (fun _ => Pdiv.PullbackComparison.lift_id_one f c.A)) t₂ ht₂
  symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
      (chartPullLinComb c.P _ _ _ _ (Pdiv.PullbackComparison.pφ₂ f c.A) (fun _ => Pdiv.PullbackComparison.lift_swap f c.A)) c.symm
  lev := fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback f c.A) (c.lev a)
  lev_add := fun a b => GlobalTheory.SiegelPull.push_injective (Pdiv.PullbackComparison.isGrpPullback f c.A) _ (by
    rw [map_mul, GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', c.lev_add, MonObj.comp_mul])
  lev_tors := fun a => GlobalTheory.SiegelPull.push_injective (Pdiv.PullbackComparison.isGrpPullback f c.A) _ (by
    rw [map_pow, map_one, GlobalTheory.SiegelPull.push_secPull', ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one])
  geom := fun k _ _ x β z hx hz => by
    have pb := Pdiv.PullbackComparison.isGrpPullback f c.A
    obtain ⟨g₁, g₂, g₃⟩ := c.geom k (x ≫ f) β z (by rw [Category.assoc, hs, hx]) hz
    refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
    · rw [← (GlobalTheory.SiegelPull.push_injective pb (Over.mk x)).eq_iff, GlobalTheory.SiegelPull.push_secPull, map_one]
      rfl
    · obtain ⟨a, ha⟩ := g₂ (pushHom pb (Over.mk x) g) (by
        have := congrArg (pushHom pb (Over.mk x)) hg
        rw [map_pow, map_one] at this
        exact this)
      exact ⟨a, GlobalTheory.SiegelPull.push_injective pb _ ((GlobalTheory.SiegelPull.push_secPull pb _ _).trans ha)⟩
    · exact (weilIs_grpPullback_of_comm S S' c.A _ f (Pdiv.PullbackComparison.pφ f c.A) _ _ (pull_isLB c.isLB _)
        (pull_isLB (pull_isLB c.isLB (Pdiv.PullbackComparison.pφ₂ f c.A)) _) pb
        (GlobalTheory.SiegelPull.diag_iso (Pdiv.PullbackComparison.isSquare f c.A) (Pdiv.PullbackComparison.gen_refl _ (pull_isLB c.isLB (Pdiv.PullbackComparison.pφ₂ f c.A))))
        (Over.mk x) M _ _ _ _ _
        (congrArg (fun q => q.left) (GlobalTheory.SiegelPull.push_secPull pb (c.lev a) (Over.mk x)).symm)
        (congrArg (fun q => q.left) (GlobalTheory.SiegelPull.push_secPull pb (c.lev b) (Over.mk x)).symm)).2 (g₃ a b)

theorem siegPB_siegPull (c : SiegPre h M ζ s) (f : S' ⟶ S) (s' : S' ⟶ Sp B) (hs : f ≫ s = s') :
    SiegPB (siegPull c f s' hs) c f :=
  ⟨Pdiv.PullbackComparison.pφ f c.A, Pdiv.PullbackComparison.pφ₂ f c.A, Pdiv.PullbackComparison.isGrpPullback f c.A, Pdiv.PullbackComparison.isSquare f c.A,
    Pdiv.PullbackComparison.gen_refl _ (pull_isLB c.isLB _), fun a => GlobalTheory.SiegelPull.secPull_left (Pdiv.PullbackComparison.isGrpPullback f c.A) _⟩

theorem principal_siegPull (c : SiegPre h M ζ s) (f : S' ⟶ S) (s' : S' ⟶ Sp B) (hs : f ≫ s = s')
    (hc : c.Principal) : (siegPull c f s' hs).Principal :=
  (GlobalTheory.siegPre_pullback h M B ζ S S' s s' f c hs).2 _ (siegPB_siegPull c f s' hs) hc

end Pull

end GlobalTheory.LowChart

namespace GlobalTheory.LowChart

section Pow

variable {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : ZM.SFam h n ζ)

abbrev powA (r : ℕ) : Over F.X := powObj F.univ.A r

def toO (r : ℕ) : (powA F r).left ⟶ Sp o := (powA F r).hom ≫ F.s

abbrev coord {r : ℕ} (i : Fin r) : powA F r ⟶ F.univ.A := powPr F.univ.A i

variable {F}

def lift {T : Scheme.{0}} (u : T ⟶ F.X) {r : ℕ} (p : Fin r → (T ⟶ F.univ.A.left))
    (hp : ∀ i, p i ≫ F.univ.A.hom = u) : T ⟶ (powA F r).left :=
  ((powIsLimit F.univ.A r).lift (Fan.mk (Over.mk u) fun i => Over.homMk (p i) (hp i))).left

variable (F)

abbrev siegAt {T : Scheme.{0}} {r : ℕ} (f : T ⟶ (powA F r).left) (s' : T ⟶ Sp o) (hs : f ≫ toO F r = s') :
    SiegPre h n ζ s' :=
  siegPull F.univ (f ≫ (powA F r).hom) s' (by rw [Category.assoc]; exact hs)

def ptAt {T : Scheme.{0}} {r : ℕ} (f : T ⟶ (powA F r).left) (s' : T ⟶ Sp o) (hs : f ≫ toO F r = s') (i : Fin r) :
    𝟙_ (Over T) ⟶ (siegAt F f s' hs).A :=
  Over.homMk (pullback.lift (f ≫ (coord F i).left) (𝟙 T) (by
      rw [Category.assoc, Over.w (coord F i)]; exact (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)

def cAt {T : Scheme.{0}} {r : ℕ} (f : T ⟶ (powA F r).left) (s' : T ⟶ Sp o) (hs : f ≫ toO F r = s')
    (a : Fin r → ℤ) : 𝟙_ (Over T) ⟶ (siegAt F f s' hs).A :=
  ∏ i, ptAt F f s' hs i ^ a i

end Pow

end GlobalTheory.LowChart

namespace GlobalTheory.LowChart

section Base

variable {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : ZM.SFam h n ζ) {r : ℕ} (y : (powA F r).left)

instance smooth_toO : Smooth (toO F r) := by
  have := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (h * (h + 1) / 2) F.s
  have := F.univ.ab.smooth
  have := GlobalTheory.smooth_powObj_hom F.univ.A r
  unfold toO
  infer_instance

instance isLocallyNoetherian_powA [IsNoetherianRing o] : IsLocallyNoetherian (powA F r).left :=
  LocallyOfFiniteType.isLocallyNoetherian (toO F r)

variable [IsNoetherianRing o]

abbrev W : Type :=
  AdicCompletion (maximalIdeal ((powA F r).left.presheaf.stalk y)) ((powA F r).left.presheaf.stalk y)

def toPow : Sp (W F y) ⟶ (powA F r).left := GlobalTheory.fromSpecCompletedStalk _ y

def base : o →+* W F y := (Spec.preimage (toPow F y ≫ toO F r)).hom

abbrev sieg : SiegPre h n ζ (spMap (base F y)) := siegAt F (toPow F y) _ (spMap_base F y).symm

end Base

end GlobalTheory.LowChart

namespace GlobalTheory.LowChart

section Zero

open SiegelTor

variable (n : ℕ) (hn : 3 ≤ n)

theorem isUnit_zetaAway (n : ℕ) (hn : 3 ≤ n) : IsUnit (zetaAway n) := by
  rw [← cycBase_ζ (show n ≠ 0 by omega)]
  exact (cycBase (show n ≠ 0 by omega)).ζ.isUnit

def zeroFam : ZM.SFam 0 n (zetaAway n) :=
  ZM.SFamModel.zeroFamLevel (isUnit_zetaAway n hn) (isUnit_natCast (show n ≠ 0 by omega)) (by omega)

instance : IsRegularRing (cycAway n) := by
  have := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  infer_instance

end Zero

end GlobalTheory.LowChart

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower =====
