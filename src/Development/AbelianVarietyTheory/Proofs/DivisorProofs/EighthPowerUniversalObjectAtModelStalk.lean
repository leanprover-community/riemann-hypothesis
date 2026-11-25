module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsMonHomOfComm
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowExt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.QuasiCompactGeomConnectedPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementaryMatrixEndomorphismGroupPullbackTranspo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementaryMatrixEndomorphismGroupPullbackTranspoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivisorOfForallCompleteDvrPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEighthPowerGroupPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionExtendsFromGenericFibreSemiAb
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfIsPowGrp, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGeneric, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGenericStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniversalObjectAtModelStalk

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfIsPowGrp =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfIsPowGrp", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsMonHomOfComm\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowExt\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.QuasiCompactGeomConnectedPow\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfIsPowGrp =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGeneric =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGeneric", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp\npublic import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion\npublic import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfIsPowGrp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff\nimport Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGeneric =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGenericStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGenericStatement", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGeneric\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff\nimport Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_eighth_power_projections_extend_from_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G C : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj C] [IsCommMonObj C], IsSemiAbelian G → IsAbelianScheme C → ∀ pr' : Fin 8 → ((Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj C), (∀ a, IsMonHom (pr' a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ (Over.pullback (jK R)).obj C)), ∃! x : T' ⟶ (Over.pullback (jK R)).obj G, ∀ a, x ≫ pr' a = y a) → ∃ prO : Fin 8 → (G ⟶ C), (∀ a, IsMonHom (prO a)) ∧ (∀ a, (Over.pullback (jK R)).map (prO a) = pr' a) ∧ ∀ (T' : Over (Sp R)) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ G, ∀ a, x ≫ prO a = y a := by
  first | exact @GlobalTheory.PowExtend.exists_pow_projections
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGenericStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniversalObjectAtModelStalk =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniversalObjectAtModelStalk", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff\nimport Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal\nimport Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms\nimport Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullbackStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementaryMatrixEndomorphismGroupPullbackTranspo\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementaryMatrixEndomorphismGroupPullbackTranspoStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGenericStatement\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivisorOfForallCompleteDvrPoints\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEighthPowerGroupPullbackStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionExtendsFromGenericFibreSemiAb\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open MonObj

noncomputable section

namespace GlobalTheory.Poinc.Eq8.StalkPow

theorem lbIso_of_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ N N' : LB G.left, N.IsLB → N'.IsLB → LBIso (N.pull (pullback.fst G.hom (jK R))) (N'.pull (pullback.fst G.hom (jK R))) → LBIso N N' :=
  fun _ _ _ _ _ _ G _ hG _ _ hN hN' h => GlobalTheory.GenericDec.lbIso_of_generic G hG hN hN' h

theorem eighth_power_at_stalk : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ z : V.toScheme, ∃ (cO : SiegPre g n ζ ((V.toScheme.fromSpecStalk z ≫ v) ≫ F.s)) (prO : Fin 8 → ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G ⟶ cO.A)), SiegPB cO F.univ (V.toScheme.fromSpecStalk z ≫ v) ∧ (∀ a, IsMonHom (prO a)) ∧ (∀ (T' : Over (Spec (V.toScheme.presheaf.stalk z))) (y : Fin 8 → (T' ⟶ cO.A)), ∃! x : T' ⟶ (Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G, ∀ a, x ≫ prO a = y a) ∧ LBIso (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (V.toScheme.fromSpecStalk z ≫ V.ι))) (LB.LinComb cO.P (K := Fin 8 × Fin 8) (fun ab => (lift (prO ab.1) (prO ab.2)).left) (fun ab => W ab.1 ab.2)) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G), MatOn FinalForm pr a b f → MatEnd prO a b ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).map f) := by
  intro g n o _ ζ F W o' Ω _ _ _ _ S ρ u c pr hS M U₀ EE FinalForm hO V v hv z
  obtain ⟨hpb, hmon, huniv, hLc⟩ := hS
  obtain ⟨hdom, hnoeth, hic⟩ := stalk_isDomain_isNoetherian_isIntegrallyClosed o' Ω M hO.normal V z
  haveI := hdom; haveI := hnoeth; haveI := hic
  obtain ⟨emb, hemb⟩ := exists_generic_stalk o' Ω M V z

  have hVne : (V : Set M.Z).Nonempty := ⟨z.1, z.2⟩
  have rU : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff M.pt U₀).1 (M.top_le_preimage_pt hO.ne)
  have rV : Set.range M.pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff M.pt V).1 (M.top_le_preimage_pt hVne)
  set x₀ := IsOpenImmersion.lift U₀.ι M.pt rU with hx₀def
  set xV := IsOpenImmersion.lift V.ι M.pt rV with hxVdef
  have hx₀ : x₀ ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxV : xV ≫ V.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hx₀u : x₀ ≫ FinalForm.u₀ = spMap S.R.val.toRingHom := FinalForm.u₀_gen x₀ hx₀
  have hxVv : xV ≫ v = spMap S.R.val.toRingHom ≫ u := hv xV hxV
  have hjξ : jK (V.toScheme.presheaf.stalk z) ≫ V.toScheme.fromSpecStalk z = spMap emb ≫ xV := by
    rw [← cancel_mono V.ι, Category.assoc, hemb, Category.assoc, hxV]
  have hjι : jK (V.toScheme.presheaf.stalk z) ≫ (V.toScheme.fromSpecStalk z ≫ V.ι) = (spMap emb ≫ x₀) ≫ U₀.ι := by
    rw [hemb, Category.assoc, hx₀]
  have htg : (spMap emb ≫ x₀) ≫ FinalForm.u₀ = spMap emb ≫ spMap S.R.val.toRingHom := by
    rw [Category.assoc, hx₀u]
  have hjv : jK (V.toScheme.presheaf.stalk z) ≫ (V.toScheme.fromSpecStalk z ≫ v) = (spMap emb ≫ spMap S.R.val.toRingHom) ≫ u := by
    rw [← Category.assoc, hjξ, Category.assoc, hxVv, Category.assoc]

  have hGO : IsSemiAbelian ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G) :=
    IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi
  have hGOg := (isGrpPullback_pullback ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G) (jK (V.toScheme.presheaf.stalk z))).comp
    (isGrpPullback_pullback FinalForm.G (V.toScheme.fromSpecStalk z ≫ V.ι))
  obtain ⟨ψ, hψφ, hψs, hψpb⟩ := exists_genfib_of_zhOut FinalForm _ _ _ hGOg (spMap emb ≫ x₀) hjι.symm
  rw [htg] at hψpb

  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨cO, hcO⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n o o ζ ζ (RingHom.id o) F.X _ F.s
    ((V.toScheme.fromSpecStalk z ≫ v) ≫ F.s) (V.toScheme.fromSpecStalk z ≫ v) rfl
    (by rw [hid, Category.comp_id])).1 F.univ
  obtain ⟨χ, χ₂, χ₂', hχ, hsq, hsq', hP⟩ := exists_siegPB_compare F.univ cO c _ u (jK (V.toScheme.presheaf.stalk z)) _ hjv hcO hpb
  obtain ⟨pr', hpr'χ, hmon', huniv'⟩ := GlobalTheory.T.eighthPowerProjections_groupPullback pr hψpb hχ hmon huniv
  have t2 := GlobalTheory.T.exists_eighth_power_projections_extend_from_generic (V.toScheme.presheaf.stalk z)
  have t3 := t2 ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G)
  have t4 := t3 cO.A
  obtain ⟨prO, hmonO, hprOg, hunivO⟩ := t4 hGO cO.ab pr' hmon' huniv'
  refine ⟨cO, prO, hcO, hmonO, hunivO, ?_, ?_⟩

  ·
    have hLB0 : (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (V.toScheme.fromSpecStalk z ≫ V.ι))).IsLB := pull_isLB FinalForm.L.isLB _
    have hLB1 : (LB.LinComb cO.P (K := Fin 8 × Fin 8) (fun ab => (lift (prO ab.1) (prO ab.2)).left) (fun ab => W ab.1 ab.2)).IsLB :=
      LB.isLB_linComb cO.isLB _ _
    have A1 := _root_.GlobalTheory.Ex.GenericFibre.lbIso_pull (GlobalTheory.PolBaseChange.lbIso_refl hLB0)
      (pullback.fst ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G).hom (jK (V.toScheme.presheaf.stalk z))) hψφ
    have A2 := _root_.GlobalTheory.Ex.GenericFibre.lbIso_pull (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB FinalForm.L.isLB FinalForm.φ)) ψ rfl
    have A3 := _root_.GlobalTheory.Ex.GenericFibre.lbIso_pull (L := ρ.P.L) (a := pullback.fst ρ.P.A.hom FinalForm.u₀) ⟨FinalForm.w, FinalForm.w_gen⟩ ψ rfl
    have X1 := LBIso.trans (pull_isLB hLB0 _) (pull_isLB FinalForm.L.isLB _) (pull_isLB ρ.P.isLB _) A1
      (LBIso.trans (pull_isLB FinalForm.L.isLB _) (pull_isLB (pull_isLB FinalForm.L.isLB _) _) (pull_isLB ρ.P.isLB _) A2.symm A3)
    have X2 := _root_.GlobalTheory.Poinc.Eq8.lbIso_eighth_pull c.P (cO.P.pull χ₂') ρ.P.L _ pr pr' W c.isLB (pull_isLB cO.isLB _) ρ.P.isLB
      (pull_isLB hLB0 _) hsq hP hpr'χ X1 hLc
    have X3 := GlobalTheory.ShapePull.iso_linComb_pull (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB cO.isLB χ₂'))
      (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => (lift (prO ab.1) (prO ab.2)).left)
      (fun ab => W ab.1 ab.2) (pullback.fst ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G).hom (jK (V.toScheme.presheaf.stalk z)))
      (fun ab => by
        have e₁ : ∀ q, (pr' q).left ≫ pullback.fst cO.A.hom (jK (V.toScheme.presheaf.stalk z)) =
            pullback.fst ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G).hom (jK (V.toScheme.presheaf.stalk z)) ≫ (prO q).left := by
          intro q; rw [← hprOg q]; exact pullback.lift_fst _ _ _
        apply _root_.GlobalTheory.GrpSpread.sq_ext
        · rw [Category.assoc _ χ₂', hsq'.1, ← Category.assoc (Over.Hom.left (lift (pr' ab.1) (pr' ab.2))),
            ← Over.comp_left, lift_fst, e₁, Category.assoc (pullback.fst _ _) (Over.Hom.left (lift (prO ab.1) (prO ab.2))),
            ← Over.comp_left, lift_fst]
        · rw [Category.assoc _ χ₂', hsq'.2, ← Category.assoc (Over.Hom.left (lift (pr' ab.1) (pr' ab.2))),
            ← Over.comp_left, lift_snd, e₁, Category.assoc (pullback.fst _ _) (Over.Hom.left (lift (prO ab.1) (prO ab.2))),
            ← Over.comp_left, lift_snd])
    have l4 := lbIso_of_generic_fibre (V.toScheme.presheaf.stalk z)
    have l4' := l4 ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G)
    exact l4' hGO _ _ hLB0 hLB1 (LBIso.trans (pull_isLB hLB0 _) (LB.isLB_linComb (pull_isLB cO.isLB _) _ _)
      (pull_isLB hLB1 _) X2 X3)

  ·
    intro a b f hf
    obtain ⟨hfm, f₁, hf₁, hf₁φ⟩ := hf
    have hmapf : ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).map f).left ≫ pullback.fst FinalForm.G.hom (V.toScheme.fromSpecStalk z ≫ V.ι) =
        pullback.fst FinalForm.G.hom (V.toScheme.fromSpecStalk z ≫ V.ι) ≫ f.left := pullback.lift_fst _ _ _
    have hmapg : ((Over.pullback (jK (V.toScheme.presheaf.stalk z))).map ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).map f)).left ≫
        pullback.fst ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G).hom (jK (V.toScheme.presheaf.stalk z)) = pullback.fst ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G).hom (jK (V.toScheme.presheaf.stalk z)) ≫ ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).map f).left :=
      pullback.lift_fst _ _ _
    have hmapf₁ : ((Over.pullback FinalForm.u₀).map f₁).left ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = pullback.fst ρ.P.A.hom FinalForm.u₀ ≫ f₁.left :=
      pullback.lift_fst _ _ _
    have key : ((Over.pullback (jK (V.toScheme.presheaf.stalk z))).map ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).map f)).left ≫ ψ =
        ψ ≫ ((Over.pullback FinalForm.u₀).map f₁).left := by
      apply FinalForm.cart.1.hom_ext
      · rw [Category.assoc, hψφ, Category.assoc, hf₁φ, ← Category.assoc ψ, hψφ, ← Category.assoc, hmapg, Category.assoc,
          hmapf, Category.assoc]
      · have w1 : ((Over.pullback FinalForm.u₀).map f₁).left ≫ ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom =
            ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom := Over.w _
        have w2 : ψ ≫ ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom = ((Over.pullback (jK (V.toScheme.presheaf.stalk z))).obj ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G)).hom ≫ (spMap emb ≫ x₀) := hψs
        rw [Category.assoc, Category.assoc, w1, w2, ← Category.assoc, Over.w]
    have hgen : ((Over.pullback (jK (V.toScheme.presheaf.stalk z))).map ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).map f)).left ≫
        (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) = (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ f₁.left := by
      rw [← Category.assoc, key, Category.assoc, hmapf₁, Category.assoc]
    have hME := GlobalTheory.T.elementaryMatrixEndomorphism_groupPullback_transport pr pr' a b f₁ _ hψpb hχ hpr'χ hgen hf₁
    have hsemiC := GlobalTheory.isSemiAbelian_of_isAbelianScheme cO.A cO.ab
    have hone : (Over.pullback (jK (V.toScheme.presheaf.stalk z))).map (1 : ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G) ⟶ cO.A) = 1 := by
      apply GlobalTheory.MatEndPull.ext_of_pb (isGrpPullback_pullback cO.A (jK (V.toScheme.presheaf.stalk z)))
      have e1 : ((Over.pullback (jK (V.toScheme.presheaf.stalk z))).map (1 : ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G) ⟶ cO.A)).left ≫ pullback.fst cO.A.hom (jK (V.toScheme.presheaf.stalk z)) =
          pullback.fst ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G).hom (jK (V.toScheme.presheaf.stalk z)) ≫ (1 : ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G) ⟶ cO.A).left := pullback.lift_fst _ _ _
      rw [e1, _root_.ReciprocityTheory.ChartRestriction.G.Chart.one_left', _root_.ReciprocityTheory.ChartRestriction.G.Chart.one_left', Category.assoc ((Over.pullback (jK (V.toScheme.presheaf.stalk z))).obj ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G)).hom,
        _root_.ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left (isGrpPullback_pullback cO.A (jK (V.toScheme.presheaf.stalk z))), ← Category.assoc (pullback.fst _ _) ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G).hom,
        pullback.condition]
      exact Category.assoc _ _ _
    haveI : IsMonHom f := hfm
    refine ⟨inferInstance, fun w => ?_⟩
    haveI := hmon' w
    haveI := hmonO w
    have e0 := GlobalTheory.SemiAbExtDomain.existsUnique_hom_extension_generic (R := (V.toScheme.presheaf.stalk z)) (FractionRing (V.toScheme.presheaf.stalk z))
    have e1 := e0 ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G)
    have e2 := e1 cO.A hGO hsemiC
    have ext : ∃! F : ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G) ⟶ cO.A, IsMonHom F ∧ (Over.pullback (jK (V.toScheme.presheaf.stalk z))).map F =
        (Over.pullback (jK (V.toScheme.presheaf.stalk z))).map ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).map f) ≫ pr' w := e2 _
    have hw := hME.2 w
    apply ext.unique ⟨inferInstance, by rw [Functor.map_comp, hprOg]⟩
    by_cases hwa : w = a
    · rw [if_pos hwa] at hw ⊢
      exact ⟨hmonO b, by rw [hprOg, hw]⟩
    · rw [if_neg hwa] at hw ⊢
      exact ⟨inferInstanceAs (IsMonHom (toUnit _ ≫ η[cO.A])), by rw [hone, hw]⟩

end GlobalTheory.Poinc.Eq8.StalkPow
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniversalObjectAtModelStalk =====
