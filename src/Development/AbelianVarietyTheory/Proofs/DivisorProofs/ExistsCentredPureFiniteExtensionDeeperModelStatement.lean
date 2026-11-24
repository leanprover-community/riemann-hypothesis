module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalIntegralClosureUnitDegree
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Invariant.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionDegreeDvdCardInvariants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureGaloisFiniteAutGroupInvariants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing
public import Mathlib.Basic.Finite.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLiftInvariantExtensionLocalisation
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominatorStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtensionStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModel, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModelStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominatorStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominatorStatement", "h": "module\n\npublic import Mathlib.AlgebraicGeometry.Morphisms.Finite\npublic import Mathlib.Combinatorics.Quiver.ReflQuiver\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominator\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf\nimport Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt\nimport Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.finite_stalk_germ_quotient_integral_unit_denominator : ∀ (X Y : Scheme.{0}) (p : Y ⟶ X), IsFinite p → ∀ (y : Y) (a : Y.presheaf.stalk y), ∃ b s : Y.presheaf.stalk y, IsUnit s ∧ a * s = b ∧ (∃ P : Polynomial (X.presheaf.stalk (p y)), P.Monic ∧ P.eval₂ (p.stalkMap y).hom b = 0) ∧ ∃ Q : Polynomial (X.presheaf.stalk (p y)), Q.Monic ∧ Q.eval₂ (p.stalkMap y).hom s = 0 := by
  first | exact @GlobalTheory.Poinc.finite_stalk_quot_integral
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominatorStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtensionStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtensionStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtension\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf\nimport Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt\nimport Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.stalkHom_stalkMap_eq_functionFieldExtension : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (p : M₂.Z ⟶ M₁.Z), M₂.pt ≫ p = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (z₂ : M₂.Z) (x : M₁.Z.presheaf.stalk (p z₂)), M₂.stalkHom z₂ ((p.stalkMap z₂).hom x) = algebraMap Ω₁ Ω₂ (M₁.stalkHom (p z₂) x) := by
  first | exact @GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtensionStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModel =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModel", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalIntegralClosureUnitDegree\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Defs\npublic import Mathlib.RingTheory.Invariant.Defs\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionDegreeDvdCardInvariants\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominatorStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureGaloisFiniteAutGroupInvariants\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtensionStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing\npublic import Mathlib.Basic.Finite.Defs\npublic import Mathlib.RingTheory.LocalRing.Defs\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLiftInvariantExtensionLocalisation\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep

theorem exists_centred_ext_tower : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsCN V → IsLocalHom ev → RegAt X₁ z₁ ev → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ 𝔗.Ext ev io ev₂ := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ z₁ act _ 𝔗 z₂ hz V _ _ _ ev hV hev _
  subst hz

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ := (X₁.M.stalkHom (𝔗.p z₂)).toAlgebra
  obtain ⟨hdom, hfr, hic, hno⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ (𝔗.p z₂)
  letI : Algebra (𝔗.X₂.M.Z.presheaf.stalk z₂) 𝔗.X₂.Ω₁ := (𝔗.X₂.M.stalkHom z₂).toAlgebra
  obtain ⟨hdom₂, hfr₂, hic₂, -⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i 𝔗.X₂ z₂
  haveI := 𝔗.fd
  haveI := 𝔗.gal
  obtain ⟨hfin, hfinA, hinj, hfix⟩ := GlobalTheory.Poinc.integralClosure_galois_finite_invariants (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom (𝔗.p z₂))).toAlgebra
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hdom; haveI := hfr; haveI := hic; haveI := hdom₂; haveI := hfr₂; haveI := hic₂
  haveI : Algebra.IsInvariant (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) :=
    ⟨fun b hb => hfix b hb⟩
  haveI : Module.Finite (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) := hfin
  haveI : Finite (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) := hfinA
  have hcard : Nat.card (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) = Module.finrank X₁.Ω₁ 𝔗.X₂.Ω₁ := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (galRestrict (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁ (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)).toEquiv).symm

  have hn1 : IsUnit ((X₁.ρ.n : ℕ) : X₁.o₁) := by
    have hu := X₁.S.unit
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [X₁.ρ.N_eq]
      exact Dvd.dvd.mul_left (dvd_pow (dvd_pow_self _ (by have := X₁.ρ.two_le; omega)) two_ne_zero) _
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul] at hu
    exact isUnit_of_mul_isUnit_left hu
  have hnA : IsUnit ((X₁.ρ.n : ℕ) : (X₁.M.Z.presheaf.stalk (𝔗.p z₂))) := by
    obtain ⟨u, hu⟩ := hn1
    have hm : algebraMap X₁.o₁ X₁.Ω₁ (↑u⁻¹) ∈ X₁.M.O (𝔗.p z₂) := Subalgebra.algebraMap_mem _ _
    refine IsUnit.of_mul_eq_one ((X₁.M.stalkEquiv _).symm ⟨_, hm⟩) (X₁.M.stalkHom_injective _ ?_)
    rw [map_mul, map_one, map_natCast, ← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    change ((X₁.ρ.n : ℕ) : X₁.Ω₁) * algebraMap X₁.o₁ X₁.Ω₁ (↑u⁻¹) = 1
    rw [← map_natCast (algebraMap X₁.o₁ X₁.Ω₁), ← hu, ← map_mul, Units.mul_inv, map_one]
  have hnV : IsUnit ((X₁.ρ.n : ℕ) : V) := by simpa using hnA.map ev
  have hdegV : IsUnit ((Module.finrank X₁.Ω₁ 𝔗.X₂.Ω₁ : ℕ) : V) := by
    obtain ⟨e, he⟩ := 𝔗.deg
    rw [he, Nat.cast_pow]
    exact hnV.pow e

  haveI : CharZero V := hV.2.2.2
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  obtain ⟨K', _, _, β, hK'fd, hK'dvd, hβ⟩ := _root_.GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)
    (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) hinj (FractionRing V)
    ((algebraMap V (FractionRing V)).comp ev)
  haveI := hK'fd
  have hK'u : IsUnit ((Module.finrank (FractionRing V) K' : ℕ) : V) := by
    rw [hcard] at hK'dvd
    obtain ⟨c, hc⟩ := hK'dvd
    rw [hc, Nat.cast_mul] at hdegV
    exact isUnit_of_mul_isUnit_left hdegV
  obtain ⟨V', _, _, _, io, j, hV', hioi, hiof, hiol, hcon, hjinj, hj, hjr⟩ := _root_.GlobalTheory.LocExt.exists_isCN_integralClosure_of_isUnit_finrank V hV K' hK'u
  have hβmem : ∀ b : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, β b ∈ j.range := by
    intro b
    obtain ⟨P, hPm, hP⟩ := integralClosure.isIntegral b
    obtain ⟨y, hy⟩ := hjr (β b) ⟨P.map ev, hPm.map ev, by
      rw [Polynomial.eval₂_map, RingHom.comp_assoc, ← hβ, ← Polynomial.hom_eval₂, hP, map_zero]⟩
    exact ⟨y, hy⟩
  let jr : V' ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hjinj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let β' : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →+* V' := jr.symm.toRingHom.comp (β.codRestrict j.range hβmem)
  have hβ' : ∀ b, j (β' b) = β b := fun b => congrArg Subtype.val (jr.apply_symm_apply ⟨β b, hβmem b⟩)

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (𝔗.X₂.M.Z.presheaf.stalk z₂) := (𝔗.p.stalkMap z₂).hom.toAlgebra
  have hg1 : ∀ x : (X₁.M.Z.presheaf.stalk (𝔗.p z₂)), 𝔗.X₂.M.stalkHom z₂ ((𝔗.p.stalkMap z₂).hom x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) :=
    fun x => (GlobalTheory.T.stalkHom_stalkMap_eq_functionFieldExtension X₁.o₁ X₁.Ω₁ 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ X₁.M 𝔗.X₂.M 𝔗.p 𝔗.p_pt z₂ x)
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (𝔗.X₂.M.Z.presheaf.stalk z₂) 𝔗.X₂.Ω₁ := IsScalarTower.of_algebraMap_eq fun x => (hg1 x).symm
  have hinj₂ := 𝔗.X₂.M.stalkHom_injective z₂
  have hBmem : ∀ b : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, (b : 𝔗.X₂.Ω₁) ∈ (𝔗.X₂.M.stalkHom z₂).range := fun b => by
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := (𝔗.X₂.M.Z.presheaf.stalk z₂)) (K := 𝔗.X₂.Ω₁)).1
      (IsIntegral.tower_top (A := (𝔗.X₂.M.Z.presheaf.stalk z₂)) b.2)
    exact ⟨y, hy⟩
  let e₂ : (𝔗.X₂.M.Z.presheaf.stalk z₂) ≃+* (𝔗.X₂.M.stalkHom z₂).range := RingEquiv.ofBijective (𝔗.X₂.M.stalkHom z₂).rangeRestrict
    ⟨fun a b h => hinj₂ (congrArg Subtype.val h), (𝔗.X₂.M.stalkHom z₂).rangeRestrict_surjective⟩
  let f : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →+* (𝔗.X₂.M.Z.presheaf.stalk z₂) :=
    e₂.symm.toRingHom.comp (((integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁).val : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] 𝔗.X₂.Ω₁).toRingHom.codRestrict _ hBmem)
  have hf : ∀ b, 𝔗.X₂.M.stalkHom z₂ (f b) = b := fun b => congrArg Subtype.val (e₂.apply_symm_apply ⟨_, hBmem b⟩)
  have hfB : ∀ (t : (𝔗.X₂.M.Z.presheaf.stalk z₂)) (h : 𝔗.X₂.M.stalkHom z₂ t ∈ integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁), f ⟨_, h⟩ = t :=
    fun t h => hinj₂ (hf _)
  have hloc : IsLocalHom (f.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁))) := by
    have h : f.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)) = (𝔗.p.stalkMap z₂).hom :=
      RingHom.ext fun a => hinj₂ (by rw [RingHom.comp_apply, hf, hg1]; rfl)
    rw [h]; infer_instance
  have hint : ∀ t : (𝔗.X₂.M.Z.presheaf.stalk z₂), (∃ P : Polynomial (X₁.M.Z.presheaf.stalk (𝔗.p z₂)), P.Monic ∧ P.eval₂ (𝔗.p.stalkMap z₂).hom t = 0) →
      𝔗.X₂.M.stalkHom z₂ t ∈ integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ := by
    rintro t ⟨P, hPm, hP⟩
    refine ⟨P, hPm, ?_⟩
    have h : algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ = (𝔗.X₂.M.stalkHom z₂).comp (𝔗.p.stalkMap z₂).hom := RingHom.ext fun x => (hg1 x).symm
    rw [h, ← Polynomial.hom_eval₂, hP, map_zero]
  have hsurj : ∀ y : (𝔗.X₂.M.Z.presheaf.stalk z₂), ∃ b s : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, IsUnit (f s) ∧ y * f s = f b := by
    intro y
    obtain ⟨b, s, hs, hys, hb, hs'⟩ := GlobalTheory.T.finite_stalk_germ_quotient_integral_unit_denominator _ _ 𝔗.p 𝔗.p_fin z₂ y
    refine ⟨⟨_, hint b hb⟩, ⟨_, hint s hs'⟩, ?_, ?_⟩
    · rw [hfB]; exact hs
    · rw [hfB, hfB]; exact hys
  have hker : ∀ b, f b = 0 → ∃ s : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, IsUnit (f s) ∧ s * b = 0 := fun b hb =>
    ⟨1, by rw [map_one]; exact isUnit_one, by
      rw [_root_.one_mul]; exact Subtype.ext (by rw [← hf b, hb, map_zero]; rfl)⟩
  haveI := hiol; haveI := hev
  have hβ'A : β'.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)) = io.comp ev := RingHom.ext fun a =>
    hjinj ((hβ' _).trans ((RingHom.congr_fun hβ a).trans (RingHom.congr_fun hj (ev a)).symm))
  obtain ⟨ev₂, hev₂, hcomp⟩ := _root_.GlobalTheory.twisted_lift_to_localisation (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) (𝔗.X₂.M.Z.presheaf.stalk z₂)
    (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) f hloc hsurj hker V' (io.comp ev) β' inferInstance hβ'A
  refine ⟨V', inferInstance, inferInstance, inferInstance, io, ev₂, hV', hioi, hiof, hiol, hcon, hev₂, fun x x₂ hx => ?_⟩
  have h : x₂ = f (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) x) := hinj₂ (by rw [hf]; exact hx)
  rw [h]
  exact RingHom.congr_fun hcomp x

end GlobalTheory.Poinc.Sep
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModel =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModelStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModelStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModel\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_centred_pure_finite_extension_deeper_model : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsCN V → IsLocalHom ev → RegAt X₁ z₁ ev → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ 𝔗.Ext ev io ev₂ := by
  first | exact @GlobalTheory.Poinc.Sep.exists_centred_ext_tower
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModelStatement =====
