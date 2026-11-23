module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodProductCommutesFrobeniusZpow
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

theorem _root_.GlobalTheory.T.periodProduct_commutes_frobenius_zpow : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρs)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρm)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρt)] (n : ℤ) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)), ((phiU P ρt ^ n : (Module.End ↥L.1 ↥(Dpst P ρt))ˣ) : Module.End ↥L.1 ↥(Dpst P ρt)) (GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y) = GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht (((phiU P ρs ^ n : (Module.End ↥L.1 ↥(Dpst P ρs))ˣ) : Module.End ↥L.1 ↥(Dpst P ρs)) x) (((phiU P ρm ^ n : (Module.End ↥L.1 ↥(Dpst P ρm))ˣ) : Module.End ↥L.1 ↥(Dpst P ρm)) y) := by
  first | exact @GlobalTheory.Pst.TwistLetters.phiU_zpow_dmul | exact GlobalTheory.Pst.TwistLetters.phiU_zpow_dmul | (intros; apply GlobalTheory.Pst.TwistLetters.phiU_zpow_dmul <;> assumption)
