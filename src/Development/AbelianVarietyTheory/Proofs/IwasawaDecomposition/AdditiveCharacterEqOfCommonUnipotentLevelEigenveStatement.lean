module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterEqOfCommonUnipotentLevelEigenve
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.additiveCharacter_eq_of_common_unipotentLevel_eigenvector : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (p m : ℕ) (θ : GAf L n ≃* GAf L n) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (F : GAf L n → V) (F' : GAf L n → V') (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (ψ₀ ψ₀' : AddChar (s.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ ξ' : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), p.Prime → s.Above p → m.Coprime p → 2 ≤ r → r ≤ n → FrameAut θ → F ≠ 0 → F' ≠ 0 → NG.IsPsi0 s ψ₀ → NG.IsPsi0 s ψ₀' → NG.LevelUni J χ s r ψ₀ ξ → NG.LevelUni J' χ' s r ψ₀' ξ' → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ : J', Eig F' κ (χ' κ : ℂˣ)) → (∀ κ, TrivOutside {s.v} κ → NG.UniRT s r (s.loc n κ) → ∃ c c' : ℂ, Eig F (θ κ) c ∧ Eig F' (θ κ) c' ∧ c ^ m = c' ^ m) → ∀ y, Valued.v y ≤ 1 → ψ₀ y = ψ₀' y := by
  first | exact @GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq | exact GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq | (intros; apply GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq <;> assumption)
