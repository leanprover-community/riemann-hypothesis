module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParahoricOfScalarActionOnRamifiedParahoricFor
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
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


theorem _root_.GlobalTheory.T.mem_parahoric_of_scalar_action_on_ramifiedParahoricForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (a : s.v.adicCompletion (maximalRealSubfield L)), F ≠ 0 → Valued.v a = 1 → (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s r (s.loc n κ))) → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = 1 → χ ⟨κ, h⟩ = 1) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = a → χ ⟨κ, h⟩ ≠ 1) → ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (∃ c, Eig F κ c) → NG.ParaRT s r (s.loc n κ) := by
  first | exact @GlobalTheory.ParaRigid.mem_para_of_eig | exact GlobalTheory.ParaRigid.mem_para_of_eig | (intros; apply GlobalTheory.ParaRigid.mem_para_of_eig <;> assumption)
