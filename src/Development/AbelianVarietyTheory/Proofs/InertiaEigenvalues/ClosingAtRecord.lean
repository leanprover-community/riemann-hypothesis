module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultVTwistedDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotDRLOfTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateTwistMultiplicationIntertwines
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.Closing

theorem closing_at_record : ∀ D : D7, DualJumpL D.loc ∧ PotDRL D.loc ∧ PcrisTensorL D.loc ∧
    PairedCharacterCondition.tieBr (D := D) ∧ InertEq D := by
  intro D
  have hT : ∀ (l : ℕ) [Fact (Nat.Prime l)], Nonempty (LocTied l (D.loc l) (D.locA l)) :=
    fun l _ => ⟨D.locT l⟩
  refine ⟨GlobalTheory.DualJump.dualJumpL D.loc D.locA hT, GlobalTheory.Pass.potDRL_of_tied D.loc D.locA hT,
    GlobalTheory.PcrisTwist.pcrisTensorL_of_tied D.loc D.locA hT, ?_, GlobalTheory.BridgeInertia.inertEq D⟩
  intro i w hw
  exact GlobalTheory.bridge_degW D.nbr i w hw

end GlobalTheory.Closing
