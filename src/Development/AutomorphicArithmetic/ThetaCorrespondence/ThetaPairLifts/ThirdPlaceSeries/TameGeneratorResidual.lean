module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFrobeniusConjInertiaPowModWildStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameGeneratorResidual
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReductionTrivialOnWildInertia
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

@[expose] public section



section
noncomputable section
namespace GlobalTheory.ResidualTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.ResidualTame
namespace GlobalTheory.RowWildTame
end GlobalTheory.RowWildTame
namespace GlobalTheory.RowTie
theorem tameGenerator_residual_alt_alt (D : D7) (h1 : GlobalTheory.RowCopy.RbarTie D) (h2 : GlobalTheory.RowTie.IotaRed D)
    (h3 : _root_.UpperTheory.GalS.LabTameS D.nd D.naut) (h4 : _root_.UpperTheory.GalS.RowRepAtGN D) :
    GlobalTheory.RowCopy.JointOccurrenceCondition D := by
  intro σ k v _ _ i hl hne hg
  refine ⟨_root_.GlobalTheory.ResidualTame.cpAt' D h1 h2 h3 h4 σ k v i hl hne hg, ?_⟩
  obtain ⟨φ, hI, hW⟩ := GlobalTheory.T.exists_frobenius_conj_inertia_pow_mod_wild _ _ _ D.nd D.naut k v _ (D.ntypes.tg_mem k v)
  refine ⟨φ, ?_⟩
  have h := _root_.GlobalTheory.T.rbar_wild_inertia_of_labTame_repAtGN D h1 h3 h4 σ k v i hl hne hg _ hI hW
  rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h
  exact h
end GlobalTheory.RowTie
end
end
