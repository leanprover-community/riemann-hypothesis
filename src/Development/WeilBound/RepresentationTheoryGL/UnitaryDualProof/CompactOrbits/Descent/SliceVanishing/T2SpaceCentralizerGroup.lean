module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.ContinuousCj
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.NilpotentPowers.IsNilpotentPowSub
public import GroundTheory.AutomorphicForms.WhittakerDistribution
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem t2k : T2Space k := Asm.t2

theorem tdk : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField

theorem sck : SecondCountableTopology k := (GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).1

theorem continuous_aevalM (P : k[X]) : Continuous fun x : Matrix (Fin n) (Fin n) k => aeval x P := by
  have : T2Space k := t2k
  simp_rw [aeval_eq_sum_range]
  exact continuous_finsetSum _ fun i _ => (continuous_pow i).const_smul (P.coeff i)

theorem isClosed_Tset {F : Set (Matrix (Fin n) (Fin n) k)} (hF : IsClosed F) (P : k[X]) : IsClosed (Tset F P) := by
  have : T2Space k := t2k
  exact hF.inter (isClosed_eq (continuous_aevalM P) continuous_id)

instance t2Space_centralizer_group (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : T2Space (GzS Z) := by
  have : T2Space k := t2k
  infer_instance

instance gzs_td (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : TotallyDisconnectedSpace (GzS Z) := by
  infer_instance

instance gzs_sc (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : SecondCountableTopology (GzS Z) := by
  have : SecondCountableTopology (GL (Fin n) k) := GlobalTheory.SplitFlip.secondCountable_GL
  exact TopologicalSpace.Subtype.secondCountableTopology _

instance gzs_sig (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : SigmaCompactSpace (GzS Z) := by
  infer_instance

end PositivityTheory.RgUd.T.Desc.SLF
