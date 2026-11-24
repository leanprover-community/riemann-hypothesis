module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmHalfIntegralGeneratorMemAlgebraicClosure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianLeviVectorBaseOrthogonal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem heisenbergHaarFacts_hold : InductiveHeisenbergInputs :=
  ⟨Formalism.FourierDecayAlt.P.stabilizer_integration_formula,
    Formalism.FourierDecayAlt.P.rank_one_coordinates_formula,
    Formalism.FourierDecayAlt.P.stabilizer_one_parameter_mem,
    Formalism.FourierDecayAlt.P.unipotent_haar_recursion,
    Formalism.FourierDecayAlt.P.unipotent_haar_base_case,
    Formalism.FourierDecayAlt.P.heisenberg_conjugation_by_levi,
    Formalism.FourierDecayAlt.P.heisenberg_levi_conjugation_measure,
    Formalism.FourierDecayAlt.P.heisenberg_inverse,
    Formalism.FourierDecayAlt.P.heisMul_statement,
    Formalism.FourierDecayAlt.P.heisenberg_mem_unipotent,
    Formalism.FourierDecayAlt.P.heisenberg_subgroup_closed,
    Formalism.FourierDecayAlt.P.heisenberg_haar_measure,
    Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting,
    Formalism.FourierDecayAlt.P.weyl_subgroup_compact,
    Formalism.FourierDecayAlt.P.norm_power_integrable_sharp,
    Formalism.FourierDecayAlt.P.matrix_norm_ge_one,
    Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar,
    Formalism.FourierDecayAlt.P.haar_measure_inversion,
    Formalism.FourierDecayAlt.P.compact_group_haar_exists,
    Formalism.FourierDecayAlt.P.unitary_group_closed,
    Formalism.FourierDecayAlt.P.unipotent_radical_closed,
    Formalism.FourierDecayAlt.P.weyl_subgroup_closed,
    Formalism.FourierDecayAlt.P.levi_haar_measure_exists,
    Formalism.FourierDecayAlt.P.weyl_haar_exists,
    Formalism.FourierDecayAlt.P.unipotent_haar_exists,
    Formalism.FourierDecayAlt.P.unitary_group_haar_exists,
    Formalism.FourierDecayAlt.P.heisenberg_action_formula⟩

end ReciprocityTheory.ChartRestriction.DS.Xi
