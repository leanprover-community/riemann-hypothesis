module

public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.CardTwoSidedQuotient
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.KerHalf
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.KerJet
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.KernelIndexForm
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.LinearSubstitutionDiagonal
public import Formalism.LocalToGlobal.AlgebraicTheory.SplitPlaceScaledBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace Formalism.L2.AlgTh

theorem jetAtSplit : JetAtSplit :=
  jetAtSplit_of split_place_scaled_bound kernel_index_form representatives_split level_kills_half_lattice chosen_lift_killed_level p_torsion_represents_quotient card_two_sided_quotient index_product_formula
    taylor_jet_expansion linear_substitution_diagonal

end Formalism.L2.AlgTh
