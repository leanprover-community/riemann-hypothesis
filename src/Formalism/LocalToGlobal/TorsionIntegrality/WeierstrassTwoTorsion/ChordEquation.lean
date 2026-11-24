module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementM
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementN
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ChainRuleFormalGroupVar
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.XPowSuccDvdOfDerivative
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

universe u v

namespace Formalism.L2.Th1.A

theorem zMap : ZMap.{u, v} := z_series_map_spec
theorem jetMem : JetMem.{u} := jet_mem'
theorem wpPrimeShape : WpPrimeShape.{u} := weierstrass_p_prime_shape

theorem plusZCleared : PlusZCleared.{u} := plusZCleared_of plusZ tInZ

end Formalism.L2.Th1.A
