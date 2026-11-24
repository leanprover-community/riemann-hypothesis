module

public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Satake
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.UG.P

theorem hecke_algebra_GL_commutative : Formalism.UG.HeckeCommGL := hecke_algebra_GL_comm_of_cartan cartan_decomposition_holds

theorem satake_transform_hecke_operator_Tj : Formalism.UG.SatakeTj := satake_Tj_of_spherical_cosets exists_spherical_function Tj_double_coset_decomposition

end Formalism.UG.P
