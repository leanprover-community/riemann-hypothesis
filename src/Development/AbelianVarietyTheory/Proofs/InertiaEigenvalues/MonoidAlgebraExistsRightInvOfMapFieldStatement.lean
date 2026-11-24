module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonoidAlgebraExistsRightInvOfMapField
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


theorem _root_.GlobalTheory.T.monoidAlgebra_exists_right_inv_of_map_field : ∀ {E L G : Type} [Field E] [Field L] [Group G] [Fintype G] (j : E →+* L) (x : MonoidAlgebra E G), (∃ v : MonoidAlgebra L G, MonoidAlgebra.mapRingHom G j x * v = 1) → ∃ v : MonoidAlgebra E G, x * v = 1 := by
  first | exact @GlobalTheory.groupAlgebra_exists_right_inv_of_map | exact GlobalTheory.groupAlgebra_exists_right_inv_of_map | (intros; apply GlobalTheory.groupAlgebra_exists_right_inv_of_map <;> assumption)
