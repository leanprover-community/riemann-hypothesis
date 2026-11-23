module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
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

namespace Formalism.L2.KerInert

def Adm8All : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p), Formalism.MainNotions.FormalGroupSystem.adm8 D X

theorem admissible_all_levels : Adm8All := fun D _ _ X =>
  ⟨Formalism.MainNotions.G.LatticeSystems.exponent_condition_holds D X.G, (Formalism.L2.G.Model.operators_preserve_lattices D X.G).2⟩

end Formalism.L2.KerInert
