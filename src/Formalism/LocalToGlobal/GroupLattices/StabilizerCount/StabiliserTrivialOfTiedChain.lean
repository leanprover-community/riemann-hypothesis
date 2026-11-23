module

public import Formalism.LocalRingCardinality.DataLevelD
public import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite
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

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.G.StabilizerCardinality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_stab0_mem (D : D7) (lev : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    Nat.card ((D.mem u).C.stab 0 c) = 1 := by
  have := Formalism.L2.G.Triv.stabZero_rec D lev u c
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩

end Formalism.L2.G.StabilizerCardinality

end
