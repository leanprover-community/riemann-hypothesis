module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibFibT
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Onto

theorem mem_closure_image {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (H : AddSubgroup A)
    (y : B) : y ∈ AddSubgroup.closure (f '' (H : Set A)) ↔ ∃ t ∈ H, f t = y := by
  rw [← AddSubgroup.coe_map, AddSubgroup.closure_eq, AddSubgroup.mem_map]

variable {D : D7} (X : HidaSetting D)

def embHom : D.host.E →+ (InfinitePlace X.B.I.F → ℂ) where
  toFun := embV X
  map_zero' := by funext v; simp [embV]
  map_add' x y := by funext v; simp [embV]

theorem mem_cl_emb (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (y : InfinitePlace X.B.I.F → ℂ) :
    y ∈ AddSubgroup.closure (embV X '' (I : Set D.host.E)) ↔ ∃ t ∈ I, embV X t = y := by
  have := mem_closure_image (embHom X) ((I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) y
  exact this

theorem theta_spec (D : D7) : IsIntegral ℤ (theta D) ∧ theta D + D.host.conj (theta D) = 1 := by
  have h := thetaEx_holds D
  unfold theta
  rw [dite_eq_left h]
  exact h.choose_spec

end Onto

end Formalism.L2.SG.Pf.NcReal.JX.NOf
