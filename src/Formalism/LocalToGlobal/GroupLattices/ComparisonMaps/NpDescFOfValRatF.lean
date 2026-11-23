module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
public import Formalism.SharpRestriction.GrowthBounds.PlaneCountTheoremWithConstants
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.YvRatOfValRat
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NpDescOfValRat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

def ValRatF {eps : ℝ} (Fm : FamP eps) : Prop :=
  Ev Fm fun x i => ∀ hx : Fm.x1 < x, ValRat (Fm.ex x hx i).cmp

theorem npDescF_of_valRatF {eps : ℝ} (Fm : FamP eps) (h : ValRatF Fm) : NPDescF Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx i hx1 => ?_⟩
  refine npDesc_of_valRat _ (Fm.gatT x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK ?_ (hx0 x hx i hx1)
  exact (Fm.ex x hx1 i).lat.vram

theorem CmpTied.valRat {D : D7} {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D}
    {c : LatCmp D} (K : CmpTied D X T Gt c) : ValRat c := by
  intro u w hg x i L hL
  exact ⟨_, ((K.tie u w hg).val_cmp x i L hL).symm⟩

end Formalism.L2.G.Cmp
