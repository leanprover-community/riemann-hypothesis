module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieValL
public import Formalism.LocalToGlobal.CharacterGerms.RowTieP_TCoord
public import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsPack
public import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsU
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsE

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

theorem unitSelf_holds (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : UnitSelfSt Y p :=
  unitSelf_of Y p fun o => gmPack_holds Y (p o)

theorem projSelf_holds (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : ProjSelfSt Y p :=
  projSelf_of Y p fun o => gmPack_holds Y (p o)

theorem germLiftSelf_holds (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))
    (H : ∀ o, (Y.rawSelf (p o)).Hyps V) : GermLiftSelfSt Y p H :=
  germLiftSelf_of Y p H (projSelf_holds Y p) fun o => tcoordSelf_holds C V O dd Y d (I0 o) (p o) (H o).cartH

end Formalism.L2.FormalSeriesBounds
