module

public import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KUnr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

section Loc

variable {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ] {M : Type} [AddCommGroup M] [Module O M]

theorem locRep_triv (g : Γ) (x : KHf.MK (O := O) M) :
    KHf.locRep (Representation.trivial O Γ M) g x = x := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map (nonZeroDivisors O) (Representation.trivial O Γ M g) (LocalizedModule.mk m s) =
      LocalizedModule.mk m s
    rw [LocalizedModule.map_mk]
    rfl

end Loc

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (δO : D.nd.O i)

theorem col_mem (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ dc.col := by
  have h : l.1 ∈ K.plSet i dc := by
    unfold K.plSet
    simp [l.2]
  rw [K.colIdx, K.plOf_idx i dc h]
  exact l.2

end Rec

end Formalism.MainNotions.N.KUnr
