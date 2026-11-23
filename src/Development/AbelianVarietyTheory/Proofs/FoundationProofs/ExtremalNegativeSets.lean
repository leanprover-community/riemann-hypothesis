module

public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.FWT

namespace GlobalTheory.Cmp.ExtremalNegativeSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Idx

variable {n : ℕ} {ε : Fin n → Bool}

theorem mem_negS {a : Fin n} : a ∈ negS ε ↔ ε a = false := by simp [negS]

theorem revNeg_anti {a b : Fin n} (hab : a < b) (ha : ε a = false) (hb : ε b = false) :
    revNeg ε b < revNeg ε a := by
  have ha' : a ∈ negS ε := mem_negS.2 ha
  have hb' : b ∈ negS ε := mem_negS.2 hb
  rw [show revNeg ε a = (revOn ε ⟨a, ha'⟩ : Fin n) from Equiv.Perm.ofSubtype_apply_of_mem _ ha',
    show revNeg ε b = (revOn ε ⟨b, hb'⟩ : Fin n) from Equiv.Perm.ofSubtype_apply_of_mem _ hb']
  have h1 : ((negS ε).orderIsoOfFin rfl).symm ⟨a, ha'⟩ < ((negS ε).orderIsoOfFin rfl).symm ⟨b, hb'⟩ :=
    (OrderIso.lt_iff_lt _).2 (Subtype.mk_lt_mk.2 hab)
  exact ((negS ε).orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.2 h1)

end Idx

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end GlobalTheory.Cmp.ExtremalNegativeSets

end
