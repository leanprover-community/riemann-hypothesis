module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

instance borelMx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩

instance tagMx (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) :=
  inferInstanceAs (IsTopologicalAddGroup (Fin m → Fin n → AE D))

theorem countable_ratMx (m n : ℕ) : Countable (ratMx D m n) := by
  haveI : Countable D.host.E :=
    Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.symm.toEquiv
  haveI : Countable (Matrix (Fin m) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin m → Fin n → D.host.E))
  unfold ratMx
  have hs : Function.Surjective (fun x : Matrix (Fin m) (Fin n) D.host.E =>
      (⟨_, AddMonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ :
        ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range)) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hy
    exact ⟨x, rfl⟩
  exact hs.countable

end Formalism.IndefR.Eqv

end
