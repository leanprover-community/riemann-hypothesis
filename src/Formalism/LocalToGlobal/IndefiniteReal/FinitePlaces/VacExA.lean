module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct




namespace Formalism.IndefR.Fin.VacEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsDyIdem (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) : Prop :=
  IsSplitIdem D e ∧ finPart D e ∈ intAE D ∧
    ∃ ε : AF D.host.F, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε


theorem fstA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : fstA D.host.F (pairA D.host.F x y) = x := rfl
theorem sndA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : sndA D.host.F (pairA D.host.F x y) = y := rfl



section Sym

variable (S T : HSp D)

end Sym

section Phi

variable (S T : HSp D)

def U0 (Λ : AddSubgroup (WO S T)) : AddSubgroup (WO S T) where
  carrier := {w | ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0}
  add_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u + u', Λ.add_mem hu hu', fun i j => ?_⟩
    have : (a + b - (u + u')) i j = (a - u) i j + (b - u') i j := by
      simp only [Matrix.sub_apply, Matrix.add_apply]; abel
    rw [this, map_add (f := _), ha, hb, add_zero]
  zero_mem' := ⟨0, Λ.zero_mem, fun i j => by simp⟩
  neg_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨-u, Λ.neg_mem hu, fun i j => ?_⟩
    have : (-a - -u) i j = -((a - u) i j) := by simp only [Matrix.sub_apply, Matrix.neg_apply]; abel
    rw [this, map_neg, ha, neg_zero]

theorem mem_U0 {Λ : AddSubgroup (WO S T)} {w : WO S T} :
    w ∈ U0 S T Λ ↔ ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0 := Iff.rfl

theorem le_open_neighbourhood {Λ : AddSubgroup (WO S T)} : Λ ≤ U0 S T Λ := fun u hu => ⟨u, hu, fun i j => by simp⟩

theorem open_neighbourhood_set_eq (Λ : AddSubgroup (WO S T)) :
    (U0 S T Λ : Set (WO S T)) = {w | ∃ u ∈ Λ, (w - u).map (finPart D) = 0} := by
  ext w
  simp only [SetLike.mem_coe, mem_U0, Set.mem_setOf_eq]
  refine exists_congr fun u => and_congr_right fun _ => ⟨fun h => ?_, fun h i j => ?_⟩
  · ext i j; exact h i j
  · have := congrFun (congrFun h i) j; simpa using this


end Phi

section Lat

variable (S T : HSp D)

variable {S T}

end Lat

end Formalism.IndefR.Fin.VacEx
