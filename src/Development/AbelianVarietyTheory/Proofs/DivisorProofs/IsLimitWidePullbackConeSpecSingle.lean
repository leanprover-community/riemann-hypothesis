module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

namespace GlobalTheory.CechOne

theorem isLimit_cone_one (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (0 + 1) => GlobalTheory.CechOne.fB A B)
      (GlobalTheory.CechOne.fB A B) (fun _ => 𝟙 _) (fun _ => Category.id_comp _))) := by
  refine ⟨WidePullbackCone.IsLimit.mk _ (fun t => t.π 0) ?_ ?_ ?_⟩
  · intro t
    rw [WidePullbackCone.mk_base]
    exact t.condition 0
  · intro t i
    rw [WidePullbackCone.mk_π]
    exact (Category.comp_id (t.π 0)).trans (congrArg t.π (Fin.fin_one_eq_zero i).symm)
  · intro t m _ hπ
    have := hπ 0
    rw [WidePullbackCone.mk_π] at this
    exact (Category.comp_id m).symm.trans this

end GlobalTheory.CechOne
