module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory.OffDivisor

theorem etale_localization_of_comap : ∀ (R Q A : Type) [CommRing R] [CommRing Q] [Algebra R Q] [CommRing A] [Algebra R A] (p : Ideal R) [p.IsPrime] (q : Ideal Q) [q.IsPrime], q.comap (algebraMap R Q) = p → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A) → Algebra.Etale (Localization.AtPrime q) (TensorProduct R (Localization.AtPrime q) A) := by
  intro R Q A _ _ _ _ _ p _ q _ hpq h
  subst hpq
  letI : Algebra (Localization.AtPrime (q.comap (algebraMap R Q))) (Localization.AtPrime q) :=
    (Localization.localRingHom _ q (algebraMap R Q) rfl).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (q.comap (algebraMap R Q))) (Localization.AtPrime q) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R Q (Localization.AtPrime q)]
  haveI := Algebra.Etale.baseChange (R := Localization.AtPrime (q.comap (algebraMap R Q))) (B := Localization.AtPrime q) (A := TensorProduct R (Localization.AtPrime (q.comap (algebraMap R Q))) A)
  exact Algebra.Etale.of_equiv ((Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime (q.comap (algebraMap R Q))) (Localization.AtPrime q) (Localization.AtPrime q) A :
    TensorProduct (Localization.AtPrime (q.comap (algebraMap R Q))) (Localization.AtPrime q) (TensorProduct R (Localization.AtPrime (q.comap (algebraMap R Q))) A) ≃ₐ[Localization.AtPrime q] TensorProduct R (Localization.AtPrime q) A))

end GlobalTheory.OffDivisor
