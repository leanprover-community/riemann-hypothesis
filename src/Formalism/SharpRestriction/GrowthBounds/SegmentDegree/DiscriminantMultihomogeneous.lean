module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AllowedLettersOfLateRows
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SegmentProductDegreeDetermined
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem degAt_ph_detPl {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (j x : ℤ) (t : Fin n') :
    DegAt t (∑ a : Fin r, if posOf n' (X.row j x a) = t then p ^ X.F.dist j (X.row j x a) else 0)
      (phSeg R K p X.F j (plEmb R r K (X.detPl R j x))) := by
  have key : ∀ σ : Equiv.Perm (Fin r), DegAt t
      (∑ a : Fin r, if posOf n' (X.row j x a) = t then p ^ X.F.dist j (X.row j x a) else 0)
      (∏ i : Fin r, phSeg R K p X.F j (plEmb R r K (MvPolynomial.X (X.row j x (σ i), i)))) := by
    intro σ
    rw [← Equiv.sum_comp σ (fun a => if posOf n' (X.row j x a) = t then p ^ X.F.dist j (X.row j x a) else 0)]
    apply degAt_prod
    intro i _
    simp only [plEmb, phSeg, rename_X, aeval_X]
    have h := degAt_pow (R := R) (degAt_X (x := t) (posOf n' (X.row j x (σ i)), Fin.castAdd K i))
      (p ^ X.F.dist j (X.row j x (σ i)))
    convert h using 2
    split_ifs <;> simp
  unfold Dat.detPl
  rw [Matrix.det_apply']

  simp only [map_sum, map_mul, map_prod, Matrix.of_apply, map_intCast]
  apply degAt_sum
  intro σ _
  have e : ((Equiv.Perm.sign σ : ℤ) : RRing R n' (r + K)) = C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
  rw [e]
  exact degAt_C_mul _ (key σ)

theorem discriminant_multihomogeneous : DiscriminantMultihomogeneous := by
  intro p n' r K _ _ _ X O _
  rw [RRdeg, mem_restrictSupport_iff]
  intro m hm t
  have hdeg : DegAt t (X.Et p K t) (X.Dl p K O) := by
    unfold Dat.Dl Dat.DlSeg Dat.Et
    simp only [map_prod, map_pow]
    apply degAt_prod
    intro j _
    apply degAt_prod
    intro x _
    exact degAt_pow (degAt_ph_detPl X p K j x t) _
  exact hdeg m hm

end Formalism.MainNotions.SelectionLemmas.Pf
