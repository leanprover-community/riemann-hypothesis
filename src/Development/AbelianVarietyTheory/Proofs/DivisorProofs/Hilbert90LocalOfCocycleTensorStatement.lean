module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90LocalOfCocycleTensor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open TensorProduct

theorem _root_.GlobalTheory.T.hilbert90_of_cocycle_faithfullyFlat_tensor : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
    [Module.FaithfullyFlat R S] (c : (S ⊗[R] S)ˣ),
    Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) (c : S ⊗[R] S) *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) →
    ∀ p : Ideal R, p.IsPrime → ∃ r ∉ p, ∃ m s : S, ∃ n : ℕ,
      (m ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] m ∧ m * s = algebraMap R S r ^ n := by
  first | exact @GlobalTheory.FlatDescent.hilbert90_local_of_cocycle | exact GlobalTheory.FlatDescent.hilbert90_local_of_cocycle | (intros; apply GlobalTheory.FlatDescent.hilbert90_local_of_cocycle <;> assumption)
