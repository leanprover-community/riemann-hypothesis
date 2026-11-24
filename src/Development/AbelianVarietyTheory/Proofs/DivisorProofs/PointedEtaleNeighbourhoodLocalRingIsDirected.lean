module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing GlobalTheory.Henselisation

open scoped TensorProduct

namespace GlobalTheory.Henselisation

theorem etNbhd_isDirected (R : Type) [CommRing R] [IsLocalRing R] :
    IsDirected (EtNbhd R) (· ≤ ·) := by
  refine ⟨fun i j => ?_⟩
  let C := i.A ⊗[R] j.A
  haveI : Algebra.Etale R C := Algebra.Etale.comp R i.A C
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := C)).1 inferInstance
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let P : C →ₐ[R] ResidueField R := Algebra.TensorProduct.lift i.pt j.pt (fun _ _ => Commute.all _ _)
  let k : EtNbhd R :=
    { n := n, I := RingHom.ker f, etale := Algebra.Etale.of_equiv e.symm, pt := P.comp e.toAlgHom }
  refine ⟨k, ⟨(e.symm.toAlgHom).comp Algebra.TensorProduct.includeLeft, ?_⟩,
    ⟨(e.symm.toAlgHom).comp Algebra.TensorProduct.includeRight, ?_⟩⟩
  · apply AlgHom.ext; intro a
    show P (e (e.symm _)) = i.pt a
    rw [AlgEquiv.apply_symm_apply]
    change P (a ⊗ₜ[R] (1 : j.A)) = i.pt a
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  · apply AlgHom.ext; intro a
    show P (e (e.symm _)) = j.pt a
    rw [AlgEquiv.apply_symm_apply]
    change P ((1 : i.A) ⊗ₜ[R] a) = j.pt a
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

end GlobalTheory.Henselisation
