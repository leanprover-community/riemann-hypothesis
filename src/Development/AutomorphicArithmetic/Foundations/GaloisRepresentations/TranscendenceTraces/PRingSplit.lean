module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianIndEtaleOverPrimeStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

theorem UpperTheory.Gal.TranscendenceTraces.ringSplit_of :
    FinSec → IndDesc → RingSplit := by
  intro hF hI A B C _ _ _ _ _ _ _ _ P
  obtain ⟨O, _, _, _, hSH, hInd, hP⟩ := GlobalTheory.T.exists_strictlyHenselian_indEtale_over_prime A P.asIdeal
  letI : Algebra B (O ⊗[A] B) := (Algebra.TensorProduct.includeRight : B →ₐ[A] O ⊗[A] B).toRingHom.toAlgebra
  obtain ⟨s⟩ := hF O (O ⊗[A] B) ((O ⊗[A] B) ⊗[B] C) hSH
  have t0 : C →ₐ[B] O ⊗[A] B :=
    (s.restrictScalars B).comp (Algebra.TensorProduct.includeRight : C →ₐ[B] (O ⊗[A] B) ⊗[B] C)
  let c : O ⊗[A] B →ₐ[B] B ⊗[A] O :=
    { (Algebra.TensorProduct.comm A O B).toAlgHom.toRingHom with
      commutes' := fun b => by
        show Algebra.TensorProduct.comm A O B ((1 : O) ⊗ₜ[A] b) = b ⊗ₜ[A] (1 : O)
        simp }
  obtain ⟨E, _, _, hE, ⟨φ⟩, hC⟩ := hI A O B C hInd ⟨c.comp t0⟩
  refine ⟨E, inferInstance, inferInstance, hE, ?_, hC⟩
  haveI : (Ideal.comap (φ : E →+* O) (IsLocalRing.maximalIdeal O)).IsPrime := Ideal.comap_isPrime _ _
  refine ⟨⟨Ideal.comap (φ : E →+* O) (IsLocalRing.maximalIdeal O), inferInstance⟩, ?_⟩
  ext1
  show Ideal.comap (algebraMap A E) (Ideal.comap (φ : E →+* O) (IsLocalRing.maximalIdeal O)) = P.asIdeal
  rw [Ideal.comap_comap, ← hP]
  congr 1
  exact φ.comp_algebraMap
