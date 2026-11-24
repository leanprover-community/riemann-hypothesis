module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern

private theorem key_primeq {R : Type} [CommRing R] [Algebra ℚ R] {M c c' : ℕ} [NeZero M] (k : ℕ)
    (ψ : DirichletCharacter R c) (ψ' : DirichletCharacter R c') (e : c = c') (h : c ∣ M) (h' : c' ∣ M)
    (hψ : DirichletCharacter.changeLevel h ψ = DirichletCharacter.changeLevel h' ψ') :
    genB k (ψ : ZMod c → R) = genB k (ψ' : ZMod c' → R) ∧ ∀ a : ℕ, ψ (a : ZMod c) = ψ' (a : ZMod c') := by
  subst e
  have hψψ : ψ = ψ' := DirichletCharacter.changeLevel_injective h hψ
  subst hψψ
  exact ⟨rfl, fun _ => rfl⟩

theorem UpperTheory.V.Bern.b_primeq :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter R N), (χ.IsPrimitive → Bprim k χ = genB k χ ∧ ∀ a : ℕ, primVal χ a = χ (a : ZMod N)) ∧ ∀ (M : ℕ) [NeZero M] (h : N ∣ M), Bprim k (DirichletCharacter.changeLevel h χ) = Bprim k χ ∧ ∀ a : ℕ, primVal (DirichletCharacter.changeLevel h χ) a = primVal χ a := by
  intro R _ _ N _ k χ
  refine ⟨fun hp => ?_, fun M _ h => ?_⟩
  · exact key_primeq k χ.primitiveCharacter χ hp χ.conductor_dvd_level (dvd_refl N)
      (by rw [DirichletCharacter.changeLevel_primitiveCharacter, DirichletCharacter.changeLevel_self])
  · refine key_primeq k (DirichletCharacter.changeLevel h χ).primitiveCharacter χ.primitiveCharacter
      (DirichletCharacter.conductor_changeLevel χ h) (DirichletCharacter.conductor_dvd_level _)
      (χ.conductor_dvd_level.trans h) ?_
    rw [DirichletCharacter.changeLevel_primitiveCharacter,
      DirichletCharacter.changeLevel_trans _ χ.conductor_dvd_level h,
      DirichletCharacter.changeLevel_primitiveCharacter]
