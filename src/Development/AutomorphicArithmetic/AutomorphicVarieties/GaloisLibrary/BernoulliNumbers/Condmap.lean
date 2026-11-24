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

private theorem change_level_value_eq {R S : Type} [CommRing R] [CommRing S] {N : ℕ} [NeZero N] (f : R →+* S)
    {d e : ℕ} (hde : e = d) (hd : d ∣ N) (he : e ∣ N) (φ : DirichletCharacter R d) (ψ : DirichletCharacter S e)
    (h : DirichletCharacter.changeLevel he ψ = (DirichletCharacter.changeLevel hd φ).ringHomComp f) (a : ℕ) :
    ψ (a : ZMod e) = f (φ (a : ZMod d)) := by
  subst hde
  have hc : (DirichletCharacter.changeLevel hd φ).ringHomComp f = DirichletCharacter.changeLevel hd (φ.ringHomComp f) := by
    ext u
    simp [MulChar.ringHomComp_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have hψ : ψ = φ.ringHomComp f := DirichletCharacter.changeLevel_injective hd (h.trans hc)
  subst hψ
  simp [MulChar.ringHomComp_apply]

theorem UpperTheory.V.Bern.b_condmap :
    ∀ {R S : Type} [CommRing R] [CommRing S] {N : ℕ} [NeZero N] (f : R →+* S), Function.Injective f → ∀ χ : DirichletCharacter R N, DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor ∧ (∀ a : ℕ, primVal (χ.ringHomComp f) a = f (primVal χ a)) ∧ (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
  intro R S _ _ N _ f hf χ
  have hker : (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
    ext u
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.ringHomComp_apply]
    constructor
    · intro h
      exact hf (h.trans (map_one f).symm)
    · intro h
      rw [h, map_one]
  have hset : DirichletCharacter.conductorSet (χ.ringHomComp f) = χ.conductorSet := by
    ext d
    simp only [DirichletCharacter.mem_conductorSet_iff]
    constructor
    · intro h
      have h' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
      rw [hker] at h'
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'
    · intro h
      have h' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
      rw [← hker] at h'
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'
  have hcond : DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor := by
    unfold DirichletCharacter.conductor
    rw [hset]
  refine ⟨hcond, ?_, hker⟩
  intro a
  unfold primVal
  exact change_level_value_eq f hcond χ.conductor_dvd_level (DirichletCharacter.conductor_dvd_level (χ.ringHomComp f))
    χ.primitiveCharacter (DirichletCharacter.primitiveCharacter (χ.ringHomComp f))
    (by rw [DirichletCharacter.changeLevel_primitiveCharacter, DirichletCharacter.changeLevel_primitiveCharacter]) a
