module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.adicComplete
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RingKrullDimQuotientOfMemAssociatedPrimes

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem psBase_equiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (h : IsBase A) : IsBase B := by
  have hd : IsDomain A := h.dom
  have hn : IsIntegrallyClosed A := h.normal
  have hc : IsAdicComplete (maximalIdeal A) A := h.complete
  refine ⟨MulEquiv.isDomain A e.symm.toMulEquiv, IsIntegrallyClosed.of_equiv e, h.cm.of_ringEquiv e, ?_⟩
  have hm : Ideal.map e (maximalIdeal A) = maximalIdeal B := by
    ext x
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
      intro hu
      apply hy
      simpa using hu.map e.symm
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      intro hu
      apply hx
      simpa using hu.map e
  rw [← hm]
  exact (IsAdicComplete.congr_ringEquiv _ e).2 hc

private theorem psBase_cm (R : Type) [CommRing R] [IsLocalRing R] [IsDomain R]
    (h : ReciprocityTheory.CA.IsCM R) : ReciprocityTheory.CA.IsCM (PowerSeries R) := by
  haveI := h.1
  have hker : Ideal.span {(PowerSeries.X : PowerSeries R)} =
      RingHom.ker (PowerSeries.constantCoeff : PowerSeries R →+* R) := by
    ext f
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, PowerSeries.X_dvd_iff]
  have hsurj : Function.Surjective (PowerSeries.constantCoeff : PowerSeries R →+* R) :=
    fun a => ⟨PowerSeries.C a, by simp⟩
  let e : (PowerSeries R ⧸ Ideal.span {(PowerSeries.X : PowerSeries R)}) ≃+* R :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  haveI : IsLocalRing (PowerSeries R ⧸ Ideal.span {(PowerSeries.X : PowerSeries R)}) :=
    e.symm.isLocalRing
  refine ReciprocityTheory.CA.isCM_of_quotient_span_singleton (x := PowerSeries.X) ?_
    (mem_nonZeroDivisors_of_ne_zero PowerSeries.X_ne_zero) (h.of_ringEquiv e.symm)
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  simp

private theorem psBase_one (R : Type) [CommRing R] [IsLocalRing R] (h : IsBase R) :
    IsBase (PowerSeries R) := by
  haveI := h.dom
  haveI := h.normal
  haveI := h.cm.1
  haveI := h.complete
  exact ⟨inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries R,
    psBase_cm R h.cm, UpperTheory.V.abelian₂.adicComplete R⟩

theorem UpperTheory.V.AlgebraTools.Conn.psBase :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], IsBase O → ∀ n : ℕ, IsBase (MvPowerSeries (Fin n) O) := by
  intro O _ _ hO n
  induction n with
  | zero =>
    have hbij : Function.Bijective
        (MvPowerSeries.constantCoeff (σ := Fin 0) (R := O)) := by
      refine ⟨fun f g hfg => ?_, fun a => ⟨MvPowerSeries.C a, by simp⟩⟩
      ext d
      have hd : d = 0 := Subsingleton.elim _ _
      subst hd
      simpa using hfg
    exact psBase_equiv (RingEquiv.ofBijective _ hbij).symm hO
  | succ n ih =>
    exact psBase_equiv (MvPowerSeries.finSuccEquiv O n).toRingEquiv.symm (psBase_one _ ih)
