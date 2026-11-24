module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem co_mvps_equiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (h : IsAdicComplete (maximalIdeal A) A) :
    IsAdicComplete (maximalIdeal B) B := by
  rw [← map_ringEquiv_maximalIdeal e, IsAdicComplete.congr_ringEquiv]
  exact h

private theorem co_mvps_fin (R : Type) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact co_mvps_equiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm inferInstance
  | succ n ih =>
    exact co_mvps_equiv (finSuccEquiv R n).toRingEquiv.symm
      (UpperTheory.V.abelian₂.adicComplete (MvPowerSeries (Fin n) R))

theorem UpperTheory.V.Alg.co_mvps :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : Type) [Finite σ], IsCO O (MvPowerSeries σ R) := by
  intro O _ _ R _ _ hR σ _
  have hc : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hl : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hn : IsNoetherianRing R := hR.toIsNoetherian
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  refine
    { toIsLocalRing := inferInstance
      toIsNoetherian := MvPowerSeries.isNoetherianRing R
      complete := co_mvps_equiv (renameEquiv R e.symm).toRingEquiv (co_mvps_fin R n)
      isLocalHom := ⟨fun a ha => ?_⟩
      res_surj := fun x => ?_ }
  · have h := isUnit_constantCoeff _ ha
    rw [MvPowerSeries.algebraMap_apply, constantCoeff_C] at h
    exact IsLocalHom.map_nonunit a h
  · obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (constantCoeff x)
    refine ⟨a, fun h => ha ?_⟩
    have h2 := isUnit_constantCoeff _ h
    rwa [map_sub, MvPowerSeries.algebraMap_apply, constantCoeff_C] at h2
