module

public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjLocVal

theorem value_at_conj_place : ∀ (D : D7) (PP : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (y : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e PP → ϖ ∈ PP.asIdeal → ϖ ∉ PP.asIdeal ^ 2 → ChrEq c χ → χ.UnrAt (Formalism.L2.DIV.conjPl PP) → (y : AE D) = 1 + cA D e * (incA D (star (ϖ : D.host.E)) ^ n - 1) → ((c y : Circle) : ℂ) = ((χ.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
  intro D PP e ϖ c χ n y he h1 h2 hc hU hy
  obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := Formalism.IndefR.Fin.LevelGroupLemmas.isIdemAt_conj he
  have hpl : Formalism.L2.JoinChr.IsPlIdem D (cA D e) (Formalism.L2.DIV.conjPl PP) := ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (zero_mem _)
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  have hs0 : star (ϖ : D.host.E) ≠ 0 := star_ne_zero.2 hϖE
  set k : D.host.Eˣ := Units.mk0 (star (ϖ : D.host.E)) hs0 with hk
  have hy' : (y : AE D) = Formalism.L2.JoinChr.locE D (cA D e) ((k ^ n : D.host.Eˣ) : D.host.E) := by
    rw [hy, Formalism.L2.JoinChr.locE, Units.val_pow_eq_pow_val, map_pow]
    rfl
  rw [hc.2 _ _ hpl (k ^ n) y hy', map_pow, Units.val_pow_eq_pow_val]
  congr 1
  have hmem : Formalism.L2.DIV.starO ϖ ∈ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO ϖ) ∈ PP.asIdeal
    rw [Formalism.L2.DIV.starO_starO]; exact h1
  have hnsq : Formalism.L2.DIV.starO ϖ ∉ (Formalism.L2.DIV.conjPl PP).asIdeal ^ 2 := by
    intro hm
    have hm' := Ideal.le_comap_pow (f := Formalism.L2.DIV.starOHom) (K := PP.asIdeal) 2 hm
    rw [Ideal.mem_comap] at hm'
    apply h2
    have : Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO ϖ) = ϖ := Formalism.L2.DIV.starO_starO ϖ
    rwa [this] at hm'
  have hunif : Formalism.L2.Host.IsUnifAt (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) := by
    show Valued.v (((star (ϖ : D.host.E) : D.host.E)) : (Formalism.L2.DIV.conjPl PP).adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← Formalism.L2.DIV.starO_coe,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact GlobalTheory.LatIntFacts.intValuation_uniformiser _ hmem hnsq
  have hval : χ.loc (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) = χ.val (Formalism.L2.DIV.conjPl PP) := by
    have hu : Formalism.L2.Host.IsUnitAt (Formalism.L2.DIV.conjPl PP)
        (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k * (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.unif (Formalism.L2.DIV.conjPl PP)))⁻¹) := by
      have h2' := Formalism.L2.Host.unif_spec (Formalism.L2.DIV.conjPl PP)
      unfold Formalism.L2.Host.IsUnitAt
      unfold Formalism.L2.Host.IsUnifAt at hunif h2'
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hunif, h2']
      exact mul_inv_cancel₀ (by simp)
    have h3 := hU _ hu
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact h3
  show ((χ.loc (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) : ℂˣ) : ℂ) = _
  rw [hval]

end GlobalTheory.ConjLocVal
