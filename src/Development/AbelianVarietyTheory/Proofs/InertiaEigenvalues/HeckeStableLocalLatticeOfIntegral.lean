module

import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LatStab

theorem jMt_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  apply Formalism.L2.jMt_injective <;> assumption

theorem latStable_of_latInt : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (w : D.what₂.places.Pl), LatInt D M (B.Qc j w) j h1 h2 w → LatStable B j w := by
  intro D M B j h1 h2 w hI v k hvk x hx
  classical
  obtain ⟨s, ϖ, hcj, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
  have hinj := jMt_injective D (D.what₂.muTw w) j
  let f : D.what₂.Mt (D.what₂.muTw w) j → D.what₂.MtL (D.what₂.muTw w) j := fun g =>
    if h : g ∈ Set.range (D.what₂.jMt (D.what₂.muTw w) j) then h.choose else 0
  have hf : ∀ g ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, D.what₂.jMt (D.what₂.muTw w) j (f g) = g := by
    intro g hg
    have h := hI.1 g hg
    simp only [f, dif_pos h]
    exact h.choose_spec
  have key : ∀ y ∈ genSet D (D.what₂.muTw w) j, B.hK j w v k (B.iV j w y) ∈ latLoc B j w := by
    intro y hy
    obtain ⟨c, hc0, hcE⟩ := hI.2 v k s ϖ hvk hcj hu _ hy
    have e1 := B.hL_def j w h1 h2 v k s ϖ hvk hcj hu y
    rw [hcE] at e1
    have e2 := (M (D.what₂.muTw w) j h1 h2).real_inj e1
    have e3 : B.hL j w v k y = ∑ g ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, c g • f g := by
      apply hinj

      rw [e2, map_sum]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_smulₛₗ, hf g hg]

    rw [B.hK_def, e3, map_sum]
    refine Submodule.sum_mem _ fun g hg => ?_
    rw [map_smulₛₗ]
    obtain ⟨o, ho⟩ := (B.ec_w j w (c g)).1 (hc0 g)
    rw [← ho, algebraMap_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨f g, ?_, rfl⟩)
    show D.what₂.jMt (D.what₂.muTw w) j (f g) ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen
    rw [hf g hg]; exact hg
  have hle : latLoc B j w ≤ (latLoc B j w).comap ((B.hK j w v k).restrictScalars (B.Oc j w)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact key y hy
  exact hle hx

end GlobalTheory.LatStab

end
