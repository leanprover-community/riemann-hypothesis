module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.HeightCounting.Up.LocEx

theorem exists_loc_of_thetaT {D : D7} {M : MtFam D} (T : NormalizedLocalCompatibility D M) {v : D.what₂.places.Pl} (hv : TwistedAt D v) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hne : ∃ f, D.what₂.thetaT (D.what₂.muTw v) j f ≠ 0) :
    ∃ i : D.nd.Loc, D.nd.w i = v ∧ D.nd.j i = j := by
  obtain ⟨f, hf⟩ := hne
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw v) j)
  have hidx : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw v) j)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h3 := (D.what₂.jMt_basis (D.what₂.muTw v) j b).2
    rw [Set.range_eq_empty, Submodule.span_empty] at h3
    exact hf ((Submodule.mem_bot ℂ).1 (h3 ▸ Submodule.mem_top))
  obtain ⟨k⟩ := hidx
  haveI : Nontrivial (T.B.V j v) := ⟨⟨_, 0, (T.B.iV_basis j v b).1.ne_zero k⟩⟩
  haveI : Nontrivial (Formalism.L2.heckeAlg T.B j v) := inferInstance
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (Formalism.L2.heckeAlg T.B j v)
  obtain ⟨i, hi, -⟩ := T.mx_all j v h1 h2 hv I hI
  obtain ⟨ej, ew⟩ := (D.nd.locs_mem _ _ _).1 hi
  exact ⟨i, ew, ej⟩

theorem thetaT_ne_of_lamTr {D : D7} {μ : D.what₂.Tup} {j : ℕ} {σ : D.what₂.FT} (hpos : 0 < DV.lamTr D μ j σ) :
    ∃ f ∈ D.what₂.isot j σ, D.what₂.thetaT μ j f ≠ 0 := by
  by_contra h
  push_neg at h
  have hT : D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ ((D.what₂.isot j σ).starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) = 0 := by
    ext y
    simp [h _ ((D.what₂.isot j σ).starProjection_apply_mem y)]
  unfold DV.lamTr at hpos
  rw [hT, map_zero, Complex.zero_re, zero_div] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.HeightCounting.Up.LocEx

end
