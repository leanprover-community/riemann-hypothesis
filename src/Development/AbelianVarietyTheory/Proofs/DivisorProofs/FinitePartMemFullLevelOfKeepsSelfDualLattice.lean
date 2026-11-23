module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCompactDualHaar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PolyGrowthStatementPfB

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.FullLevel

theorem finE_mem_lev_of_isKM : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Links.IsSDFrame V β Λ 1 → V.rank ≤ L.r → L.P.H = ⊤ → ∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L := by
  intro D V β Λ L hΛ hr hP h hK
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hΛ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hk : GlobalTheory.Member.FinCong V 1 h := by
    intro z hz
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1] at hz ⊢
    exact hK.2.1 z hz
  have hc : ∀ a : GA D V, GlobalTheory.Member.FinCong V 1 a → ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (1 : ℕ) • y := by
    intro a ha
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap Λ 1 _ ha
  have hc' := hc _ (GlobalTheory.Member.PrincLevel.finCong_inv hk)
  rw [map_inv] at hc'
  obtain ⟨y, hy, -⟩ := GlobalTheory.PrincInLevel.exists_int (Formalism.L2.Herm.intAf D.host.F D.host.E) β (Formalism.IndefR.Lev.finE V h)
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ) 1 hfr (hc h hk) hc'
  have hS : Formalism.IndefR.Lev.finE V h ∈ Formalism.L2.DIV.St β := ⟨y, hy⟩
  have hU : Formalism.IndefR.Lev.finE V h ∈ Formalism.L2.DIV.UA D.sp.cm V.gram := GlobalTheory.LevSplit.finE_mem_UA V h
  have hb : ∀ a : Fin V.rank, a.val < L.r := fun a => lt_of_lt_of_le a.2 hr
  refine Formalism.L2.DIV.mem_lev.2 ⟨Formalism.L2.DIV.mem_parLev.2 ⟨hU, hS, fun PP _ => ?_, fun PP _ => ?_⟩, ?_⟩
  · intro i j hij
    exfalso
    simp only [Formalism.L2.DIV.blkOf, if_pos (hb i), if_pos (hb j)] at hij
    exact lt_irrefl _ hij
  · intro i j hij
    exfalso
    simp only [Formalism.L2.DIV.blk2, if_pos (hb i), if_pos (hb j)] at hij
    exact lt_irrefl _ hij
  · rw [hP]; exact Subgroup.mem_top _

end GlobalTheory.CovTop.VolUp.FullLevel
