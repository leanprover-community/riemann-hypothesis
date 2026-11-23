module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LevelWeightSumBound
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

theorem _root_.GlobalTheory.T.level_weight_sum_bound : ∀ (n M : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (i : Fin M) (h : ∑ j, sz lev M j = n),
    ‖∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), ((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ) -
      ((sz lev M i : ℂ) * ((modExp (fun j => Fin (sz lev M j)) i : ℂ) / 2))‖ ≤ 3 * (n : ℝ) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.norm_cluster_sum_le | exact GlobalTheory.CompanionTheory.RgCOBlock.norm_cluster_sum_le | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.norm_cluster_sum_le <;> assumption)
