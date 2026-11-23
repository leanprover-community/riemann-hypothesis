module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.DepthDrop
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.PrimeEqOfMemPrimeIdeal
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.depth :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ {t : T} {p : GlobalTheory.ChiGrid.Pair T} (d : FinDatum G t p), d.P = locPl G t →
      ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away G t w → ∀ k : ℕ, 0 < k → IsCosetDatum k d →
      ∃ k' : ℕ, 0 < k' ∧ IsCosetDatum k' d ∧ padicValNat l k' ≤ padicValNat l k ∧ (l ∣ k' → GlobalTheory.NormSum.SplitIn D l) := by
  classical
  intro D T L sc G large₂ hS t p d hP w l hl hlw hA k hk hc
  by_cases h : ∃ PP ∈ d.P, ((l : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal
  · obtain ⟨PP, hPP, hlPP⟩ := h
    have key : ((l : ℕ) : 𝓞 D.host.F) ∈ (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal := by
      rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_under, map_natCast]
      exact hlPP
    have hsplit : GlobalTheory.NormSum.SplitIn D l := by
      rw [hP] at hPP
      unfold locPl at hPP
      rcases Finset.mem_union.mp hPP with h0 | hQ
      · unfold GlobalTheory.ChiGrid.Places.W0 at h0
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h0
        rw [G.pl.w_over v hv] at key
        exact UpperTheory.WildA.small_set_primes_split large₂ hS v hv l hl key
      · rcases hA PP hQ with hS0 | hno
        · exact UpperTheory.WildA.small_set_primes_split large₂ hS _ hS0 l hl key
        · exact absurd hlw (hno l hl hlPP)
    exact ⟨k, hk, hc, le_rfl, fun _ => hsplit⟩
  · obtain ⟨k', hk', hnd, hc'⟩ := UpperTheory.WildA.depthDrop d l hl (fun w hw hlw' => h ⟨w, hw, hlw'⟩) k hk hc
    refine ⟨k', hk', hc', ?_, fun hd => absurd hd hnd⟩
    rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hnd]
    exact Nat.zero_le _
