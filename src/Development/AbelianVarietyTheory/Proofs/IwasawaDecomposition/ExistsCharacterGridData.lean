module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NFunAddOneLtEExpAddCen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAuxiliaryHeckeCharacterToricListOfGridStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.GridLg

theorem lamOf_ok (D : D7) {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (cDep b : ℝ) (G : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩)
    (w0 : HeightOneSpectrum (𝓞 D.host.E)) (h : GlobalTheory.LamTie.PlacesOk D.host (AbsolutelyIrreducibleSpan.q0 D) w0) :
    (GlobalTheory.BigTop.Fun.lamOf G).Ok := by
  classical
  refine ⟨⟨?_, h.distinct, h.splits⟩, GlobalTheory.T.lamOf_chi_is_chosen_hecke_character_of_placesOk D L _ G w0 h, fun j a g => ?_⟩
  · have h1 := G.pl.basePlace_over_qZero
    have h2 := G.pl.w_over G.pl.v0 (Finset.mem_insert_self _ _)
    show ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w G.pl.v0).asIdeal
    have h3 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F) ∈ (G.pl.w G.pl.v0).asIdeal := by
      rw [← h2] at h1; exact h1
    rwa [map_natCast] at h3
  · exact GlobalTheory.BigTop.Fun.nFun_add_one_lt_eExp_add_cen 1 j a g

end GlobalTheory.HeightCounting.Up.GridLg

end
