module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StageDict

theorem fst_isFinF_frames : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW), (∀ τ, (GlobalTheory.SquareComm.frSgn true FA).cart τ = -X.rA.s τ) →
    (∀ τ, FW.cart τ = X.rW.s τ) → X.Is ψ θ α β νH S → ∀ t, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t) := by
  intro D T A A' WW X ψ θ α β νH S FA FW hcA hcW hX t
  have hv := hX.isVac
  have hν : Formalism.L2.Theta.IsHeckeChar D (α t / β t) := by
    have h := (hX.weil t).hecT
    rw [← inv_div]
    refine ⟨?_, fun x => ?_⟩
    · exact continuous_inv.comp h.1
    · show ((β t / α t) _)⁻¹ = 1
      rw [h.2 x, inv_one]
  have hI : X.ideal S t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_
    rw [Ideal.zero_eq_bot]
    exact w.ne_bot
  obtain ⟨f₁, h1, h1t⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW (α t / β t) (X.e t) (S t) (X.ideal S t) X.vac
    hX.rigA hX.rigW hν (hX.idem t) hI hv
  have heq : X.f t = f₁ := by
    obtain ⟨⟨Tm, hT⟩, hall⟩ := hX.fst t
    rw [hall Tm hT, h1.2 Tm hT]
  have hft : IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (X.f t) := heq ▸ h1t
  refine ⟨hft, fun τ => ?_⟩
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.idem t)
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hv.1.1.1 hv.2.inf ho.infPart_eq ho.conj.infPart_eq
    (hX.fst t) hv.2.theta hft (hv.2.fock τ)
  rw [hcA τ, hcW τ]
  exact hF

end GlobalTheory.StageDict
