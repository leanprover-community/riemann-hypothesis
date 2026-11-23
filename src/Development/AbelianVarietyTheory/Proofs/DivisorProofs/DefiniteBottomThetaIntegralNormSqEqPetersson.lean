module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.NormBigDict

theorem normSq_eq_petersson : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (P : PolF D WW.rank A.rank)
    (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)), ν.IsHaarMeasure → IsFundamentalDomain (GQ WW) 𝓕 ν →
    ∃ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure ∧
      ((∫ h in 𝓕, ‖X.I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) =
        petersson WW ν (up ((X.ω t).toSgn true) m (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) fun _ => 1) (up ((X.ω t).toSgn true) m (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) fun _ => 1) := by
  intro D T L sc G W i j A A' WW X hX t P ν 𝓕 hν h𝓕
  have h := hX.is
  obtain ⟨ν₁, hν₁, hfd, hint⟩ := GlobalTheory.SgnIdent.meas_sgn true A X.m X.fd h.meas.1 h.meas.2
  refine ⟨ν₁, hν₁, ?_⟩
  have hW := h.weil t
  have hΦ := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := GlobalTheory.Grid.neg A) h.isVac.1 h.isVac.2.inf (fun τ => -X.rA.s τ)
    X.rA.B X.rW.s X.rW.B (GlobalTheory.ConstRatio.theta_f h t).1 P
  set Φ := pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P with hΦd
  set om := (X.ω t).toSgn true with hom

  have hg : ∀ y : GA D WW, AutomorphicL2Unitary.LeftInv (GQ (GlobalTheory.Grid.neg A)) (fun g => thetaKO om g y Φ * (fun _ => (1 : ℂ)) g) := by
    intro y γ hγ g
    show om (γ * g, y) Φ 0 * 1 = om (g, y) Φ 0 * 1
    have e : ((γ * g, y) : GA D (GlobalTheory.Grid.neg A) × GA D WW) = (γ, 1) * (g, y) := by rw [Prod.mk_mul_mk, one_mul]
    rw [e, map_mul, Module.End.mul_apply]
    rw [hW.om_aut γ hγ 1 (GQ WW).one_mem _ (hW.om_pres _ _ hΦ)]

  have hup : ∀ y, up om ν₁ Φ (fun _ => 1) y = X.I W.ψ W.θ t P y := by
    intro y
    haveI := hν₁
    simp only [up, AutomorphicL2Unitary.autMeasure]
    rw [integral_quotMeasure hfd]
    simp only [(hg y).descend_mk]
    simp only [mul_one]
    exact (hint fun g => thetaKO (X.ω t) g y Φ).2

  have hinv : AutomorphicL2Unitary.LeftInv (GQ WW) (up om ν₁ Φ fun _ => 1) := by
    intro γ hγ y
    rw [hup, hup]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.I, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker]
    congr 1
    funext g
    exact GlobalTheory.ThetaMean.leftInv_theta hW hΦ ((GlobalTheory.Grid.ofSgn true A).symm g) γ hγ y
  haveI := hν
  simp only [petersson, pet]
  rw [integral_quotMeasure h𝓕]
  simp only [hinv.descend_mk, hup, Complex.mul_conj, ← Complex.sq_norm]
  exact (integral_ofReal).symm

end GlobalTheory.NormBigDict

end
