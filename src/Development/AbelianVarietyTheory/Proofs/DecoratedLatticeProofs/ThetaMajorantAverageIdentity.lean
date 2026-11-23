module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.IkedaK

variable {D : D7}

theorem bdd_om_compact {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {P : Set (GA D S × GA D T)}
    (hP : IsCompact P) : ∃ C : ℝ, ∀ p ∈ P, ∀ x, ‖om p f x‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  have hc := GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hW f hf
  obtain ⟨C, hC⟩ := (hP.prod hK).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun p hp x => ?_⟩
  obtain ⟨γ, ⟨γ', rfl⟩, hx⟩ := hKc x
  have hq := (hW.om_pres p f hf).quasi γ' x
  have e : (((incA D).toAddMonoidHom.mapMatrix (m := Fin T.rank) (n := Fin S.rank)) γ') = ratW T S γ' := rfl
  rw [e] at hx
  have h1 := hW.std.1.2.1 (-(symplOH S T (ratW T S γ') x))
  have := hC (p, ratW T S γ' + x) ⟨hp, hx⟩
  simp only at this
  rw [hq, norm_mul, h1, one_mul] at this
  exact this

theorem om_mul_apply {S T : HSp D} (om : WRep S T) (p q : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om q f) = om (p * q) f := by
  rw [map_mul]; rfl

theorem weilRepUnitaryPair_left_apply_right {S T : HSp D} (om : WRep S T) (g : GA D S) (k : GA D T) (f : WO S T → ℂ) :
    om (g, 1) (om (1, k) f) = om (g, k) f := by
  rw [om_mul_apply]; congr 1; ext <;> simp

theorem weilRepUnitaryPair_right_apply_left {S T : HSp D} (om : WRep S T) (g : GA D S) (k : GA D T) (f : WO S T → ℂ) :
    om (1, k) (om (g, 1) f) = om (g, k) f := by
  rw [om_mul_apply]; congr 1; ext <;> simp

end GlobalTheory.IkedaK
