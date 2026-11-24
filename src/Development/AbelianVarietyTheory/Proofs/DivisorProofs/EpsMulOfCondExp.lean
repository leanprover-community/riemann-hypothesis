module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

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

namespace GlobalTheory.SqStepArith

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt)

theorem chrW_chs {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (x : (Fv D.host.F v)ˣ) :
    chrW (GlobalTheory.SqStep.chs G i j t).ν τ x = (nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom x) := by
  have e : (GlobalTheory.SqStep.chs G i j t).ν = G.nu t i (j + 1) := by
    show (Lc.mu t (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  show GlobalTheory.LFun.locChar (GlobalTheory.SqStep.chs G i j t).ν _ _ = _
  rw [e, GlobalTheory.LFun.locChar_eq_of_chrEq (chrEq_nu G t i j hL)]

theorem eps_mul_of_condExp {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (ν₀ ξ : (Fv F v)ˣ →* ℂˣ) (s : (Fv F v)ˣ) (z : ℤ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀) :
    (ν₀ s : ℂ) * eps ψ ν₀ z * gauss ψ (ν₀ * ξ) =
      (((ξ (s * unifAt v ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀))⁻¹ : ℂˣ) : ℂ) * gauss ψ ν₀ *
        (((ν₀ * ξ) s : ℂ) * eps ψ (ν₀ * ξ) z) := by
  unfold eps
  rw [h]
  simp only [MonoidHom.mul_apply, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, mul_inv, Units.val_inv_eq_inv_val]
  have h1 : (ξ s : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : (ξ (unifAt v) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
  ring

theorem chs_T_base {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) : (GlobalTheory.SqStep.chs G i j μ₀).T = G.pl.S0 := by
  classical
  have hQ : Lc.Q μ₀ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
    have h := (hL.Q_ram μ₀ PP).2 (Or.inl hPP)
    apply h
    rw [hL.xi_base]
    intro x _
    rfl
  have htw : twPl G μ₀ = ∅ := by
    unfold twPl locPl
    rw [hQ, Finset.union_empty]
    exact Finset.filter_false_of_mem fun w hw h => h hw
  show G.pl.S0 ∪ (twPl G μ₀).image _ = _
  rw [htw, Finset.image_empty, Finset.union_empty]

end GlobalTheory.SqStepArith
