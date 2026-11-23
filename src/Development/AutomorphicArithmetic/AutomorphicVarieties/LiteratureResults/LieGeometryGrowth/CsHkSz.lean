module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAltSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCompSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsFlowSz
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

@[expose] public section

open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.hkSz :
    HkSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨hA, C₁, hC₁⟩ := altSz V F q k (1 + c)
  obtain ⟨C₂, h₂, hC₂⟩ := compSz V (V →L[ℝ] V) ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)
  obtain ⟨C₃, h₃, hC₃⟩ := compSz V V (V [⋀^Fin (q + 1)]→L[ℝ] F) k (1 + c)
  let L : (V [⋀^Fin (q + 1)]→L[ℝ] F) →L[ℝ] (V →L[ℝ] V [⋀^Fin q]→L[ℝ] F) :=
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap
  refine ⟨2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|), by positivity, ?_⟩
  intro W t w p b ht hW hWs hw hws
  obtain ⟨f1, f2, f3, f4⟩ := flowSz V k c W t p ht hW hWs
  have a1 : Sz k (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p (C₃ * b) :=
    hC₃ w _ p b f1 hw (fun i h1 h2 => f4 i h1 (h2.trans (Nat.le_succ k))) hws
  have s1 : ContDiffAt ℝ ∞ (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p := hw.comp p f1
  have a2 := (appSz V _ _ k p).2.1 L _ _ s1 a1
  have s2 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y))) p := L.contDiff.contDiffAt.comp p s1
  have a3 := (appSz V _ _ k p).1 _ W _ _ s2 hW a2 ((hWs.of_le (Nat.le_succ k)).mono (le_abs_self c))
  have s3 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y)) (W y)) p := s2.clm_apply hW
  have a4 := hC₂ _ _ p _ f2 hA.contDiffAt (fun i _ h2 => f3 i h2) ((hC₁ _ f3.norm_le).mono (le_abs_self C₁))
  have s4 := hA.contDiffAt.comp p f2
  have a5 := (appSz V _ _ k p).1 _ _ _ _ s4 s3 a4 a3
  have e : 2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|) * b =
      2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * (C₃ * b)) * |c|) := by ring
  rw [e]
  exact a5
