module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CwShift
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.VacAnn
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

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fkD :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F) (N : Submodule ℂ (S4 F)), N ≤ Vac δ → ∀ m w i, ∀ φ ∈ O.Fk N m, O.d w i φ ∈ O.Fk N (m + 1) := by
  intro F _ _ _ δ O N hN m
  obtain ⟨hmono, hx, -⟩ := UpperTheory.ConvolutionTheory.R2.Fo.fkBasic F O
  induction m with
  | zero =>
    intro w i φ hφ
    have hφ' : φ ∈ N := hφ
    rw [UpperTheory.ConvolutionTheory.R2.Fo.vacAnn F δ O φ (hN hφ') w i]
    exact Submodule.smul_mem _ _ (hx N 0 w i φ hφ)
  | succ m ih =>
    intro w i
    have hle : O.Fk N (m + 1) ≤ (O.Fk N (m + 1 + 1)).comap (O.d w i) := by
      change O.Fk N m ⊔ ⨆ w', ⨆ j, (O.Fk N m).map (O.x w' j) ≤ _
      refine sup_le ?_ (iSup_le fun w' => iSup_le fun j => ?_)
      · intro ψ hψ
        exact hmono N N le_rfl (m + 1) (m + 1 + 1) (Nat.le_succ _) (ih w i ψ hψ)
      · rw [Submodule.map_le_iff_le_comap]
        intro ψ hψ
        change O.d w i (O.x w' j ψ) ∈ O.Fk N (m + 1 + 1)
        have hc := congrArg (fun T : Module.End ℂ (S4 F) => T ψ) (UpperTheory.ConvolutionTheory.R2.Fo.weyl F O w w' i j).2
        have hc' : O.d w i (O.x w' j ψ) = O.x w' j (O.d w i ψ) + (if w = w' ∧ i = j then (1 : Module.End ℂ (S4 F)) else 0) ψ := hc
        rw [hc']
        refine Submodule.add_mem _ (hx N (m + 1) w' j _ (ih w i ψ hψ)) ?_
        split_ifs
        · exact hmono N N le_rfl m (m + 1 + 1) (by omega) hψ
        · exact Submodule.zero_mem _
    exact fun φ hφ => hle hφ
