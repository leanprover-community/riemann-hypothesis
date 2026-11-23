module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GrpLevel
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NLevel
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.level :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (Om : G1 F →* Module.End ℂ (S4 F)), IsOm δ η Om → ∀ φ, ∀ᶠ g in 𝓝 (1 : G1 F), InfOne g → Om g φ = φ := by
  intro F _ _ δ η Om hOm φ
  let H : Subgroup (G1 F) :=
    { carrier := {g | Om g φ = φ}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        have h : Om a⁻¹ (Om a φ) = φ := by
          rw [← Module.End.mul_apply, ← map_mul]; simp
        rwa [ha] at h }
  have key : ∀ (f : S4 F) (b : A F), (∀ v, ψ (b * q4 δ v) * f.1 v = f.1 v) → Om (nU b) f = f := by
    intro f b h
    exact Subtype.ext (funext fun v => (hOm.n b f v).trans (h v))
  have h : ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → nU b ∈ H ∧ wW F * nU b * (wW F)⁻¹ ∈ H := by
    refine ((nLevel F δ φ).and (nLevel F δ (Om (wW F)⁻¹ φ))).mono fun b hb h0 => ⟨key φ b (hb.1 h0), ?_⟩
    show Om (wW F * nU b * (wW F)⁻¹) φ = φ
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, key _ _ (hb.2 h0),
      ← Module.End.mul_apply, ← map_mul]
    simp
  exact grpLevel F H h
