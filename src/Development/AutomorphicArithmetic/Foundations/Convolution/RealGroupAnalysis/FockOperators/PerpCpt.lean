module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.perpCpt :
    ∀ (F : Type) [Field F] [NumberField F] (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)), ∃ K : Set (FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
    ∀ x : A F, (∀ a : A F, a.1 = 0 → a.2 ∈ Λ → ψ (a * x) = 1) → x.2 ∈ K := by
  intro F _ _ Λ
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset (K := F) (W := (Λ : Set (FiniteAdeleRing (𝓞 F) F)))
    (Λ.isOpen.mem_nhds Λ.zero_mem)
  refine ⟨(idealFiniteAdeles (traceDualIdeal F J) : Set (FiniteAdeleRing (𝓞 F) F)),
    isCompact_idealFiniteAdeles _, fun x hx => ?_⟩
  refine (forall_finiteAdelicChar_mul_eq_one_iff J x.2).1 fun y hy => ?_
  have h := hx (finiteAdeleInr y) rfl (hJ hy)
  have e : finiteAdeleInr y * x = finiteAdeleInr (y * x.2) := by
    refine Prod.ext ?_ rfl
    change (0 : _) * x.1 = 0
    exact zero_mul _
  rw [e] at h
  rw [finiteAdelicChar_apply]
  exact Circle.ext h
