module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.ZetaDenom

theorem isRayL_top_wideInd_iff : ∀ {F : Type} [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ),
    IsRayL (⊤ : Ideal (𝓞 F)) (wideInd C) Z ↔ IsClassZeta C Z := by
  intro F _ _ C Z
  refine and_congr_right fun _ => forall₂_congr fun s _ => ?_
  let g : IdealsIn C → {I : Ideal (𝓞 F) // CoprimeTo F ⊤ I} :=
    fun I => ⟨I.1.1, nonZeroDivisors.coe_ne_zero I.1, sup_top_eq _⟩
  have hg : Function.Injective g := fun I J h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : {I : Ideal (𝓞 F) // CoprimeTo F ⊤ I} => x.1) h))
  rw [← hg.hasSum_iff (f := fun I : {I : Ideal (𝓞 F) // CoprimeTo F ⊤ I} =>
    (wideInd C I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) fun I hI => by
      have : cls I.1 ≠ C := fun h => hI ⟨⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2.1⟩,
        by rw [← h, cls_of_ne_bot I.2.1]⟩, rfl⟩
      simp [wideInd, this]]
  refine iff_of_eq (congrArg (HasSum · (Z s)) (funext fun I => ?_))
  have h1 : cls (I.1 : Ideal (𝓞 F)) = C := by
    rw [cls_of_ne_bot (nonZeroDivisors.coe_ne_zero I.1)]
    exact I.2
  simp [g, wideInd, h1]

end GlobalTheory.ZetaDenom
