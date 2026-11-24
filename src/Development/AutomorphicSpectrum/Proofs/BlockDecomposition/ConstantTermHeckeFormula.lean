module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero

@[expose] public section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have key : ∀ S : Subgroup H, S = ⊤ → ((S.index : ℂ))⁻¹ * ∑ᶠ _ : H ⧸ S, c = c := by
    rintro S rfl
    haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
    haveI : Unique (H ⧸ (⊤ : Subgroup H)) := Unique.mk' _
    rw [finsum_unique, Subgroup.index_top]
    simp
  exact key _ (by ext k; simp [rStab])

theorem ctT_split_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E), IsSplitAt w → IsUnifV E w ϖ → ∀ (k : ℕ) (m : GLw a w × GLw b w), ctT h w ν ϖ k m = (ν ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) * (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) fun X => Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) := by
  intro E _ _ _ n a b h w ν ϖ hw hϖ k m
  have hT : UL n w = ⊤ := if_pos hw
  have hv : ∀ y : GLw n w, ((toSub (UL n w) y : UL n w) : GLw n w) = y := fun y => by
    have hy : y ∈ UL n w := hT ▸ Subgroup.mem_top y
    simp [toSub, hy]
  have hc : ∀ (x : GLw n w) (g : GlobalTheory.LFun.KGL w (n := n)),
      Tj ℂ n (Ov E w) ϖ k ((g : GLw n w)⁻¹ * x * g) = Tj ℂ n (Ov E w) ϖ k x := fun x g =>
    (Tj_mem_hecke (n := n) hϖ k).1 g⁻¹ g x
  unfold ctT ctMu ct
  congr 2
  congr 1
  funext X
  simp only [hv, hc]
  exact avg_const (H := GlobalTheory.LFun.KGL w (n := n)) _

end GlobalTheory.CompanionTheory.CtS

end
