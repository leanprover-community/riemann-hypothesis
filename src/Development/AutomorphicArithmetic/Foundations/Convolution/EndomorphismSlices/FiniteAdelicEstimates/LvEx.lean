module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.lvEx :
    UpperTheory.Zero.ConvolutionTheory.EB.LvEx := by
  intro E _ _ _ a b Z φ h
  have key : ∀ w : Pl E, ∃ (A : Subgroup (GLw a w)) (B : Subgroup (GLw b w)),
      IsOpen (A : Set (GLw a w)) ∧ IsOpen (B : Set (GLw b w)) ∧ A ≤ KGL w (n := a) ∧ B ≤ KGL w (n := b) ∧
      (w ∉ Z → A = KGL w (n := a) ∧ B = KGL w (n := b)) ∧ (w ∈ Z → IsHecke (A.prod B) (φ w)) := by
    intro w
    by_cases hw : w ∈ Z
    · obtain ⟨K', ho, hle, hH⟩ := h w hw
      refine ⟨K'.comap (MonoidHom.inl _ _), K'.comap (MonoidHom.inr _ _), ?_, ?_, ?_, ?_,
        fun h' => absurd hw h', fun _ => ⟨hH.1, ?_⟩⟩
      · exact ho.preimage (continuous_id.prodMk continuous_const)
      · exact ho.preimage (continuous_const.prodMk continuous_id)
      · intro x hx
        exact (hle hx).1
      · intro y hy
        exact (hle hy).2
      · rintro ⟨x, y⟩ ⟨hx, hy⟩ g
        have hxy : ((x, y) : GLw a w × GLw b w) ∈ K' := by
          have := K'.mul_mem hx hy
          simpa using this
        exact hH.2 _ hxy g
    · exact ⟨KGL w (n := a), KGL w (n := b), (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1,
        (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1, le_rfl, le_rfl,
        fun _ => ⟨rfl, rfl⟩, fun h' => absurd h' hw⟩
  choose A B hA hB hA' hB' hoff hfix using key
  exact ⟨⟨A, B, hA, hB, hA', hB', hoff⟩, hfix⟩
