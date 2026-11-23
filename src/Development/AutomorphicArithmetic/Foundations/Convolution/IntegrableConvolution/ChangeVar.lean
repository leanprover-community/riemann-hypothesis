module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

open MeasureTheory

private theorem measurePreserving_chainCoords {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] (m : ℕ) :
    ∀ δ : Fin m → G,
    MeasurePreserving (fun x : Fin (m + 1) → G => (x 0, fun i : Fin m => (x i.castSucc)⁻¹ * δ i * x i.succ))
      (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ => μ)) := by
  induction m with
  | zero =>
    intro δ
    have h := measurePreserving_piFinSuccAbove (fun _ : Fin 1 => μ) 0
    convert h using 1
    funext x
    refine Prod.ext rfl ?_
    funext i
    exact i.elim0
  | succ m ih =>
    intro δ
    have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 2) => μ) 0
    have h2 := (MeasurePreserving.id μ).prod (ih (Fin.tail δ))
    have h3 : MeasurePreserving
        (fun p : G × (G × (Fin m → G)) => (id p.1, (p.1⁻¹ * δ 0 * p.2.1, p.2.2)))
        (μ.prod (μ.prod (Measure.pi fun _ => μ))) (μ.prod (μ.prod (Measure.pi fun _ => μ))) := by
      refine MeasurePreserving.skew_product (g := fun (a : G) (q : G × (Fin m → G)) => (a⁻¹ * δ 0 * q.1, q.2))
        (MeasurePreserving.id μ) ?_ (Filter.Eventually.of_forall fun a => ?_)
      · unfold Function.uncurry
        fun_prop
      · exact ((measurePreserving_mul_left μ (a⁻¹ * δ 0)).prod (MeasurePreserving.id _)).map_eq
    have h4 := (MeasurePreserving.id μ).prod
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm
    have h := h4.comp (h3.comp (h2.comp h1))
    convert h using 1
    funext x
    refine Prod.ext rfl ?_
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]

private theorem tele {G : Type} [Group G] (m : ℕ) : ∀ (δ : Fin m → G) (x : Fin (m + 1) → G),
    (List.ofFn fun i : Fin m => (x i.castSucc)⁻¹ * δ i * x i.succ).prod =
      (x 0)⁻¹ * (List.ofFn δ).prod * x (Fin.last m) := by
  induction m with
  | zero => intro δ x; simp
  | succ m ih =>
    intro δ x
    have h := ih (fun i => δ i.succ) (fun i => x i.succ)
    simp only [List.ofFn_succ, List.prod_cons, ← Fin.succ_castSucc]
    rw [h]
    simp [mul_assoc]

theorem UpperTheory.ConvolutionTheory.L1.changeVar :
    UpperTheory.ConvolutionTheory.L1.ChangeVar := by
  intro G _ _ _ _ _ _ _ _ μ _ m δ
  refine ⟨measurePreserving_chainCoords μ m (fun i => δ i.castSucc), fun x => ?_⟩
  funext i
  unfold UpperTheory.ConvolutionTheory.L1.fib
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, tele m (fun i => δ i.castSucc) x, List.ofFn_succ' δ]
    simp [mul_assoc]
  · rw [Fin.snoc_castSucc, Fin.coeSucc_eq_succ]
