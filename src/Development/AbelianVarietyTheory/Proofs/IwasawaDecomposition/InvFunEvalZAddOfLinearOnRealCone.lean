module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

theorem evalZ_eq_sum_of_toReal_eq_addcone {O : Type} [CommRing O] (ψ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {v : Fin m → LinearMap.BilinForm ℤ X} (hv : ψ.LinearOn v)
    {β : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (h : toReal β = ∑ i, c i • toReal (v i)) : ψ.evalZ β = ∑ i, c i * ψ.evalZ (v i) := by
  rw [← hv c hc]
  unfold InvFun.evalZ
  congr 1
  funext a b
  have := LinearMap.congr_fun₂ h a b
  simpa [LinearMap.sum_apply] using this

theorem evalZ_add_of_linearOn_inRCone (O : Type) [CommRing O] (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X) (hv : ψ.LinearOn v)
    (β x : LinearMap.BilinForm ℤ X) (hβ : InRCone v β) (hx : InRCone v x) :
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x := by
  obtain ⟨a, ha, hβ⟩ := hβ
  obtain ⟨b, hb, hx⟩ := hx
  have hs : toReal (β + x) = ∑ i, (a i + b i) • toReal (v i) := by
    have : toReal (β + x) = toReal β + toReal x := LinearMap.ext₂ fun s t => by simp
    rw [this, hβ, hx, ← Finset.sum_add_distrib]
    simp only [add_smul]
  rw [evalZ_eq_sum_of_toReal_eq_addcone ψ hv (fun i => add_nonneg (ha i) (hb i)) hs,
    evalZ_eq_sum_of_toReal_eq_addcone ψ hv ha hβ, evalZ_eq_sum_of_toReal_eq_addcone ψ hv hb hx,
    ← Finset.sum_add_distrib]
  simp only [add_mul]

end GlobalTheory.PolFan.Mark
