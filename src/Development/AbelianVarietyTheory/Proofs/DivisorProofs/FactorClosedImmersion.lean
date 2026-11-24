module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory.PDivGroup

variable {p : ℕ} {k : Type} [CommRing k]

def liftClosed {K G H : PDivGroup p k} (i : K ⟶ G) (hi : ∀ n : ℕ, Function.Surjective (i.app n))
    (f : H ⟶ G) (hf : ∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) : H ⟶ K :=
  ⟨fun n => liftSurj (i.app n) (hi n) (f.app n) (hf n), fun n => BialgHom.ext fun b => by
    obtain ⟨a, rfl⟩ := hi (n + 1) b
    change H.res n (liftSurj (i.app (n + 1)) (hi (n + 1)) (f.app (n + 1)) (hf (n + 1))
        (i.app (n + 1) a)) =
      liftSurj (i.app n) (hi n) (f.app n) (hf n) (K.res n (i.app (n + 1) a))
    rw [liftSurj_apply, res_app, res_app, liftSurj_apply]⟩

theorem liftClosed_comp {K G H : PDivGroup p k} (i : K ⟶ G)
    (hi : ∀ n : ℕ, Function.Surjective (i.app n)) (f : H ⟶ G)
    (hf : ∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) :
    liftClosed i hi f hf ≫ i = f :=
  Hom.ext (funext fun n => BialgHom.ext fun a => liftSurj_apply (i.app n) (hi n) (f.app n) (hf n) a)

theorem cancel_closed {K G H : PDivGroup p k} (i : K ⟶ G)
    (hi : ∀ n : ℕ, Function.Surjective (i.app n)) (g g' : H ⟶ K) (h : g ≫ i = g' ≫ i) :
    g = g' :=
  Hom.ext (funext fun n => BialgHom.ext fun b => by
    obtain ⟨a, rfl⟩ := hi n b
    have := DFunLike.congr_fun (congrArg (fun u : H ⟶ G => u.app n) h) a
    simpa using this)

end GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.factor_closedImmersion : ∀ (p : ℕ) (k : Type) [CommRing k] (K G : PDivGroup p k) (i : K ⟶ G), (∀ n : ℕ, Function.Surjective (i.app n)) → (∀ (H : PDivGroup p k) (f : H ⟶ G), (∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) → ∃ g : H ⟶ K, g ≫ i = f) ∧ ∀ (H : PDivGroup p k) (g g' : H ⟶ K), g ≫ i = g' ≫ i → g = g' :=
  fun _ _ _ _ _ i hi => ⟨fun _ f hf => ⟨liftClosed i hi f hf, liftClosed_comp i hi f hf⟩,
    fun _ g g' h => cancel_closed i hi g g' h⟩
