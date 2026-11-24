module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfValuedEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.Mem.Chr GlobalTheory.LFun

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E]

theorem pLoc_conjFin_eq (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (c x)) (hv : ∀ x, Valued.v (s x) = Valued.v x) (x : Af E) :
    pLoc E w (conjFin c x) = s (pLoc E w x) := by
  have hw : ConjPl c w w := fun k => by
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
      w.valuedAdicCompletion_eq_valuation' k
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (c k)) = w.valuation E (c k) :=
      w.valuedAdicCompletion_eq_valuation' _
    rw [← h1, ← h2, ← hs, hv]
  have key : ∀ (u : HeightOneSpectrum (𝓞 E)) (_ : w = u) (φ : u.adicCompletion E →+* w.adicCompletion E),
      Continuous φ → (∀ k : E, φ (algebraMap E _ k) = algebraMap E _ (c k)) → φ (pLoc E u x) = s (pLoc E w x) := by
    rintro _ rfl φ h1 h2
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer h1
      (continuous_of_valued_eq (w.valuedAdicCompletion_surjective E) s hv)
      (funext fun k => (h2 k).trans (hs k).symm)) _
  rw [pLoc_conjFin]
  exact key _ (eq_conjSrc hw) _ (conjLoc_spec c w).1 (conjLoc_spec c w).2.1

variable [IsCMField E]

theorem cT_cLoc {n : ℕ} (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : UA E n) : cT s (cLoc w g).val * (cLoc w g).val = 1 := by
  have hg : cT (conjAd E) g.1.val * 1 * g.1.val = 1 := g.2
  rw [Matrix.mul_one] at hg
  have h := congrArg ((pLoc E w).comp (pFin E)).mapMatrix hg
  rw [map_mul, map_one] at h
  rw [← h]
  congr 1
  refine Matrix.ext fun i j => ?_
  exact (pLoc_conjFin_eq (IsCMField.complexConj E).toRingEquiv w s hs hv (pFin E (g.1.val j i))).symm

end GlobalTheory.UnitaryBC

end
