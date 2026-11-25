module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.CechPic

namespace GlobalTheory.Mix

variable {k K : Type} [CommRing k] [CommRing K] {X G : Scheme.{0}} {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X} {ρ : k →+* K}

def bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (z : CxPts q τ) : CxPts p (τ.comp ρ) := CxPts.bcMap w τ z

theorem bcPt_val (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (z : CxPts q τ) : (bcPt w τ z).1 = z.1 ≫ j := rfl

theorem continuous_bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) : Continuous (bcPt w τ) :=
  CxPts.continuous_of_comp (bcPt_val w τ)

theorem cInfAt_bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) {f : CxPts p (τ.comp ρ) → ℝ} {z : CxPts q τ}
    (h : CInfAt f (bcPt w τ z)) : CInfAt (fun y => f (bcPt w τ y)) z := by
  have hm : ∀ y, (bcPt w τ y).1 = y.1 ≫ j := bcPt_val w τ
  unfold CInfAt at h ⊢
  obtain ⟨W, ι, hι, g, F, O, hW, hO, hmem, hF, he⟩ := h
  refine ⟨j ⁻¹ᵁ W, ι, hι, fun a => j.app W (g a), F, O, (CxPts.mem_ptsIn_preimage hm).2 hW, hO, ?_, hF, ?_⟩
  · simpa only [CxPts.ev_of_comp hm] using hmem
  · filter_upwards [(continuous_bcPt w τ).continuousAt.tendsto.eventually he] with y hy
    simpa only [CxPts.ev_of_comp hm] using hy

def MLine.bc (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)) : MLine q τ where
  B := A.B.pull j
  φ := A.φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => bcPt w τ) fun _ _ => rfl
  cInf i z hz := (cInfAt_bcPt w τ (A.cInf _ _ (mem_of_mem_linComb (m := fun _ => bcPt w τ z)
    (fun _ => rfl) hz PUnit.unit))).congr (.of_forall fun y => by simp [Weight.linComb])

end GlobalTheory.Mix
