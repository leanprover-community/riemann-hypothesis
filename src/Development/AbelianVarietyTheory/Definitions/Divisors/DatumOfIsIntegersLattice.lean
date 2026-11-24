module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open WeierstrassCurve
open scoped IntermediateField

namespace GlobalTheory.CMModel

def Stable (L : PeriodPair) (F : IntermediateField ℚ ℂ) {ι : Type} (T : ι → ℂ) : Prop :=
  ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ e : ι ≃ ι, ∀ i, GlobalTheory.ConjPoint.IsConj L L σ (T i) (T (e i))

def IntV (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) : Prop :=
  W.a₁ ∈ V ∧ W.a₂ ∈ V ∧ W.a₃ ∈ V ∧ W.a₄ ∈ V ∧ W.a₆ ∈ V

def ModelAt (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (W : WeierstrassCurve ℂ) (D : ℂ) : Prop :=
  ∃ C : VariableChange ℂ, (C.u : ℂ) ∈ F ∧ C.r ∈ F ∧ C.s ∈ F ∧ C.t ∈ F ∧ IntV V (C • W) ∧
    V.valuation (C • W).Δ = V.valuation D

abbrev Sq (p : ℕ) : Type := {k : Fin p // ((k : ℕ) : ZMod p) ≠ 0 ∧ IsSquare ((k : ℕ) : ZMod p)}


open Classical in
instance (p : ℕ) : Fintype (Sq p) := Subtype.fintype _

def sqPt (p : ℕ) (t : ℂ) (k : Sq p) : ℂ := ((k.1 : ℕ) : ℂ) * t

def sqProd (p : ℕ) (L : PeriodPair) (t : ℂ) : ℂ := ∏ k : Sq p, L.derivWeierstrassP (sqPt p t k)

def shortTwist {R : Type} [CommRing R] (d a₄ a₆ : R) : WeierstrassCurve R := ⟨0, 0, 0, d ^ 2 * a₄, d ^ 3 * a₆⟩

structure Datum (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ) : Prop where

  mul : Formalism.L2.Th1.F.MulStable L (GlobalTheory.Published.sqrtNegNat p)

  g₂_mem : L.g₂ ∈ F

  g₃_mem : L.g₃ ∈ F

  notMem : t ∉ L.lattice

  ker : GlobalTheory.Published.sqrtNegNat p * t ∈ L.lattice

end GlobalTheory.CMModel
