module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
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

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace GlobalTheory.Et.TrivTors

def sigmaFinSuccIso (V : Scheme.{0}) (k : ℕ) :
    (∐ fun _ : Fin (k + 1) => V) ≅ V ⨿ (∐ fun _ : Fin k => V) where
  hom := Sigma.desc (Fin.cases coprod.inl fun i => Sigma.ι (fun _ : Fin k => V) i ≫ coprod.inr)
  inv := coprod.desc (Sigma.ι (fun _ : Fin (k + 1) => V) 0)
    (Sigma.desc fun i => Sigma.ι (fun _ : Fin (k + 1) => V) i.succ)
  hom_inv_id := by
    ext i
    induction i using Fin.cases
    · simp only [Fin.cases_zero, Sigma.ι_comp_desc_assoc]
      exact coprod.inl_desc _ _
    · simp only [Fin.cases_succ, Sigma.ι_comp_desc_assoc, Category.assoc, Category.comp_id]
      erw [coprod.inr_desc, Sigma.ι_comp_desc]
  inv_hom_id := by
    apply coprod.hom_ext
    · erw [coprod.inl_desc_assoc, Sigma.ι_comp_desc]
      simp
    · erw [coprod.inr_desc_assoc]
      ext i
      simp

theorem sigmaFinSuccIso_hom_desc (V : Scheme.{0}) (k : ℕ) :
    (sigmaFinSuccIso V k).hom ≫ coprod.desc (𝟙 V) (Sigma.desc fun _ : Fin k => 𝟙 V) =
      Sigma.desc fun _ : Fin (k + 1) => 𝟙 V := by
  ext i
  induction i using Fin.cases
  · simp only [sigmaFinSuccIso, Sigma.ι_comp_desc_assoc, Fin.cases_zero, Sigma.ι_comp_desc]
    exact coprod.inl_desc _ _
  · simp only [sigmaFinSuccIso, Sigma.ι_comp_desc_assoc, Fin.cases_succ, Sigma.ι_comp_desc,
      Category.assoc]
    erw [coprod.inr_desc, Sigma.ι_comp_desc]

theorem isFinite_sigmaDesc_fin (V : Scheme.{0}) : ∀ k : ℕ, IsFinite (Sigma.desc fun _ : Fin k => 𝟙 V)
  | 0 => by
    have : IsEmpty (∐ fun _ : Fin 0 => V : Scheme.{0}) := by
      exact ⟨fun x => ((sigmaMk fun _ : Fin 0 => V).symm x).1.elim0⟩
    exact ((IsClosedImmersion.iff_isFinite_and_mono _).mp (by infer_instance)).1
  | k + 1 => by
    have := isFinite_sigmaDesc_fin V k
    rw [← sigmaFinSuccIso_hom_desc]
    infer_instance

end GlobalTheory.Et.TrivTors
