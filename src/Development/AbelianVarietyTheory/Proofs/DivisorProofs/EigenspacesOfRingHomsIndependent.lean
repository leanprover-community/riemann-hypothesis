module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
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
public import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem iSupIndep_eig : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type)
    [CommRing Λ] (h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), Function.Injective (algebraMap O C) →
    iSupIndep (fun σ : Λ →+* O => eig C (⇑ρ) σ) := by
  intro C _ O _ _ Λ _ h ρ hinj
  let T : Λ → Module.End C (Fin h → C) := fun a => Matrix.toLin' ((ρ a).map (algebraMap O C))
  have hT : ∀ a b, T a * T b = T (a * b) := by
    intro a b
    simp only [T, map_mul, Matrix.map_mul]
    rw [Matrix.toLin'_mul]
    rfl
  have hc : ∀ a b, Commute (T a) (T b) := by
    intro a b
    show T a * T b = T b * T a
    rw [hT, hT, mul_comm]
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  let g : (Λ →+* O) → (Λ → C) := fun σ a => algebraMap O C (σ a)
  have hg : Function.Injective g := by
    intro σ τ hστ
    ext a
    exact hinj (congrFun hστ a)
  refine (hind.comp hg).mono ?_
  intro σ
  exact iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace

end GlobalTheory
