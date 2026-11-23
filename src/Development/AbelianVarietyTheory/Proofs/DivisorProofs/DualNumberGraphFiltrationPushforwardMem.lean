module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

theorem push_constMor_pull {k : Type} [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀)
    [IsMonHom g] (c : primDR A₀) :
    primPull (epsDP k) (GlobalTheory.DeRham.epsRed k) g ((constMor A₀).pull c) =
      (constMor A₀).pull (primPull (dp0 k) (𝟙 _) g c) := by
  have K := (constMor A₀).isMor.comp (homMor (epsDP k) (GlobalTheory.DeRham.epsRed k) g).isMor
  apply Subtype.ext
  exact (IsMor.pullback1_comp (constMor A₀).isMor
    (homMor (epsDP k) (GlobalTheory.DeRham.epsRed k) g).isMor K (fun _ ↦ rfl) rfl c.1).trans
    (IsMor.pullback1_comp (homMor (dp0 k) (𝟙 _) g).isMor (constMor A₀).isMor K
      (fun _ ↦ rfl) (by simp) c.1).symm

theorem push_mem_graphFil : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀) [IsMonHom g] (f : HdR A₀ →ₗ[k] HdR A₀), (∀ x ∈ Fil A₀, f (push (dp0 k) (𝟙 _) g x) - push (dp0 k) (𝟙 _) g (f x) ∈ Fil A₀) → ∀ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, push (epsDP k) (GlobalTheory.DeRham.epsRed k) g d ∈ GlobalTheory.HTRealise.graphFil A₀ f := by
  intro k _ A₀ _ g _ f hf d hd
  obtain ⟨x, hx, y, hy, e⟩ := hd
  refine ⟨push (dp0 k) (𝟙 _) g x, push_mem_Fil g hx,
    push (dp0 k) (𝟙 _) g (f x) - f (push (dp0 k) (𝟙 _) g x) + push (dp0 k) (𝟙 _) g y,
    add_mem (by rw [← neg_sub]; exact neg_mem (hf x hx)) (push_mem_Fil g hy), fun c ↦ ?_⟩
  rw [push_apply, push_constMor_pull, e]
  simp only [push_apply, LinearMap.add_apply, LinearMap.sub_apply]
  congr 2
  ring

end GlobalTheory.HTRealise
