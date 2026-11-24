module

public import GroundTheory.AutomorphicForms.GKModules.RightRegular
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory GroundTheory.Automorphic

namespace GlobalTheory.HCA

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤) {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤)

structure SmFn [MeasurableSpace G] (μ : Measure G) (S : Submodule ℂ (G → ℂ)) (K : Set G)
    (Λ : List (Fin d) → (G → ℂ) → ℂ) : Prop where
  lin : ∀ l, ∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ l (c • f + f') = c * Λ l f + Λ l f'
  bdd : ∀ l, ∃ C : ℝ, ∀ f ∈ S, ‖Λ l f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ
  der : ∀ l i, ∀ f ∈ S, HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) (Λ (i :: l) f) 0

def solG (P : Polynomial ℂ) : Submodule ℂ (G → ℂ) :=
  (LinearMap.ker (Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P)).map
    (h.smoothFuns (F := ℂ)).subtype

theorem mem_solG {P : Polynomial ℂ} {f : G → ℂ} : f ∈ solG h b P ↔ ∃ hf : h.IsSmoothFun f,
    Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P
      (⟨f, hf⟩ : h.smoothFuns (F := ℂ)) = 0 := by
  simp only [solG, Submodule.mem_map, LinearMap.mem_ker, Submodule.subtype_apply]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩
  · rintro ⟨hf, h0⟩
    exact ⟨⟨f, hf⟩, h0, rfl⟩

namespace SmFnEx

end SmFnEx

end GlobalTheory.HCA

end
