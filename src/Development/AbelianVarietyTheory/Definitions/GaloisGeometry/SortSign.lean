module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CechDR GlobalTheory.HodgeCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD

section Hmap

variable {k : Type} [Field k] {M M' : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']

def Cx.hmap (K : Cx k M) (L : Cx k M') (f : M →ₗ[k] M') (hf : IsMap K L f) (n : ℤ) : K.H n →ₗ[k] L.H n :=
  Submodule.mapQ _ _ ((f.restrict (p := K.Z n) (q := L.Z n) fun a ha => by
      refine ⟨(hf n a ha.1).1, ?_⟩
      change L.D (f a) = 0
      rw [← (hf n a ha.1).2]
      have : K.D a = 0 := ha.2
      rw [this, map_zero]))
    (by
      rintro ⟨a, ha⟩ hb
      obtain ⟨c, hc, e⟩ := hb
      refine ⟨f c, ?_, ?_⟩
      · have h1 := (hf (n - 1) c hc).1
        exact h1
      · change L.D (f c) = f a
        rw [← (hf (n - 1) c hc).2, e]; rfl)

end Hmap

section Pull

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {E E' : Type} [AddCommGroup E] [Module k E]
  [AddCommGroup E'] [Module k E']

def sortSign (τ : κ → ι) (s : Finset κ) : ℤ := ∏ a ∈ s, ∏ b ∈ s, if a < b ∧ τ b < τ a then -1 else 1


open Classical in
def pullC (τ : κ → ι) (φ : E →ₗ[k] E') : (Finset ι → E) →ₗ[k] (Finset κ → E') where
  toFun c s := if Set.InjOn τ s then sortSign τ s • φ (c (s.image τ)) else 0
  map_add' a b := by
    funext s
    by_cases h : Set.InjOn τ s <;> simp [h, smul_add]
  map_smul' r a := by
    funext s
    by_cases h : Set.InjOn τ s <;> simp [h, smul_comm (sortSign τ s) r]

end Pull

section Rat

variable (k : Type) [Field k] {K K' : Type} [Field K] [Field K'] [Algebra k K] [Algebra k K']

def IsDRMap (ψ : K →ₐ[k] K') (φ : DR k K →ₗ[k] DR k K') : Prop :=
  ∀ (q : ℕ) (b : K) (v : Fin q → K), φ (b • ExteriorAlgebra.ιMulti K q fun j => D k K (v j)) =
    ψ b • ExteriorAlgebra.ιMulti K' q fun j => D k K' (ψ (v j))

end Rat

end GlobalTheory.PD
