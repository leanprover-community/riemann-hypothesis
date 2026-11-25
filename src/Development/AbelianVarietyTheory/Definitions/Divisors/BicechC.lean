module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.PD

section Bi

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  {E E' E'' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E'']


variable (k ι κ E'') in
def biD : (Finset ι × Finset κ → E'') →ₗ[k] (Finset ι × Finset κ → E'') :=
  LinearMap.pi fun x =>
    (∑ i ∈ x.1, GlobalTheory.cubeSign x.1 i • LinearMap.proj (R := k) (φ := fun _ : Finset ι × Finset κ => E'') (x.1.erase i, x.2)) +
      ((-1 : ℤ) ^ (x.1.card + 1)) •
        ∑ j ∈ x.2, GlobalTheory.cubeSign x.2 j • LinearMap.proj (R := k) (φ := fun _ : Finset ι × Finset κ => E'') (x.1, x.2.erase j)

def bicechC (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') (n : ℤ) :
    Submodule k (Finset ι × Finset κ → E'') :=
  Submodule.pi Set.univ fun x =>
    if x.1.Nonempty ∧ x.2.Nonempty ∧ ((x.1.card + x.2.card : ℕ) : ℤ) = n + 2 then Submodule.map₂ μ (A x.1) (B x.2) else ⊥

def bicech (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') :
    Cx k (Finset ι × Finset κ → E'') :=
  ⟨bicechC μ A B, biD k ι κ E''⟩

def boxC (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') : Finset ι × Finset κ → E'' :=
  fun x => μ (a x.1) (b x.2)


end Bi

end GlobalTheory.PD
