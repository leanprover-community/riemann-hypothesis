module

public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.PairingIndexBounds.F

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def aaOf (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E)
    {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t}

variable {D}

def movD {E : Type} [Field E] {a b : ℕ} (Φ : HomE E a b → ℂ) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) :
    HomE E a b → ℂ :=
  fun x => Φ (inFr g g' x)

def kerTh {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ)
    (N : Submodule (𝓞 D.host.E) (Sp D.host.E a)) (N' : Submodule (𝓞 D.host.E) (Sp D.host.E b))
    (Ξ : HomE D.host.E a b → ℂ) : TaylorLogMetric.VC D a b → ℂ :=
  thC (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (aaOf D cc) SS N N' c Ξ
    (B.eNat χ a b N N')

def serP {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {a b : ℕ} (θ : TaylorLogMetric.VC D a b → ℂ) :
    MvPowerSeries (D.what₂.Tau × Fin b × Fin a) ℂ_[p] :=
  TaylorLogMetric.pSer D lam θ

end Formalism.L2.PairingIndexBounds.F
