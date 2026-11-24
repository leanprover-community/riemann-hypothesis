module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitVectorOrthogonal

open NumberField Formalism.BasicNotions

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def OfKind (W : HSpace E) (M P Q : ℕ) : Prop :=
  W.rank = M ∧ W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def perp (W : HSpace E) (x : W.V) : Submodule E W.V := LinearMap.ker (W.hT x)

def perpLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) (x : W.V) : Submodule (𝓞 E) W.V :=
  L ⊓ (perp W x).restrictScalars (𝓞 E)

def IsSelfDualLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) : Prop :=
  Submodule.IsLattice E L ∧ Formalism.HermitianLatticesTheory.dual W.hT L = L

def HasComplement (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) : Prop :=
  ∃ L : Submodule (𝓞 E) W.V, IsSelfDualLat W L ∧ x ∈ L ∧
    L = Submodule.span (𝓞 E) {x} ⊔ perpLat W L x ∧
    ∃ (W' : HSpace E) (ι : W'.V →ₗ[E] W.V), OfKind W' M' P' Q' ∧
      HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = perp W x ∧
      W'.L0.map (ι.restrictScalars (𝓞 E)) = perpLat W L x

def UnitVectorPerpOver (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ (W : HSpace E) (M P Q : ℕ), OfKind W M P Q → 3 ≤ M →
    (1 ≤ P → ∃ x : W.V, W.hD x x = 1 ∧ HasComplement W x (M - 1) (P - 1) Q) ∧
    (1 ≤ Q → ∃ x : W.V, W.hD x x = -1 ∧ HasComplement W x (M - 1) P (Q - 1))

end Generic

def UnitVectorPerp (D : D7) : Prop :=
  letI := D.host.cmStar
  UnitVectorPerpOver D.host.E

end GlobalTheory.IndefiniteRowSideFullHecke.UnitVectorOrthogonal

end
