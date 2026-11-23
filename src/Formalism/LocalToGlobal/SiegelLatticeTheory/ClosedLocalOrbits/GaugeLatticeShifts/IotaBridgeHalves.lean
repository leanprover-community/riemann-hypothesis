module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictPf
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IotaBridgeARC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u →
    ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : X.B.I.GA), RatLink X b β →
      (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 * (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)
        ∈ X.B.I.Kset →
      NCong X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) →
      AdTriv X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) → RatTriv u X Λ β

def IotaBridgeRAC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u →
    ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : X.B.I.GA), RatLink X b β →
      (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 * (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)
        ∈ X.B.I.Kset →
      NCong X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) →
      RatTriv u X Λ β → AdTriv X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u))

end Formalism.L2.SG.Pf
