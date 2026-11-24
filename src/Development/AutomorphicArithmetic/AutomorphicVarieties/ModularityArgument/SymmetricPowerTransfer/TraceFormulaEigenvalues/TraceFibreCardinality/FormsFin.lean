module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

theorem UpperTheory.V.Z.Sym.Tf.formsFin :
    UpperTheory.V.Z.Sym.Tf.FormsFin := by
  intro Γ G V _ _ _ _ _ B hB
  obtain ⟨S, hS⟩ := hB.cls
  let L : B.Forms →ₗ[ℂ] (S → V) :=
    (LinearMap.funLeft ℂ V (fun s : S => (s : G))).comp B.Forms.subtype
  refine Module.Finite.of_injective L ?_
  intro φ ψ h
  apply Subtype.ext
  funext g
  obtain ⟨γ, s, hs, u, hu, rfl⟩ := hS g
  have hsv : φ.1 s = ψ.1 s := congrFun h ⟨s, hs⟩
  have e1 : φ.1 (B.ι γ * s * u) = (B.ω ⟨u, hu⟩ : ℂ) • φ.1 (B.ι γ * s) := φ.2.2 _ ⟨u, hu⟩
  have e2 : ψ.1 (B.ι γ * s * u) = (B.ω ⟨u, hu⟩ : ℂ) • ψ.1 (B.ι γ * s) := ψ.2.2 _ ⟨u, hu⟩
  have f1 : φ.1 (B.ι γ * s) = B.W γ (φ.1 s) := φ.2.1 γ s
  have f2 : ψ.1 (B.ι γ * s) = B.W γ (ψ.1 s) := ψ.2.1 γ s
  rw [e1, e2, f1, f2, hsv]
