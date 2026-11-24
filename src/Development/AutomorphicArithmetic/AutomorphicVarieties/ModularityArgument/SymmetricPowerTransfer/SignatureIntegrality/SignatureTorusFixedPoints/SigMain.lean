module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.NotIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkDOrb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkGOrb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkKValLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.TauOfRoots
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open UpperTheory.V.Z.Sym.Sig in
theorem UpperTheory.V.Z.Sym.Sig.sigMain : UpperTheory.V.Z.Sym.Sig.SigMain := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hR χ hχ
  obtain ⟨hJ, hJf, hJ2, hJ2f, hcG, hcS, hreg⟩ := okLev k O hO h2 Δ s hs hs0 V Ry hR χ hχ
  exact ⟨hcG, hcS, hcS, hJ, hJf, hJ2, hJ2f, hreg,
    fun t ht => (okG k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).1,
    fun t ht => (okG k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.1,
    fun t ht => (okG k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.2,
    fun t ht => okGOrb k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht,
    fun t ht => (okS k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).1,
    fun t ht => (okS k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.1,
    fun t ht => (okS k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.2,
    fun t ht => (okK k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).1,
    fun t ht => (okK k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.1,
    fun t ht => (okK k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.2,
    fun t ht => okDOrb k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht⟩
