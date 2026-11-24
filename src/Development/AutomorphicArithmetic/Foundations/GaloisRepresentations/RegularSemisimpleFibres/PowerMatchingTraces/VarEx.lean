module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocGalEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.LocTw
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPow
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

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.G

theorem varEx : VarEx := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn P hP v w hv
  let μE : Measure (normOneGL (K := E) (n := n)) := Measure.haar
  let μF : Measure (normOneGL (K := F) (n := n)) := Measure.haar
  have hlocEx := UpperTheory.ConvolutionTheory.C.locGalEx F E σ hp n v w hv
  have hw := hlocEx.1
  obtain ⟨s, hs, hloc⟩ := hlocEx.2
  refine ⟨s, hs, fun τ' hτ' => ?_⟩
  obtain ⟨χ', ⟨z, hz'⟩, V, hV⟩ := Dp.exTwist E n μE P hn
  obtain ⟨hex, htw⟩ := T.powTwist F E
  obtain ⟨χ, hz⟩ := (hex z).1
  obtain ⟨-, -, h1⟩ := htw z χ χ' hz hz'
  obtain ⟨-, -, -, hconj, -⟩ := h1 n hn
  obtain ⟨-, -, -, -, -, θ, hθ, hst⟩ := T.carryLift F E σ hσ hp n hn μE μF
  have hstab := (hst _ V hV).1 fun g => hconj P _ (hP g)
  obtain ⟨⟨τ₁, hτ₁⟩, hall⟩ := locTw E n hn P χ' w.1 τ' hτ'
  obtain ⟨e, he⟩ := hall τ₁ hτ₁
  have hocc : Occurs μE V w.1 τ₁ :=
    (occursIff E n μE V hV.summand w.1 τ₁).2 ((Dp.locIff E n μE _ V hV w.1 τ₁).1 hτ₁)
  obtain ⟨I₁, hI₁⟩ := (hloc μE θ hθ).2 V τ₁ hV.summand hstab hocc
  have hχ : ∀ g, chiAt n χ' w.1 (s g) = chiAt n χ' w.1 g :=
    (matchPow F E σ hσ hp n hn z χ χ' hz hz' v w hw).1 (s : Gw n w.1 →* Gw n w.1) hs
  have hne : ∀ g, chiAt n χ' w.1 g ≠ 0 := fun g => Units.ne_zero _
  refine ⟨e.trans (I₁.trans e.symm), fun g x => ?_⟩
  have h2 : e (τ'.ρ g x) = (chiAt n χ' w.1 g)⁻¹ • τ₁.ρ g (e x) := by
    rw [← he g x, map_smul, smul_smul, inv_mul_cancel₀ (hne g), one_smul]
  have h3 : τ₁.ρ (s g) (I₁ (e x)) = chiAt n χ' w.1 (s g) • e (τ'.ρ (s g) (e.symm (I₁ (e x)))) := by
    rw [← map_smul, he (s g) (e.symm (I₁ (e x))), e.apply_symm_apply]
  simp only [LinearEquiv.trans_apply]
  rw [h2, map_smul, hI₁, h3, smul_smul, hχ g, inv_mul_cancel₀ (hne g), one_smul, e.symm_apply_apply]

end UpperTheory.Gal.InertialTypesAlt.G
