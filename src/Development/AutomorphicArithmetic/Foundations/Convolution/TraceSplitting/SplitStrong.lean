module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplitAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.ConvolutionTheory.T.splitStrong :
    UpperTheory.ConvolutionTheory.T.DescStep → UpperTheory.ConvolutionTheory.T.SplitStrong := by
  intro hD F E _ _ _ _ _ _ _ _ σ hσ hp n hn π P hc hw v w i hi hcomp τ τ' hτ hτ'
  obtain ⟨-, -, -, -, -, hpl⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨hs, u, rfl, hiu⟩ := hpl v w i hi hcomp
  obtain ⟨π', hl, hloc⟩ := hD F E σ hσ hp n hn P hc v u hs
  obtain ⟨η, hη, hiso⟩ := (UpperTheory.ConvolutionTheory.R.fibre_holds F E hp n hn (.cx π') (.cx P) hl.1).2 (.cx π) hw
  have he : π'.twist η = π := (UpperTheory.ConvolutionTheory.Dp.isoEq F n (π'.twist η) π).1 hiso
  subst he
  have hτ₀ : (UpperTheory.CBC.Cusp.cx π').locComp v τ := by
    rcases hη with rfl | hη
    · simpa [GlobalTheory.CuspRep.CuspSub.twist_one] using hτ
    · exact (UpperTheory.ConvolutionTheory.T.normCharSplit F E σ hσ hp n hn η hη v hs π' τ).1 hτ
  obtain ⟨e, he⟩ := hloc τ τ' hτ₀ hτ'
  have hm : i.toRingHom = GroundTheory.Global.SemiLocal.completionMap v u.1 := RingHom.ext hiu
  refine ⟨e, fun g x => ?_⟩
  rw [hm]
  exact he g x
