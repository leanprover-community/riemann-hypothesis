module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField Matrix MeasureTheory
open scoped NumberField.AdeleRing

namespace PositivityTheory.He2M1

open GroundTheory.Global GroundTheory.Automorphic IdeleGroup PositivityTheory.RgEis

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def ltr (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) : (ι → 𝔸[k]) → ℂ :=
  fun x ↦ F ((A : Matrix ι ι 𝔸[k]) *ᵥ x)

noncomputable def thetaC (F : (ι → 𝔸[k]) → ℂ) (h : GL ι 𝔸[k]) : ℂ :=
  ∑' ξ : ι → k, F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ)

noncomputable def scalC (a : IdeleGroup k) : GL ι 𝔸[k] :=
  Units.map (Matrix.scalar ι : 𝔸[k] →+* Matrix ι ι 𝔸[k]).toMonoidHom a

noncomputable def thetaCInt (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k)
    (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ u in normOneFundamentalDomain k,
    thetaC F (scalC (moduleSection w t * (u : IdeleGroup k))) * (ω.toIdele (u : IdeleGroup k) : ℂ)
      ∂normOneMeasure k

noncomputable def thetaCFun (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k)
    (x : ℝ) : ℂ :=
  if hx : 0 < x then thetaCInt w F ω ⟨x, hx⟩ else 0

noncomputable def volChar (ω : HeckeCharacter k) : ℂ :=
  ∫ u in normOneFundamentalDomain k, (ω.toIdele (u : IdeleGroup k) : ℂ) ∂normOneMeasure k

noncomputable def thetaCConst (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) : ℂ :=
  F 0 * volChar ω

end PositivityTheory.He2M1
