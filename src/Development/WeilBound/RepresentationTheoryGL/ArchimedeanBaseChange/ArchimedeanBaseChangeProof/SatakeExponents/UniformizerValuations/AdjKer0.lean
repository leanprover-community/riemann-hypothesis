module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GlobalTheory
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

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open scoped Classical



namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

def OpNeOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E), 1 ≤ B.a + B.b → Nontrivial B.Hb →
  ∀ t : PT B, t.Ok → t.op ≠ 1

def AdjKer0 : Prop := ∀ (n : ℕ) (μ : Measure (G n)), μ.IsHaarMeasure → ∀ (M : KMod n) (g : ℝ → ℝ) (T : ℝ)
  (k : Mat n → (M.V →L[ℂ] M.V)), IsBump g T → IsKer μ M [] g k →
    IsKer μ M [] g (haveI := FiniteDimensional.complete ℂ M.V; fun y => ContinuousLinearMap.adjoint (k y⁻¹))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E}

def PT.pw (t : PT B) (m : ℕ) : PT B := BGen.wd (List.replicate m (Sum.inr t)) t

def PT.adj' (t : PT B) : PT B := { t.adj with va := t.va, vb := t.vb }

def PT.sq (t : PT B) (m : ℕ) : PT B := (t.adj'.pw m).mul (t.pw m)

def SqOk : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (t : PT B) (g : ℝ → ℝ) (m : ℕ), t.Ok →
  IsBump g t.T → (∀ v, IsKer B.μa (B.Ma v) [] g (t.ka v) ∧ ∀ χ, t.va v χ = coshT g (cas χ)) →
  (∀ v, IsKer B.μb (B.Mb v) [] g (t.kb v) ∧ ∀ χ, t.vb v χ = coshT g (cas χ)) →
  (t.pw m).Ok ∧ (t.pw m).op = t.op ^ (m + 1) ∧ (t.sq m).Ok ∧ (t.sq m).op = star (t.op ^ (m + 1)) * t.op ^ (m + 1) ∧
    (∀ χa χb, (t.sq m).val χa χb = t.val χa χb ^ (2 * (m + 1))) ∧
    (t.sq m).ψ = mulF B.ν (t.adj'.pw m).ψ (t.pw m).ψ

end PositivityTheory.Rg.BcB.F

end
