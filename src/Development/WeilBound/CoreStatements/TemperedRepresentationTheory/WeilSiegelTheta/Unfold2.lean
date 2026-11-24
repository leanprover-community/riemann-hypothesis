module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
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

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.GramSchwartzFunctions.EC

open GlobalTheory.StdUnn

def Term2 : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
  ∀ Φ : schwartzA θ V.rank n, ∀ (r : ℕ), r ≤ n → ∀ (μr : Measure (Mx D V.rank r)),
    (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) →
  ∀ (c : Matrix (Fin r) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin n) D.host.E), IsCompl c a →
  ∀ b : HermE D r, ∀ γ ∈ GF D n, mat γ = (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b.1 a).map (incA D) →
    (ω γ Φ).1 0 = J ψ V μr (pull c Φ.1) b

def Unfold2 : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ (V : HSp D) (n r : ℕ), r ≤ n → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)),
    IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ μr : Measure (Mx D V.rank r), (∃ 𝓕r, IsCovolOne (ratMx D V.rank r) μr 𝓕r) →
  ∀ (c : Matrix (Fin r) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin n) D.host.E), IsCompl c a → ∀ b : HermE D r,
  ∀ Φ : Mx D V.rank n → ℂ, Φ ∈ schwartzA θ V.rank n →
    ∫ y in 𝓕, ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
        Heisenberg₂ ψ V (HMul.hMul (zy y) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b.1 a).map (incA D))) Φ
          (ξ.map (incA D)) ∂μ =
      J ψ V μr (pull c Φ) b

end PositivityTheory.GramSchwartzFunctions.EC
