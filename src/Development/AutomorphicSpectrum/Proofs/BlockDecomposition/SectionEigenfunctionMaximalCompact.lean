module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBlockMatrixTwoByTwoFinEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
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

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.Jp

def GoodPsi (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D) : Prop :=
  (∀ a ∈ v.adicCompletionIntegers D.host.F, psiV D.host.F ψ v a = 1) ∧
    ∀ ϖ : v.adicCompletionIntegers D.host.F, Irreducible ϖ →
      ∃ b : v.adicCompletionIntegers D.host.F,
        psiV D.host.F ψ v ((b : Fv D.host.F v) / (ϖ : Fv D.host.F v)) ≠ 1

def GoodChi (D : D7) (χ : (AE D)ˣ →* Circle) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Prop :=
  ∀ a : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ,
    ‖splitProj τ (a : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ =
      ‖splitProj (τ.comp D.sp.cm.sig) (a : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ →
    χ (ideleAt D.host.F D.host.E v a) = 1

abbrev sphV (D : D7) (n : ℕ) (v : Pl D) (z : ℂ) : GLoc D.sp.cm.sig (Jst D n) v → ℂ :=
  GlobalTheory.LocIntw.sphUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) (absEv D.host.F D.host.E v)
    (GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) z

def GoodPlacesOutsideFiniteSet : Prop :=
  ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ →
    ResEta D χ r → ∀ S : Finset (Pl D), ∃ v ∉ S, GoodPsi D ψ v ∧ ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, GoodChi D χ v τ

def SplitPlaceRankCutEigenvalue : Prop :=
  ∀ (D : D7) (n r t : ℕ), r + t = n → 1 ≤ r → ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
    ∀ nb : hermA D n → G D n, IsNMap nb → ∀ v : Pl D, GoodPsi D ψ v → ∀ _ : D.host.E →ₐ[D.host.F] Fv D.host.F v,
    ∃ (C : Cut D n v) (c : ℂ → ℂ), C.Kills ψ r ∧ Differentiable ℂ c ∧ c ((t : ℂ) / 2) ≠ 0 ∧
      ∀ νv : Measure (KAt D n v), νv.IsHaarMeasure → IsProbabilityMeasure νv → ∀ z : ℂ,
        ∫ k : KAt D n v, ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x)) ∂νv = c z

def SectionEigenfunctionMaximalCompact : Prop :=
  ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (nb : hermA D n → G D n), IsNMap nb → ∀ (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), GoodChi D χ v τ → ∀ (C : Cut D n v) (νv : Measure (KAt D n v)),
    νv.IsHaarMeasure → ∀ z c : ℂ,
    (∫ k : KAt D n v, ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x)) ∂νv = c) →
    ∀ f : G D n → ℂ, IsLaw χ z f → (∀ k ∈ KAt D n v, ∀ g, f (g * k) = f g) → ∀ g : G D n,
      ∫ k : KAt D n v, cutR nb C f (g * k) ∂νv = c * f g

end GlobalTheory.CompanionTheory.Jp

end
