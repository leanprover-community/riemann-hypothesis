module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct

namespace GlobalTheory.SeeSaw

variable {D : D7}

def IsBiSmooth {A S A' : HSp D} (C : WO A S → WO S A' → ℂ) : Prop :=
  ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO A S) (L' : (Fin n → ℝ) →+ WO S A'), Continuous L → Continuous L' →
    (∀ t, (L t).map (finPart D) = 0) → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ u v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => C (u + L t) (v + L' t)

structure IsBiTheta (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (C : WO A S → WO S A' → ℂ) : Prop where
  cont : Continuous fun p : WO A S × WO S A' => C p.1 p.2
  smooth : IsBiSmooth C
  quasiL : ∀ γ u v, C (ratW S A γ + u) v = ψ (-(symplOH A S (ratW S A γ) u)) * C u v
  quasiR : ∀ γ u v, C u (ratW A' S γ + v) = ψ (-(symplOH S A' (ratW A' S γ) v)) * C u v
  levL : ∃ U : AddSubgroup (WO A S), IsOpen (U : Set (WO A S)) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ v, heisO ψ A S a (fun u => C u v) = fun u => C u v
  levR : ∃ U : AddSubgroup (WO S A'), IsOpen (U : Set (WO S A')) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ u, heisO ψ S A' a (C u) = C u

def BiAct (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'),
    IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → ∀ C, IsBiTheta ψ A S A' C →
      (∀ p, IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u) ∧
      (∀ q, IsBiTheta ψ A S A' fun u v => omb q (C u) v) ∧
      (∀ p q u v, omb q (fun v' => oma p (fun u' => C u' v') u) v = oma p (fun u' => omb q (C u') v) u) ∧
      Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' =>
        omb x.2.1 (fun v => oma x.1 (fun u => C u v) x.2.2.1) x.2.2.2

def FockRed (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'),
    x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z →
    ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C →
      ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank),
        ∀ φ, IsContAut A φ → HasCen A χ φ →
          biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) =
            ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ)

namespace Dat

variable {u : D.what₂.Word} (d : Dat D u)

end Dat

section Examples

variable {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D}

end Examples

end GlobalTheory.SeeSaw

end
