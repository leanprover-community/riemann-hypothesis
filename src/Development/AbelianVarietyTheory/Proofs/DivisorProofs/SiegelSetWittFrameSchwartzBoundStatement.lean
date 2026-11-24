module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameSchwartzBound
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem _root_.GlobalTheory.T.siegel_set_witt_frame_schwartz_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf → ∀ c : ℝ, 0 < c →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ ≤ C * ((ht y : ℝ) * ht h) ^ k * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  first | exact @GlobalTheory.TorusTheta.theta_torus_le | exact GlobalTheory.TorusTheta.theta_torus_le | (intros; apply GlobalTheory.TorusTheta.theta_torus_le <;> assumption)
