module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementActsOnFrameColumns
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem _root_.GlobalTheory.T.torus_element_acts_on_frame_columns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E)
    (t : Fin r₀ → ℝ), (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a →
    ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Xf =
        incM F Xf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i))) ∧
      ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Yf =
        incM F Yf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i)⁻¹)) ∧
      ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Yf * J) *ᵥ z = 0 →
        ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ
          (fun i => inclR (F := F) (AF F) (z i)) = fun i => inclR (F := F) (AF F) (z i) := by
  first | exact @GlobalTheory.TorusMat.isTorusElt_mat | exact GlobalTheory.TorusMat.isTorusElt_mat | (intros; apply GlobalTheory.TorusMat.isTorusElt_mat <;> assumption)
