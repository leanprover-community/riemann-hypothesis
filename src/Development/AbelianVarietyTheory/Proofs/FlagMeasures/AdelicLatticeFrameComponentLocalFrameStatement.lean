module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameComponentLocalFrame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adelicLatticeFrame_component_localFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (g k : ℕ) (Fr : AdFrame σ J (hat F L) g k) (v : HeightOneSpectrum (𝓞 F)), prV (E := E) v Fr.eps * prV (E := E) v Fr.eps = prV (E := E) v Fr.eps ∧ prV (E := E) v Fr.eps * sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) = 0 ∧ prV (E := E) v Fr.eps ∈ intV E v ∧ (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - prV (E := E) v Fr.eps - sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps)) • y = (g : E ⊗[F] v.adicCompletion F) • z) ∧ (∀ i, prVec v (Fr.b i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.bd i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.b i) = prV (E := E) v Fr.eps • prVec v (Fr.b i)) ∧ (∀ i, prVec v (Fr.bd i) = sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) • prVec v (Fr.bd i)) ∧ (∀ i j, ∃ t ∈ intV E v, hR σ J (v.adicCompletion F) (prVec v (Fr.bd i)) (prVec v (Fr.b j)) - (if i = j then prV (E := E) v Fr.eps else 0) = (g : E ⊗[F] v.adicCompletion F) * t) ∧ (∀ y ∈ loc v L, InModL (loc v L) g (Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j))) y) := by
  first | exact @GlobalTheory.St.G.frame_component_local | exact GlobalTheory.St.G.frame_component_local | (intros; apply GlobalTheory.St.G.frame_component_local <;> assumption)
