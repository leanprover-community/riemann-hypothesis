module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecomposition
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

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

theorem _root_.GlobalTheory.T.hyperbolic_pair_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), (∀ i j, σ (W.J j i) = -W.J i j) → form σ W.J H'.x H'.x = 0 → form σ W.J H'.y H'.y = 0 → form σ W.J H'.x H'.y = 1 → (∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0) → (∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y) → ∀ g ∈ unip σ W H', ∃ (b : Fin d₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), c - cA σ c = -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) ∧ mat g = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c := by
  first | exact @GlobalTheory.UnipMass.StdMat.unip_eq_nmat | exact GlobalTheory.UnipMass.StdMat.unip_eq_nmat | (intros; apply GlobalTheory.UnipMass.StdMat.unip_eq_nmat <;> assumption)
