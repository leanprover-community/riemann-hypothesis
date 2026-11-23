module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepresentationPointwiseArchimedeanDecayBound

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem per_mM {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {m : ℕ} {f : (κ → AF F) → ℂ}
    (h : Per F m f) (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) : Per F m (mM F l f) := by
  intro x z hz
  have hev : ∀ a b : AF F, evI F (a + b) = evI F a + evI F b := fun a b =>
    map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have hmul : ∀ a b : AF F, evI F (a * b) = evI F a * evI F b := fun a b =>
    map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have ha : arch F (x + z) = arch F x := by
    funext i
    obtain ⟨a, ha0, -, hza⟩ := hz i
    show evI F (x i + z i) = evI F (x i)
    rw [hev, hza, hmul, ha0, mul_zero, add_zero]
  unfold mM
  rw [ha, h x z hz]

theorem norm_word_rep {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) (x : κ → AF F) (N : ℕ) :
    ‖word F (List.replicate N (Sum.inr l)) f x‖ = |l (arch F x)| ^ N * ‖f x‖ := by
  induction N with
  | zero => simp [word]
  | succ N ih =>
    rw [List.replicate_succ, word_cons]
    show ‖(l (arch F x) : ℂ) * word F (List.replicate N (Sum.inr l)) f x‖ = _
    rw [norm_mul, ih, Complex.norm_real, Real.norm_eq_abs, pow_succ]
    ring

theorem om_bound_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k :=
  PositivityTheory.ThKF0.weil_rep_rapid_decay_height

end GlobalTheory.ArchDecay
