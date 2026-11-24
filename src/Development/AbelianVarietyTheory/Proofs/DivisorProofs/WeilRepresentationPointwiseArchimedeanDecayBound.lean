module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepresentationPointwiseArchimedeanDecayBound

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend, Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBound

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.ArchDecay

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def infAd (a : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a)

def arch (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def dD (v : κ → mixedEmbedding.mixedSpace F) (f : (κ → AF F) → ℂ) (x : κ → AF F) : ℂ :=
  deriv (fun t : ℝ => f (x + fun i => infAd F (t • v i))) 0

def mM (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) (x : κ → AF F) : ℂ :=
  (l (arch F x) : ℂ) * f x


variable (κ) in
abbrev Op : Type := (κ → mixedEmbedding.mixedSpace F) ⊕ ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)

def app (o : Op F κ) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ := Sum.elim (fun v => dD F v f) (fun l => mM F l f) o

def size (o : Op F κ) : ℝ := Sum.elim (fun v => ‖v‖) (fun l => ‖l‖) o

def word (w : List (Op F κ)) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ := w.foldr (fun o g => app F o g) f

def wordD (w : List (κ → mixedEmbedding.mixedSpace F)) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  word F (w.map Sum.inl) f

def Per (m : ℕ) (f : (κ → AF F) → ℂ) : Prop :=
  ∀ x z : κ → AF F, (∀ i, ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧
    z i = (m : AF F) * a) → f (x + z) = f x

@[simp] theorem word_cons (o : Op F κ) (w : List (Op F κ)) (f : (κ → AF F) → ℂ) :
    word F (o :: w) f = app F o (word F w f) := rfl

theorem word_append (w w' : List (Op F κ)) (f : (κ → AF F) → ℂ) : word F (w ++ w') f = word F w (word F w' f) := by
  simp [word, List.foldr_append]

end GlobalTheory.ArchDecay
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBound =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBound", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\nimport Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepresentationPointwiseArchimedeanDecayBound\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend\n\n"}
section -- clump:auto
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
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBound =====
