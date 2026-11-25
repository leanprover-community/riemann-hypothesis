module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
public import Formalism.LocalRingCardinality.DataKap
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ModelLamPDef

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.RowsRestModel

namespace GlobalTheory.Mem.Df.Model

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (H : HLat K) (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module ℂ M]
  (j : H.V →ₛₗ[σ] M) (c : Module.Basis H.ι ℂ M) (hc : ∀ i, c i = j (H.b i))




end Gen

section Pack

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (σ : X.K →+* ℂ)





end Pack

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : TC.Laws I) (hX : B.fields.Ok)



theorem exists_ka (B : Base) : ∃ (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ),
    ∀ (C : Cols B) (W : RowsRest B C), W.kaBig = kb → W.kaSmall = ks → ∀ V S N G, DV.KapDef (assemble B C W V S N G) := by
  by_cases h : ∃ (C : Cols B) (W : RowsRest B C) (_ : DivStage B C W) (_ : SStage B C W) (_ : NStage B C W), Nonempty (GJStage B C)
  · obtain ⟨C, W, V, S, N, ⟨G⟩⟩ := h
    obtain ⟨kb, ks, hk⟩ := DV.exists_blocks (assemble B C W V S N G)
    refine ⟨kb, ks, fun C' W' h1 h2 V' S' N' G' j _ _ τ => ⟨fun i => ?_, fun c => ?_⟩⟩
    · show ((W'.kaBig j τ i : ℤ) : ℚ) = _
      rw [h1]
      exact (hk j τ).1 i
    · show ((W'.kaSmall j τ c : ℤ) : ℚ) = _
      rw [h2]
      exact (hk j τ).2 c
  · exact ⟨0, 0, fun C W _ _ V S N G => absurd ⟨C, W, V, S, N, ⟨G⟩⟩ h⟩

section Build

variable {C : Cols B} {d₀ : C.Tup → ℕ} (hf : Fits C d₀) (d : C.Tup → ℕ)
  (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Eu (d a)))
  (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Eu (d C.mu0)) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] Eu (d a))
  (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ)

end Build





end GlobalTheory.Mem.Df.Model

end
