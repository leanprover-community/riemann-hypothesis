module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar

namespace GlobalTheory.Published

def LanglandsSquareIntegrable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
          ∀ (T : Finset (Fin r)) (φ : GAd σ J → ℂ), IsAutOn σ J X Y T K φ →
            (IsSqIntOn σ J X Y T φ ↔ ∀ S, T ⊆ S → ∀ s, IsCuspExp σ J X Y S K φ s → NegExp S T s)

def LanglandsLemmaUnitary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
          ∀ (T : Finset (Fin r)) (φ : GAd σ J → ℂ), IsAutOn σ J X Y T K φ →
            (∀ S, T ⊆ S → ∃! φc, IsCuspComp σ J X Y S K φ φc) ∧
            ((∀ S, T ⊆ S → IsCuspComp σ J X Y S K φ 0) → φ = 0) ∧
            (φ ≠ 0 → ∃ S, T ⊆ S ∧ ∃ s, IsCuspExp σ J X Y S K φ s)

def AutomorphicFormsUnitary : Prop := LanglandsSquareIntegrable ∧ LanglandsLemmaUnitary

end GlobalTheory.Published

namespace GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {K : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ}

theorem isSqInt_iff (H : GlobalTheory.Published.LanglandsSquareIntegrable) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (hK : IsMaxCpt σ J K) (hφ : IsAut σ J K φ) :
    IsSqInt σ J φ ↔ ∀ S s, IsCuspExp σ J X Y S K φ s → ∀ k ∈ S, ∑ i with i ≤ k, (s i).re < 0 := by
  simpa only [isSqIntOn_empty, negExp_empty, Finset.empty_subset, forall_const] using
    H F E σ h n J hJ r X Y hW K hK ∅ φ (isAutOn_empty.2 hφ)


end GlobalTheory.StdPar

end
