module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory

theorem absFin_mul_mul_transpose_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (g : GL (Fin n) (AF F ⊗[F] E)) (X : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) (j : Fin d), absFin F v (compFin F E v (((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * X * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) i j)) ≤ htFin F v (bc (compFin F E v) g) * (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) * htFin F v (bc (compFin F E v) h) := by
  intro F E _ _ _ _ _ n d g X h v i j
  have hg : ∀ a b, ((bc (compFin F E v) g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a b = compFin F E v ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b) := by
    intro a b; rfl
  have hh : ∀ a b, ((bc (compFin F E v) h : GL (Fin d) (Fv F v ⊗[F] E)) : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E)) a b = compFin F E v ((h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) a b) := by
    intro a b; rfl
  have hG : ∀ a b, absFin F v (compFin F E v ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b)) ≤ htFin F v (bc (compFin F E v) g) := by
    intro a b
    have h1 := absFin_le_normFin F v ((bc (compFin F E v) g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a b
    rw [hg] at h1
    exact h1.trans (le_htOf (normFin F v) _)
  have hH : ∀ a b, absFin F v (compFin F E v ((h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) a b)) ≤ htFin F v (bc (compFin F E v) h) := by
    intro a b
    have h1 := absFin_le_normFin F v ((bc (compFin F E v) h : GL (Fin d) (Fv F v ⊗[F] E)) : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E)) a b
    rw [hh] at h1
    exact h1.trans (le_htOf (normFin F v) _)
  have hX : ∀ a b, absFin F v (compFin F E v (X a b)) ≤ Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2)) := by
    intro a b
    exact Finset.le_sup (f := fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) (b := (a, b)) (Finset.mem_univ _)

  rw [Matrix.mul_apply, map_sum]
  refine absFin_sum_le F v _ _ fun l _ => ?_

  rw [Matrix.transpose_apply, Matrix.mul_apply, map_mul, map_sum]
  refine (absFin_mul_le F v _ _).trans (mul_le_mul' (absFin_sum_le F v _ _ fun k _ => ?_) (hH _ _))
  rw [map_mul]
  exact (absFin_mul_le F v _ _).trans (mul_le_mul' (hG _ _) (hX _ _))

end GlobalTheory
