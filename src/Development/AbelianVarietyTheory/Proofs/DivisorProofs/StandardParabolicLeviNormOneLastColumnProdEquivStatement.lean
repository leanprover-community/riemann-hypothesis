module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicLeviNormOneLastColumnProdEquiv
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

theorem _root_.GlobalTheory.T.standardParabolicLeviNormOne_lastColumn_prodEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∃ φ : (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) × ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ≃ₜ* GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∀ p, ((φ p : GAd σ J) ∈ ratPts σ J ↔ (p.1 : GAd σ J) ∈ ratPts σ J ∧ (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range) := by
  first | exact @GlobalTheory.SphEis.LeviLast.leviOne_last_prod | exact GlobalTheory.SphEis.LeviLast.leviOne_last_prod | (intros; apply GlobalTheory.SphEis.LeviLast.leviOne_last_prod <;> assumption)
