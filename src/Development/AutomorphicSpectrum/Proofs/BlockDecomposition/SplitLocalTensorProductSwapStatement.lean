module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitLocalTensorProductSwap
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

theorem _root_.GlobalTheory.T.split_local_tensor_product_swap : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), ¬ IsField (Fv F v ⊗[F] E) → ∃ φ : (Fv F v ⊗[F] E) ≃+* Fv F v × Fv F v, (∀ r, φ (sigR (Fv F v) σ r) = (φ r).swap) ∧ ∀ r, r ∈ intLoc F E v ↔ (φ r).1 ∈ v.adicCompletionIntegers F ∧ (φ r).2 ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv | exact GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv <;> assumption)
