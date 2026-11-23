module

public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactIwasawa
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaCompactStatement
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ ∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW
  obtain ⟨K₁, h₁, c₁, iw₁, lev⟩ := GlobalTheory.CompanionTheory.SiegelArch.exists_kInf F E σ hcm n J hJ r X Y hW
  obtain ⟨K₂, h₂, c₂, iw₂, good⟩ := GlobalTheory.T.unitary_adelic_iwasawa_compact F E σ hcm n J hJ r X Y hW
  obtain ⟨K, hK, iw, -⟩ := GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa F E σ hcm n J hJ r X Y hW
    K₁ K₂ h₁ h₂ c₁ c₂ iw₁ iw₂ lev good
  exact ⟨K, hK, iw⟩
