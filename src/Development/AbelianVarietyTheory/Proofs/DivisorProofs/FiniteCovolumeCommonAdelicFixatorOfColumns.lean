module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomeomorphColumnFixatorCoreUnitaryGroupStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotientStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem isClosed_fixG {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {k : ℕ} (C : Matrix (Fin n) (Fin k) E) :
    IsClosed ((fixG σ J C : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  exact isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const

theorem finCovol_fixG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) DM π → π DM ≠ ⊤ := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF π DM hπ hDM
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_homeomorph_columnFixator_coreUnitaryGroup F E σ n J j m C D Z J₀ hF
  have hcl : IsClosed ((fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) : Set (GAd σ J)) :=
    (isClosed_fixG σ J C).inter (isClosed_fixG σ J D)
  haveI : LocallyCompactSpace (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) := hcl.locallyCompactSpace
  haveI : Countable (ratPts σ J₀) := inferInstance
  exact GlobalTheory.T.covolume_ne_top_of_continuousMulEquiv_subgroup (GAd σ J₀) _ e (ratPts σ J₀) _ (fun g => by rw [he g]; rfl)
    (fun μ hμ 𝓕 h𝓕 => GlobalTheory.T.finiteVolume_adelicUnitaryQuotient F E σ hF.cm m J₀ hF.herm₀ μ hμ 𝓕 h𝓕) π DM hπ hDM

end GlobalTheory.SphEis
