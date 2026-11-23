module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlace
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
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.SupportedAtSplit
import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cmp.SeriesRay

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke

variable {D : D7}

section Forms

variable {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)

theorem sum_mem_intForms (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) {m : ℕ} (x : Fin m → C.d.c₂.F)
    (hx : ∀ k, ∀ la ∈ S, la.valuation C.d.c₂.F (x k) ≤ 1) (φ : Fin m → GA D (T.V j σ) → ℂ) (hφ : ∀ k, φ k ∈ C.intForms a n S) :
    (∑ k, C.σ₂ (x k) • φ k) ∈ C.intForms a n S := by
  choose f hf e using hφ
  refine ⟨∑ k, x k • f k, ⟨⟨sum_mem fun k _ => Submodule.smul_mem _ _ (hf k).1.1, ?_⟩, fun la hla v hv => ?_⟩, ?_⟩

  · rw [map_sum]
    exact sum_mem fun k _ => by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (hf k).1.2
  · have hV := isVal_valSet la v hv
    exact GlobalTheory.IdemInt.nonneg_sum hV _ _ fun k _ => GlobalTheory.IdemInt.nonneg_smul hV (hx k la hla) ((hf k).2 la hla v hv)

  · simp only [← e, Cover.rd, map_sum, map_smulₛₗ, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

end Forms

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))



section Data

variable {T}

variable {R i}

end Data

section First

variable {T R i κ}

variable {hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i} {v₀ : (R.MW i (sg0 D A)).Vec} {u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ}
  {c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W} {ka : ℂ} {J : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}


end First

end GlobalTheory.Cmp.SeriesRay
