module

public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.RingObjectsOfMatrixData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.ringDataObjects

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
  [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)} {T : Subalgebra O (X → O)}
  {r₀ : G →* (X → Matrix d d O)} {π : X} {χ₁ ε : G →* Oˣ} {g₀ : G} {eB e₁ s : X → Matrix d d O}
  {D : RingData O X d G t bl}

theorem deltaO_eq (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D) :
    D.δO = ∏ i ∈ Finset.Ioo 0 t, ((χ₁ g₀ : O) - (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O)) := by
  obtain ⟨-, -, -, -, -, hrr, -⟩ := hD
  have h2 : D.δO = ∏ i ∈ Finset.Ioo 0 t,
      ((D.rr 0 : D.X' → O) D.π' - (D.rr i : D.X' → O) D.π') := by
    show ((Pi.evalRingHom (fun _ : D.X' => O) D.π').comp D.T'.val.toRingHom) D.δ = _
    unfold RingData.δ
    rw [map_prod]; rfl
  rw [h2]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_Ioo] at hi
  rw [hrr 0 (by omega), hrr i hi.2]
  simp

theorem idempotent_rank_one_at_point (hI : IdemHyp O T r₀ π bl eB e₁) (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D) :
    ((D.ρk 0 D.e₁).map (algebraMap O (FractionRing O))).rank = 1 := by
  obtain ⟨-, -, -, -, hpπ, -, -, -, -, -, -, -, -, he1, -, -, hρπ, hρk, -⟩ := hD
  obtain ⟨-, -, -, -, -, -, -, hrk1, -, he1π⟩ := hI
  have h2 : (D.ρk 0 D.e₁).map (algebraMap O (FractionRing O)) =
      ((e₁ π).map (algebraMap O (FractionRing O))).toSquareBlock bl 0 := by
    rw [← hρk]
    ext i j
    have h := congrFun (congrFun (hρπ D.e₁) i.1) j.1
    rw [he1, hpπ] at h
    exact h
  rw [h2, rank_block bl 0 _ (fun a b hab => by
    show algebraMap O (FractionRing O) (e₁ π a b) = 0
    rw [he1π a b hab, map_zero])]
  exact hrk1 π

end Formalism.RepresentationBoundsCohomology.SF
