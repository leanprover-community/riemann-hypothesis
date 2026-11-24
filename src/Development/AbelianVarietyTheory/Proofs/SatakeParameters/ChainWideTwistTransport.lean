module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmulMemOfOne
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ColumnAvoidanceConditions
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace GlobalTheory.ColPeriodCompare

open NumberField IsDedekindDomain

section Lattices

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_proj (L : Submodule (𝓞 K) V) (hfg : L.FG) (hsp : Submodule.span K (L : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ v, P v ∈ W) ∧ (∀ w ∈ W, P w = w) ∧ ∀ v ∈ L, P v ∈ L := by
  apply GlobalTheory.DegAsm.FrameMove.exists_proj <;> assumption

end Lattices


open Classical in
theorem deg_eq {ι : Type} {a b : ℕ} (e : ι × Fin b × Fin a →₀ ℕ) (τ : ι) :
    ((∑ k ∈ e.support.filter (fun k => k.1 = τ), e k : ℕ) : ℤ) = ∑ β, ∑ α, (e (τ, β, α) : ℤ) := by
  rw [← Finset.sum_product', Finset.univ_product_univ, Nat.cast_sum]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun y : Fin b × Fin a => (τ, y) ∈ e.support))]
  · refine Finset.sum_bij (fun k _ => k.2) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨h1, rfl⟩ := Finset.mem_filter.1 hk
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩
    · intro k hk k' hk' h
      exact Prod.ext ((Finset.mem_filter.1 hk).2.trans (Finset.mem_filter.1 hk').2.symm) h
    · intro y hy
      exact ⟨(τ, y), Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).2, rfl⟩, rfl⟩
    · intro k hk
      obtain ⟨-, rfl⟩ := Finset.mem_filter.1 hk
      rfl
  · intro y _ hy
    have : (τ, y) ∉ e.support := fun h => hy (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [show (τ, y.1, y.2) = (τ, y) from rfl, Finsupp.notMem_support_iff.1 this, Nat.cast_zero]

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Ties

variable {D : D7} {EX : ErrX D} (Ch : Chars (BadPrimesPeriodBound.recFields D) (BadPrimesPeriodBound.recPrimes EX) D.R.m)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

variable (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)

end Ties

section Statements

variable (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D) (Ch : Chars (BadPrimesPeriodBound.recFields D) (BadPrimesPeriodBound.recPrimes EX) D.R.m)
  (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) {δ : ℂ}

end Statements

end GlobalTheory.ColPeriodCompare
