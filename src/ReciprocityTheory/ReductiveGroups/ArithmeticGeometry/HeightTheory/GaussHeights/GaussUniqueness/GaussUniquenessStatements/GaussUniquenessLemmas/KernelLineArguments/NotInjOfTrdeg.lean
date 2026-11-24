module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.ImgRSuccAbove
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

theorem not_inj_of_trdeg {F E : Type} [Field F] [Field E] [Algebra F E] {D N : ℕ} (S : Set E)
    (j0 : Fin (N + 1)) (ρ : Fin N → IntermediateField.adjoin F S) (hD : 1 ≤ D)
    (htr : Algebra.trdeg F (IntermediateField.adjoin F S) = ((D - 1 : ℕ) : Cardinal)) :
    ¬ Function.Injective (MvPolynomial.aeval (R := F) (imgR (D := D) j0 ρ)) := by
  intro hinj
  have hai : AlgebraicIndependent F (imgR (D := D) j0 ρ) := hinj
  have h1 := hai.cardinalMk_le_trdeg
  first
  | rw [← trdeg_add_eq F (IntermediateField.adjoin F S)] at h1
  rw [htr, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] at h1
  have hT : Fintype.card (TVar D N) = (D + 1) * (N + 1) := by simp [TVar]
  have hS : Fintype.card (SVar D N) = 1 + (D + 1) * N := by simp [SVar]
  rw [Cardinal.mk_fintype, Cardinal.mk_fintype, hT, hS] at h1
  norm_cast at h1
  rw [show (D + 1) * (N + 1) = (D + 1) * N + (D + 1) by ring] at h1
  generalize (D + 1) * N = P at h1
  omega

section Tr

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

noncomputable def gK (hv : IsTrivOn K v) :
    K →+* IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)) :=
  (IsLocalRing.residue _).comp ((RingHom.id K).codRestrict ((vRing v).comap (algebraMap K Ω))
    (fun x => by rw [ValuationSubring.mem_comap]; exact alg_mem v hv x))

theorem gK_surj (hv : IsTrivOn K v) : Function.Surjective (gK v hv) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨x.1, rfl⟩

end Tr

end GaussValuationUniqueness
