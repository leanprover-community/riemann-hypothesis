module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian
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

@[expose] public section

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation.EtNbhd

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem algebraMap_comp_eq_of_pt {i j : EtNbhd R} (φ₁ φ₂ : i.A →ₐ[R] j.A)
    (h₁ : j.pt.comp φ₁ = i.pt) (h₂ : j.pt.comp φ₂ = i.pt) (a : i.A) :
    algebraMap j.A j.B (φ₁ a) = algebraMap j.A j.B (φ₂ a) := by
  let ψ₁ : i.A →ₐ[R] j.B := (IsScalarTower.toAlgHom R j.A j.B).comp φ₁
  let ψ₂ : i.A →ₐ[R] j.B := (IsScalarTower.toAlgHom R j.A j.B).comp φ₂
  have : ψ₁ = ψ₂ := by
    refine GlobalTheory.EtaleHensel.algHom_eq_of_residue_eq fun b => ?_
    rw [← sub_eq_zero, ← (residue j.B).map_sub (ψ₁ b) (ψ₂ b), residue_eq_zero_iff]
    show algebraMap j.A j.B (φ₁ b) - algebraMap j.A j.B (φ₂ b) ∈ maximalIdeal j.B
    rw [← (algebraMap j.A j.B).map_sub (φ₁ b) (φ₂ b), IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show φ₁ b - φ₂ b ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (congr($h₁ b)).trans (congr($h₂ b)).symm
  exact congr($this a)

theorem trans_algebraMap_eq_of_pt {i j : EtNbhd R} (h : i ≤ j) (φ : i.A →ₐ[R] j.A)
    (hφ : j.pt.comp φ = i.pt) (a : i.A) :
    trans h (algebraMap i.A i.B a) = algebraMap j.A j.B (φ a) := by
  unfold trans
  rw [Localization.localRingHom_to_map]
  exact algebraMap_comp_eq_of_pt _ _ h.choose_spec hφ a

end GlobalTheory.Henselisation.EtNbhd

namespace GlobalTheory.Henselisation

theorem trans_system : ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ (i : EtNbhd R) (x : i.B), EtNbhd.trans (le_refl i) x = x) ∧ ∀ (i j k : EtNbhd R) (hij : i ≤ j) (hjk : j ≤ k) (x : i.B), EtNbhd.trans hjk (EtNbhd.trans hij x) = EtNbhd.trans (hij.trans hjk) x := by
  intro R _ _
  refine ⟨fun i x => ?_, fun i j k hij hjk x => ?_⟩
  · have : EtNbhd.trans (le_refl i) = RingHom.id i.B :=
      IsLocalization.ringHom_ext i.q.primeCompl (RingHom.ext fun a => by
        simp only [RingHom.comp_apply, RingHom.id_apply]
        exact EtNbhd.trans_algebraMap_eq_of_pt _ (AlgHom.id R i.A) (AlgHom.comp_id _) a)
    exact congr($this x)
  · have : (EtNbhd.trans hjk).comp (EtNbhd.trans hij) = EtNbhd.trans (hij.trans hjk) :=
      IsLocalization.ringHom_ext i.q.primeCompl (RingHom.ext fun a => by
        simp only [RingHom.comp_apply]
        rw [EtNbhd.trans_algebraMap_eq_of_pt hij hij.choose hij.choose_spec,
          EtNbhd.trans_algebraMap_eq_of_pt hjk hjk.choose hjk.choose_spec,
          EtNbhd.trans_algebraMap_eq_of_pt (hij.trans hjk) (hjk.choose.comp hij.choose)
            (by rw [← AlgHom.comp_assoc, hjk.choose_spec, hij.choose_spec])]
        rfl)
    exact congr($this x)

end GlobalTheory.Henselisation
