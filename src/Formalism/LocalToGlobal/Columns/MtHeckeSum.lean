module

public import Formalism.LocalToGlobal.Columns.MtHeckeLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt)

section Sum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Pl E} (U : MhlUnif Pb) (k : ℕ)

theorem mhs_cosets_finite (ST SG : Finset (Pl E)) (hov : IsOver v Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q)
    (hSG : ∀ Q ∈ SG, ¬ IsOver v Q) (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) : (mhlCosets hc (n := n) v U k).Finite := by
  have hB := mhl_split_bij' hc U k ST SG hov hST hSG hsp hk 1
  refine Set.Finite.of_finite_image ?_ hB.injOn
  rw [hB.image_eq]
  exact DecoSet.heckeSet_finite (conjPrime₂ Pb).ne_bot (conjIdeal_ne_bot (conjPrime₂ Pb).ne_bot) k _

theorem mhs_exists_reps (ST SG : Finset (Pl E)) (hov : IsOver v Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q)
    (hSG : ∀ Q ∈ SG, ¬ IsOver v Q) (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) :
    ∃ R : Finset (UAd hc n), Set.BijOn (fun η : UAd hc n => (QuotientGroup.mk η : UAd hc n ⧸ mhlKv hc n v)) R
      (mhlCosets hc v U k) := by
  classical
  have hfin := mhs_cosets_finite hc U k ST SG hov hST hSG hsp hk
  refine ⟨hfin.toFinset.image Quotient.out, ?_, ?_, ?_⟩
  · intro η hη
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hη
    obtain ⟨c, hc', rfl⟩ := hη
    show (QuotientGroup.mk c.out : UAd hc n ⧸ mhlKv hc n v) ∈ mhlCosets hc v U k
    rw [QuotientGroup.out_eq']
    exact hc'
  · intro η hη η' hη' h
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hη hη'
    obtain ⟨c, -, rfl⟩ := hη
    obtain ⟨c', -, rfl⟩ := hη'
    have h' : c = c' := (QuotientGroup.out_eq' c).symm.trans (h.trans (QuotientGroup.out_eq' c'))
    rw [h']
  · intro c hc'
    refine ⟨c.out, ?_, QuotientGroup.out_eq' c⟩
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset]
    exact ⟨c, hc', rfl⟩

theorem mhs_decoOf_out (ST SG : Finset (Pl E)) (hST : ∀ Q ∈ ST, ¬ IsOver v Q) (hSG : ∀ Q ∈ SG, ¬ IsOver v Q)
    (x η : UAd hc n) :
    decoOf ST SG ((x * (QuotientGroup.mk η : UAd hc n ⧸ mhlKv hc n v).out : UAd hc n) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = decoOf ST SG ((x * η : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul (mhlKv hc n v) η
  rw [e, ← mul_assoc, Subgroup.coe_mul]
  exact decoOf_mul_mhlKv ST SG hST hSG _ h.2

end Sum

end Formalism.L2.Col
