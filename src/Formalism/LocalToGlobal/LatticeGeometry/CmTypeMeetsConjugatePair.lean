module

public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

open Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace Formalism.L2.Geo

theorem emb_mul_cc_comp {R : Ranks} (H : Host R) (g : R.GG) :
    H.emb (g * R.cc) = (H.emb g).comp (H.conj : H.E →+* H.E) := by
  refine RingHom.ext fun x => ?_
  show H.φ₀ (H.sigmaOf (g * R.cc) x) = H.φ₀ (H.sigmaOf g (H.conj x))
  have : H.sigmaOf (g * R.cc) = H.sigmaOf g * H.conj :=
    map_mul (H.gal).symm g (R.cc)
  rw [this]; rfl

theorem mem_Psi_iff_mul_cc_notMem {φ : Formalism.HC.Frame} (g : φ.GG) :
    g ∈ φ.Psi ↔ g * φ.cc ∉ φ.Psi := by
  rw [Formalism.HC.Frame.mem_Psi_iff, Formalism.HC.Frame.mem_Psi_iff]
  show g.1.2 = 1 ↔ ¬ g.1.2 * (-1) = 1
  rcases Int.units_eq_one_or g.1.2 with h | h <;> rw [h] <;> decide

theorem exists_tauEmb_iff (D : D7) (g : D.R.GG) :
    (∃ τ0 : D.what₂.Tau, D.host.emb g = DV.tauEmb D τ0) ↔ g ∈ D.R.Psi := by
  constructor
  · rintro ⟨τ0, h⟩
    have := (factEmb D.R D.host).1.1 h
    rw [this]; exact (D.eTau τ0).2
  · intro hg
    refine ⟨D.eTau.symm ⟨g, hg⟩, ?_⟩
    unfold DV.tauEmb
    rw [Equiv.apply_symm_apply]

theorem cm_type_meets_conjugate_pair {D : D7} (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ) (τ : DV.Emb D p) :
    τ ∈ DV.PsiOf D jc ↔ DV.cEmb D τ ∉ DV.PsiOf D jc := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 (jc.comp τ)
  have h1 : τ ∈ DV.PsiOf D jc ↔ g ∈ D.R.Psi := by
    rw [← exists_tauEmb_iff D g, hg]; rfl
  have hc : jc.comp (DV.cEmb D τ) = D.host.emb (g * D.R.cc) := by
    rw [emb_mul_cc_comp, hg]; rfl
  have h2 : DV.cEmb D τ ∈ DV.PsiOf D jc ↔ g * D.R.cc ∈ D.R.Psi := by
    rw [← exists_tauEmb_iff D (g * D.R.cc), ← hc]; rfl
  rw [h1, h2]
  exact mem_Psi_iff_mul_cc_notMem g

end Formalism.L2.Geo
