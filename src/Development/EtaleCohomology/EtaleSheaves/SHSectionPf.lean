module

public import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHSectionPf

def SHAlgSec : Prop := ∀ (A R : CommRingCat.{0}) (f : A ⟶ R), SH A → f.hom.Etale →
  (∃ Q : Ideal R, Q.IsPrime ∧ (Q.comap f.hom).IsMaximal) → ∃ σ : R ⟶ A, f ≫ σ = 𝟙 A

def EtAffNbhd : Prop := ∀ (A : CommRingCat.{0}) [Nontrivial A] {V : Scheme.{0}} (g : V ⟶ Spec A) [Etale g] [Surjective g],
  ∃ (R : CommRingCat.{0}) (f : A ⟶ R) (ι : Spec R ⟶ V), f.hom.Etale ∧ ι ≫ g = Spec.map f ∧
    ∃ Q : Ideal R, Q.IsPrime ∧ (Q.comap f.hom).IsMaximal

theorem SHSection_of (h1 : SHAlgSec) (h2 : EtAffNbhd) : LateralTheory.E.t_E3Cut.SHSection := by
  intro A hA V g _ _
  have : Nontrivial A := by obtain ⟨hH, -⟩ := hA; infer_instance
  obtain ⟨R, f, ι, hf, hι, hQ⟩ := h2 A g
  obtain ⟨σ, hσ⟩ := h1 A R f hA hf hQ
  refine ⟨Spec.map σ ≫ ι, ?_⟩
  rw [Category.assoc, hι, ← Spec.map_comp, hσ, Spec.map_id]

end LateralTheory.E.SHSectionPf
