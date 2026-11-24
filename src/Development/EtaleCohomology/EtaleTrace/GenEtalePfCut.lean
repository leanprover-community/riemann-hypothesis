module

public import Development.EtaleCohomology.EtaleTrace.GenEtalePf
public import Development.EtaleCohomology.EtaleTrace.GenEtalePfBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenAffineData : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P]
  (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  ∃ U : P.Opens, IsAffineOpen U ∧ (U : Set P).Nonempty ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ IsNoetherianRing Γ(P, U) ∧
    (π.app U).hom.Finite ∧ Function.Injective (π.app U).hom

def GenEtaleAtBot : Prop := ∀ {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P] (π : X ⟶ P) (U : P.Opens), IsAffineOpen U →
  (U : Set P).Nonempty → IsAffineOpen (π ⁻¹ᵁ U) → (π.app U).hom.Finite → Function.Injective (π.app U).hom →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified →
  ∃ _ : (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)).IsPrime,
    (letI := (π.app U).hom.toAlgebra; Algebra.IsEtaleAt Γ(P, U) (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)))

theorem GenAffineSetup_of (h1 : GenAffineData) (h2 : GenEtaleAtBot) : GenAffineSetup := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨U, hU, hne, hU', hN, hf, hi⟩ := h1 k p r π hπ hr hfin hsurj
  exact ⟨U, hU, hne, hU', hN, hf, hi, h2 π U hU hne hU' hf hi hun⟩

theorem GenEtale_of' (h1 : GenAffineData) (h2 : GenEtaleAtBot) : GenEtale :=
  GenEtale_of (GenAffineSetup_of h1 h2) etaleOverBasic

end LateralTheory.EtaleTrace.Cov
