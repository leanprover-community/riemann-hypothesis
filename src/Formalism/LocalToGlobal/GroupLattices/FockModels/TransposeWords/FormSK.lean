module

public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

def nabO (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (ν : Fin (m + 1) → ℕ) :
    Submodule O (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :=
  Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap (dualWeyl O (m + 1) (m + 1) ν)

def expN (p m : ℕ) (lam : Fin (m + 1) → ℤ) : ℕ :=
  if ellWt lam = 0 then 0 else N0 (m + 1) * deF p (m + 1) (ellWt lam)

def FormCoreSK : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
        B (rowAct Kf g P) Q = B P (rowAct Kf g.transpose Q)) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam), B P Q = 0) → Q = 0) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ nabO O Kf m (nuOf lam), B P Q ∈ Set.range (algebraMap O Kf)) → Q ∈ nabO O Kf m (nuOf lam)) ∧
      (∀ Q ∈ nabO O Kf m (nuOf lam), ∀ P ∈ nabO O Kf m (nuOf lam),
        B P (((p : Kf) ^ expN p m lam) • Q) ∈ Set.range (algebraMap O Kf))

end Formalism.L2.G.Model.TS
