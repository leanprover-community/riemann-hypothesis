module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG

namespace PositivityTheory.SphericalProduct

def IsLowUniM {L : Type} [Field L] {n : ℕ} (g : GL (Fin n) L) : Prop :=
  (∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) L) i j = 0) ∧ ∀ i : Fin n, (g : Matrix (Fin n) (Fin n) L) i i = 1

theorem twKer_eq_jacSub {G : Type} [Group G] [TopologicalSpace G] (D : CassData G) (P : G → Prop)
    (hP : ∀ g, g ∈ D.N ↔ P g) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    twKer ρ D.N 1 = jacSub ρ P := by
  unfold twKer jacSub
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · rintro ⟨n, v, rfl⟩
    exact ⟨n, (hP _).1 n.2, v, rfl⟩
  · rintro ⟨u, hu, v, rfl⟩
    exact ⟨⟨u, (hP _).2 hu⟩, v, rfl⟩

def IwahoriU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ n : ℕ, ∃ D : CassData (GU σ n), D.J = IwU σ n ∧
      (∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L)) ∧ (∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L)) ∧
      ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)

def DomU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (D : CassData (GU σ n)), D.J = IwU σ n →
      (∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L)) → (∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L)) →
      (∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)) → ∀ t : D.T,
      ((∀ i j : Fin n, i ≤ j → ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) ≤
          ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)) → D.IsDom t) ∧
      (IsStrictDom ((t : GU σ n) : GL (Fin n) L) → D.IsStrDom t)

end PositivityTheory.SphericalProduct

end
