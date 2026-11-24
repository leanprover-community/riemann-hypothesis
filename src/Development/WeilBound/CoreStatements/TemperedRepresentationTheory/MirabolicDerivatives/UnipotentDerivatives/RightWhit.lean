module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.BZMir

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def rightUnip (n t : ℕ) : Subgroup (GL (Fin n) k × GL (Fin t) k) := Subgroup.prod ⊥ (unipB k (Fin t))


variable (k) in
def rightWhit (ψ : AddChar k Circle) (n t : ℕ) : rightUnip k n t →* ℂˣ :=
  (whitChar ψ t).comp
    { toFun := fun x => ⟨(x : GL (Fin n) k × GL (Fin t) k).2, (Subgroup.mem_prod.1 x.2).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem inl_stab (ψ : AddChar k Circle) (n t : ℕ) (m : GL (Fin n) k) (u : rightUnip k n t) :
    ∃ h : MonoidHom.inl (GL (Fin n) k) (GL (Fin t) k) m * (u : GL (Fin n) k × GL (Fin t) k) *
        (MonoidHom.inl (GL (Fin n) k) (GL (Fin t) k) m)⁻¹ ∈ rightUnip k n t,
      rightWhit k ψ n t ⟨_, h⟩ = rightWhit k ψ n t u := by
  have h1 : (u : GL (Fin n) k × GL (Fin t) k).1 = 1 := Subgroup.mem_bot.1 (Subgroup.mem_prod.1 u.2).1
  have hconj : MonoidHom.inl (GL (Fin n) k) (GL (Fin t) k) m * (u : GL (Fin n) k × GL (Fin t) k) *
      (MonoidHom.inl (GL (Fin n) k) (GL (Fin t) k) m)⁻¹ = (u : GL (Fin n) k × GL (Fin t) k) := by
    refine Prod.ext ?_ ?_ <;> simp [h1]
  refine ⟨by rw [hconj]; exact u.2, ?_⟩
  congr 1
  exact Subtype.ext hconj


variable (k) in
def derRep (ψ : AddChar k Circle) {n t N : ℕ} (h : n + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    Representation ℂ (GL (Fin n) k) (TwJacquet (jacU₂ (stdSum h) π) (rightUnip k n t) (rightWhit k ψ n t)) :=
  twAct (jacU₂ (stdSum h) π) (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _) (inl_stab ψ n t)

end GlobalTheory.BZMir

end
