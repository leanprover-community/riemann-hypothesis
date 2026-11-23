module

public import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

@[expose] public section

noncomputable section

namespace GlobalTheory.CuspFormsCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma zero_mem_SS_unitary_existence {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    (0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) ∈ X.SS la :=
  ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_zero X la, fun ξ _ x _ => _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_zero X la ξ x 0⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma add_mem_SS {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) (hQ : Q ∈ X.SS la) : P + Q ∈ X.SS la := by
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_add X hP.1 hQ.1, fun ξ hξ x hx => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_add X hP.1 hQ.1 hξ hx 0, hP.2 ξ hξ x hx, hQ.2 ξ hξ x hx, add_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma smul_mem_SS {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (a : ℂ) {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : a • P ∈ X.SS la := by
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_smul X a hP.1, fun ξ hξ x hx => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_smul X la P ξ x 0 a, hP.2 ξ hξ x hx, mul_zero]


variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.CuspFormsCompare.mem_holSub_iff_forall_SS {r : ℕ} {Comp : Type}
    (X : Comp → _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : ∀ k, _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r)
    (P : _root_.Formalism.L2.PjFree.FDSec X) : P ∈ _root_.Formalism.L2.PjFree.holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  constructor
  · intro hP
    unfold _root_.Formalism.L2.PjFree.holSub at hP
    induction hP using Submodule.span_induction with
    | mem Q hQ => exact hQ
    | zero => exact fun k => zero_mem_SS_unitary_existence (X k) (la k)
    | add Q R _ _ hQ hR => exact fun k => add_mem_SS (X k) (la k) (hQ k) (hR k)
    | smul a Q _ hQ => exact fun k => smul_mem_SS (X k) (la k) a (hQ k)
  · intro hP
    exact _root_.Formalism.L2.PjFree.holCusp_mem_holSub X la hP

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end GlobalTheory.CuspFormsCompare
