module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictPlan
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

open NumberField Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.LatDictZ

open Formalism.MainNotions.S PIW.AdelClassFin

abbrev locE (I : AutInst) (p : Ideal (𝓞 I.E)) (L : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Formalism.HermitianLatticesTheory.loc (K := I.E) p L

abbrev hE (I : AutInst) (x y : Fin I.n → I.E) : I.E := Formalism.UG.hform (starRingEnd I.E) I.J x y

def Prim (I : AutInst) (M : Submodule (𝓞 I.E) (Fin I.n → I.E)) (z : Fin I.n → I.E) : Prop :=
  ∀ c : I.E, c • z ∈ M → c ∈ (algebraMap (𝓞 I.E) I.E).range

def SplitU (I : AutInst) {r : ℕ} (s : Fin r → Fin I.n → I.E) (M : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  ∀ w ∈ M, ∃ w₁ ∈ M, w₁ ∈ Submodule.span I.E (Set.range s) ∧ ∀ a, hE I (s a) (w - w₁) = 0

def LamGenus : Prop :=
  ∀ (I : AutInst) (x : I.Gf) (p : Ideal (𝓞 I.E)), p.IsMaximal →
    ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      ∀ v, v ∈ locE I p (abelian₂ I x) ↔ ∃ w ∈ locE I p I.L, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w = v

def ZOrbit : Prop :=
  ∀ (I : AutInst) {r : ℕ} (s : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) (M : Submodule (𝓞 I.E) (Fin I.n → I.E)),
    M.FG → Submodule.span I.E (M : Set (Fin I.n → I.E)) = ⊤ → SelfDual I.J M →
    (∀ a, hE I (s a) z = 0) →
    (∀ w ∈ Submodule.span I.E (Set.range s), w ∈ I.L ↔ w ∈ M) →
    SplitU I s I.L → SplitU I s M →
    z ∈ I.L → z ∈ M → Prim I I.L z → Prim I M z →
    ∃ x : I.Gf, (∀ a, I.fmat x *ᵥ iv I (s a) = iv I (s a)) ∧ I.fmat x *ᵥ iv I z = iv I z ∧ abelian₂ I x = M

end Formalism.L2.SG.Pf.LatDictZ
