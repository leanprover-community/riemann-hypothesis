module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial

namespace PositivityTheory.AutomorphicGaloisHodgeTate.Div

def IsSSMat {Γ K ι : Type} [Group Γ] [Field K] [Fintype ι] [DecidableEq ι]
    (ρ : Γ →* GL ι K) : Prop :=
  ∀ W : Submodule K (ι → K), (∀ g : Γ, ∀ v ∈ W, (ρ g : Matrix ι ι K).mulVec v ∈ W) →
    ∃ W' : Submodule K (ι → K), IsCompl W W' ∧
      ∀ g : Γ, ∀ v ∈ W', (ρ g : Matrix ι ι K).mulVec v ∈ W'

def InLieZar {Γ K K' ι : Type} [Group Γ] [Field K] [Field K'] [Algebra K K']
    [Fintype ι] [DecidableEq ι] (ρ : Γ →* GL ι K) (X : Matrix ι ι K') : Prop :=
  ∀ f : MvPolynomial (ι × ι) K,
    (∀ g : Γ, MvPolynomial.eval (fun p : ι × ι => (ρ g : Matrix ι ι K) p.1 p.2) f = 0) →
      ∑ p : ι × ι, algebraMap K K'
          (MvPolynomial.eval (fun q : ι × ι => (1 : Matrix ι ι K) q.1 q.2)
            (MvPolynomial.pderiv p f)) * X p.1 p.2 = 0

end PositivityTheory.AutomorphicGaloisHodgeTate.Div
