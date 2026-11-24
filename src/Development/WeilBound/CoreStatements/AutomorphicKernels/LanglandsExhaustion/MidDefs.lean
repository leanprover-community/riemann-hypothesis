module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace PositivityTheory.Exh

section Tensor

variable {G H V V' W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W]

def extL {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (f : ρ.IntertwiningMap ρ')
    (σ : Representation ℂ H W) : (extTensor ρ σ).IntertwiningMap (extTensor ρ' σ) where
  toLinearMap := f.toLinearMap.rTensor W
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v w
    simp [f.isIntertwining]

def extR (σ : Representation ℂ H W) {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') : (extTensor σ ρ).IntertwiningMap (extTensor σ ρ') where
  toLinearMap := f.toLinearMap.lTensor W
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v w
    simp [f.isIntertwining]

end Tensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Ind

variable {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def ind₂Map (e : a ⊕ b ≃ n) {ρ : Representation ℂ (GL a k × GL b k) V}
    {ρ' : Representation ℂ (GL a k × GL b k) V'} (f : ρ.IntertwiningMap ρ') :
    (ind₂ e ρ).IntertwiningMap (ind₂ e ρ') :=
  parIndMap (two e) (compMap f _)

end Ind

variable {nA nB m m' N : ℕ} {VA VB V V' : Type} [AddCommGroup VA] [Module ℂ VA] [AddCommGroup VB] [Module ℂ VB]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def T3 (h2 : m + nB = m') (h1 : nA + m' = N) (PA : Representation ℂ (GL (Fin nA) k) VA)
    (PB : Representation ℂ (GL (Fin nB) k) VB) (τ : Representation ℂ (GL (Fin m) k) V) :=
  ind₂ (stdSum h1) (extTensor PA (ind₂ (stdSum h2) (extTensor τ PB)))

def tripleProductMap (h2 : m + nB = m') (h1 : nA + m' = N) (PA : Representation ℂ (GL (Fin nA) k) VA)
    (PB : Representation ℂ (GL (Fin nB) k) VB) {τ : Representation ℂ (GL (Fin m) k) V}
    {τ' : Representation ℂ (GL (Fin m) k) V'} (f : τ.IntertwiningMap τ') :
    (T3 h2 h1 PA PB τ).IntertwiningMap (T3 h2 h1 PA PB τ') :=
  ind₂Map _ (extR PA (ind₂Map _ (extL f PB)))

end PositivityTheory.Exh

end
