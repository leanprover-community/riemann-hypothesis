module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitImgMono
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSubquotientEquiv
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

theorem _root_.GlobalTheory.T.whittaker_subquotient_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    T' ≤ T → (subQuot T T').Equiv (piTensor ρ) →
    ⨆ f : (ρ 0).IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')), LinearMap.range f.toLinearMap = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main | exact GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main <;> assumption)
