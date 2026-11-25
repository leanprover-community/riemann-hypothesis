module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.RunFinOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.F.F5

def LevelFactor : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (c n : ℕ)
  (N : Fin c → ℕ) (h : ∑ i, N i = n) (K : Subgroup (GL (Fin n) (w.adicCompletion E))),
  IsOpen (K : Set (GL (Fin n) (w.adicCompletion E))) →
  ∃ Ki : ∀ i, Subgroup (GL (Fin (N i)) (w.adicCompletion E)),
    (∀ i, IsOpen (Ki i : Set (GL (Fin (N i)) (w.adicCompletion E)))) ∧
    (GlobalTheory.LFun.KGL w (n := n) ≤ K → ∀ i, GlobalTheory.LFun.KGL w (n := (N i)) ≤ Ki i) ∧
    ∀ σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E)), GlobalTheory.LGrp.IsSpherical (locProd h w σ) K →
      ∀ i, GlobalTheory.LGrp.IsSpherical (σ i).ρ (Ki i)

def FinDiscN : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (m : (E →+* ℂ) → Multiset ℂ), IsLevel Kf → FiniteDimensional ℂ W →
  ∃ (k : ℕ) (σ : Fin k → ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin N) (w.adicCompletion E))),
    ∀ (V : Submodule ℂ (Sm E N)) (σ' : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin N) (w.adicCompletion E))),
      IsDiscrete V → (∀ w, IsLocCompGL V w (σ' w)) → (∀ τ, HasInfCharGL V τ (m τ)) →
      (∀ w, GlobalTheory.LGrp.IsSpherical (σ' w).ρ (Kf w)) → HasKType W V →
      ∃ j, ∀ w, GlobalTheory.LocGL.IrrGL.of (σ j w).ρ (σ j w).smooth (σ j w).irred =
        GlobalTheory.LocGL.IrrGL.of (σ' w).ρ (σ' w).smooth (σ' w).irred

def FinFamOf : Prop := LevelFactor → FinDiscN → FinFam

end PositivityTheory.Rg.BcB.F.F5

end
