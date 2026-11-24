module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeAnnihilatorLatticeHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeDivisorIdealLatticeStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeImageLatticeStatement
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

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem lattice_facts_of_normal : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → D.Facts R p w χ φ := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hn hf hi φ ht h1 h2
  have hleaf := GlobalTheory.T.hodge_annihilator_lattice_holds D R p w χ hc hb hp hn hf hi φ ht h1
  have hseq := GlobalTheory.T.hodge_image_lattice D R p w χ hc hb hp hn hf hi φ ht h1 h2
  obtain ⟨hdx, honto, hinj⟩ := GlobalTheory.T.hodge_divisor_ideal_lattice D R p w χ hc hb hp hn hf hi φ ht h1 h2
  exact
    { le_af := hleaf
      im := fun τ => (hseq τ).1
      ker := fun τ => (hseq τ).2
      dx := hdx
      onto := honto
      inj := hinj }

end GlobalTheory.CompanionTheory.Ar.Num
